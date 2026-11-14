
// Browser-side glue only. Document edits and OT semantics remain in Lean.
interface EditorPosition { block: number; offset: number }
interface EditorBlock { kind: string; text: string }
interface EditorState {
  doc: EditorBlock[];
  rev: number;
  canUndo: boolean;
  canRedo: boolean;
  pendingOps: unknown[];
  pendingCount: number;
}
interface LeanSnapshot extends EditorState {
  ok?: boolean;
  error?: string;
}
interface LeanPort { send(payload: unknown): Promise<unknown> | unknown }
interface LeanBridge { ports: Record<string, LeanPort> }
interface BridgeWaiter {
  matches: (snapshot: LeanSnapshot) => boolean;
  resolve: (snapshot: LeanSnapshot) => void;
  reject: (error: Error) => void;
}
interface InputEvent {
  otFromBlock?: number;
  otFromOffset?: number;
  otToBlock?: number;
  otToOffset?: number;
  otData?: string;
  otCaretBlock?: number;
  otCaretOffset?: number;
}
interface Window {
  __leanBridgeReady?: Promise<LeanBridge>;
  __editorBridgeSnapshot?: (raw: LeanSnapshot) => void;
  __editorBridgeError?: (message: unknown) => void;
  __editorServerAction?: (action: unknown) => void;
}

(() => {

const editor = document.getElementById('editor')!;
let editorContent: HTMLElement = document.getElementById('editor-content')!;
const els = {
  undo: document.getElementById('undo') as HTMLButtonElement, redo: document.getElementById('redo') as HTMLButtonElement,
  kind: document.getElementById('kind') as HTMLSelectElement, rev: document.getElementById('rev')!,
  status: document.getElementById('status')!,
};
const roomName = new URLSearchParams(window.location.search).get('room') || 'demo';
const clientId = (window.crypto && crypto.randomUUID)
  ? crypto.randomUUID() : 'client-' + Math.random().toString(36).slice(2);
const collabStatus = document.getElementById('collab-status')!;
document.getElementById('room-name')!.textContent = roomName;

let state: EditorState = { doc: [], rev: 0, canUndo: false, canRedo: false, pendingOps: [], pendingCount: 0 };
let bridgePortQueue: Promise<unknown> = Promise.resolve();
let bridgeSnapshotWaiters: BridgeWaiter[] = [];

// A port send acknowledges delivery to Lean, not necessarily delivery of the
// resulting snapshot back to this JS transport. Serialize commands and wait
// for that snapshot before reading the mirrored revision or sending the next
// state-dependent command.
function sendLeanAndWait(bridge: LeanBridge, portName: string, payload: unknown, matches: (snapshot: LeanSnapshot) => boolean = () => true): Promise<LeanSnapshot> {
  const task = bridgePortQueue.then(() => new Promise<LeanSnapshot>((resolve, reject) => {
    const waiter: BridgeWaiter = {
      matches,
      resolve: value => { clearTimeout(timer); resolve(value); },
      reject: error => { clearTimeout(timer); reject(error); }
    };
    const timer = setTimeout(() => {
      bridgeSnapshotWaiters = bridgeSnapshotWaiters.filter(w => w !== waiter);
      reject(new Error('Timed out waiting for Lean snapshot after ' + portName));
    }, 10000);
    bridgeSnapshotWaiters.push(waiter);
    Promise.resolve(bridge.ports[portName].send(payload)).catch(error => {
      bridgeSnapshotWaiters = bridgeSnapshotWaiters.filter(w => w !== waiter);
      waiter.reject(error);
    });
  }));
  bridgePortQueue = task.catch(() => {});
  return task;
}

let lastPos: EditorPosition = { block: 0, offset: 0 };
let networkBusy = false;
let failedFlush = false;
let pendingRequest: { requestId: string; baseRevision: number; ops: unknown[] } | null = null;
let roomReady = false;   // initial server snapshot has been integrated
let statusTimer: ReturnType<typeof setTimeout> | undefined;

/* ---- code point helpers: Lean counts Unicode scalar values, JS strings count UTF-16 units ---- */
const cpLen = s => { let n = 0; for (const _ of s) n++; return n; };
const cpToIdx = (s, cp) => { let i = 0, n = 0; for (const ch of s) { if (n === cp) break; i += ch.length; n++; } return i; };
const idxToCp = (s, idx) => cpLen(s.slice(0, idx));
const blockLen = b => (state.doc[b] ? cpLen(state.doc[b].text) : 0);
const cmp = (a, b) => a.block - b.block || a.offset - b.offset;

/* ---- render toolbar state; Lasm owns the document DOM ---- */
function render() {
  els.undo.disabled = !state.canUndo || state.pendingCount > 0;
  els.redo.disabled = !state.canRedo || state.pendingCount > 0;
  els.rev.textContent = 'rev ' + state.rev;
  syncKind();
}

function syncKind() {
  const b = state.doc[lastPos.block];
  els.kind.value = b ? b.kind : 'para';
}

function showError(msg) {
  els.status.textContent = msg;
  els.status.style.display = 'inline-block';
  clearTimeout(statusTimer);
  statusTimer = setTimeout(() => { els.status.style.display = 'none'; }, 4000);
}

/* ---- selection <-> (block, code point offset) ---- */
function blockOf(node: Node | null): HTMLElement | null {
  while (node && node !== editor) {
    if (node.parentNode === editorContent) return node as HTMLElement;
    node = node.parentNode;
  }
  return null;
}

function domToPos(node: Node | null, off: number): EditorPosition | null {
  if (!node) return null;
  if (node === editor || node === editorContent) {
    const n = editorContent.children.length;
    if (n === 0) return { block: 0, offset: 0 };
    if (off >= n) return { block: n - 1, offset: blockLen(n - 1) };
    return { block: off, offset: 0 };
  }
  const b = blockOf(node);
  if (!b) return null;
  const i = Number(b.dataset.i);
  if (node === b) return { block: i, offset: off === 0 ? 0 : blockLen(i) };
  if (node.nodeType === 3) return { block: i, offset: idxToCp((node as Text).data, off) };
  return { block: i, offset: 0 };
}

function currentRange(): { from: EditorPosition; to: EditorPosition } {
  const sel = window.getSelection();
  if (sel && sel.rangeCount && editor.contains(sel.anchorNode)) {
    const a = domToPos(sel.anchorNode, sel.anchorOffset);
    const f = domToPos(sel.focusNode, sel.focusOffset);
    if (a && f) return cmp(a, f) <= 0 ? { from: a, to: f } : { from: f, to: a };
  }
  return { from: lastPos, to: lastPos };
}

function setCaret(pos: EditorPosition): void {
  const n = state.doc.length;
  if (n === 0) return;
  const b = Math.min(pos.block, n - 1);
  const el = editorContent.children[b];
  const t = el.firstChild;
  const domLength = t && t.nodeType === 3 ? cpLen((t as Text).data) : 0;
  const o = Math.min(pos.offset, domLength);
  const range = document.createRange();
  if (t && t.nodeType === 3) range.setStart(t, cpToIdx((t as Text).data, o));
  else range.setStart(el, 0);
  range.collapse(true);
  const sel = window.getSelection();
  sel.removeAllRanges();
  sel.addRange(range);
  lastPos = { block: b, offset: o };
  syncKind();
}

document.addEventListener('selectionchange', () => {
  const sel = window.getSelection();
  if (sel && sel.rangeCount && editor.contains(sel.focusNode)) {
    const p = domToPos(sel.focusNode, sel.focusOffset);
    if (p) { lastPos = p; syncKind(); }
  }
});

/* ---- talking to the backend ---- */
async function api(msg: Record<string, any>): Promise<any> {
  if (msg.cmd === 'state') {
    const r = await fetch('/collab?room=' + encodeURIComponent(roomName) + '&since=' + encodeURIComponent(state.rev), { cache: 'no-store' });
    return r.json();
  }
  const payload = {
    ...msg,
    room: roomName,
    clientId,
    requestId: msg.requestId || ((window.crypto && crypto.randomUUID)
      ? crypto.randomUUID() : clientId + '-' + Date.now() + '-' + Math.random()),
    baseRevision: msg.baseRevision === undefined ? state.rev : msg.baseRevision,
  };
  const r = await fetch('/collab', {
    method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(payload),
  });
  return r.json();
}

async function apply(resp: any, keep: EditorPosition): Promise<void> {
  if (!resp.ok) { showError(resp.error || 'request failed'); render(); setCaret(keep); return; }
  const bridge = await window.__leanBridgeReady;
  if (resp.changes && resp.changes.length) await sendLeanAndWait(bridge, 'remote', resp.changes,
    snapshot => snapshot.rev >= state.rev + resp.changes.length);
  state.canUndo = !!resp.canUndo;
  state.canRedo = !!resp.canRedo;
  render();
  collabStatus.textContent = 'Connected · revision ' + state.rev;
  editorContent.focus();
  setCaret(resp.cursor || keep);
}

function caretAfterInsert(from: EditorPosition, text: string): EditorPosition {
  const normalized = text.replace(/\r\n?/g, '\n');
  const lines = normalized.split('\n');
  if (lines.length === 1) return { block: from.block, offset: from.offset + cpLen(lines[0]) };
  return { block: from.block + lines.length - 1, offset: cpLen(lines[lines.length - 1]) };
}

async function replace(from: EditorPosition, to: EditorPosition, text: string): Promise<void> {
  failedFlush = false;
  const bridge = await window.__leanBridgeReady;
  await sendLeanAndWait(bridge, 'intent', { cmd: 'replace', from, to, text },
    snapshot => snapshot.pendingCount >= state.pendingCount);
  // beforeinput is cancelled, so the browser never advances its native caret.
  setCaret(text ? caretAfterInsert(from, text) : from);
}

function rangeText(from: EditorPosition, to: EditorPosition): string {
  if (from.block === to.block) {
    const t = state.doc[from.block].text;
    return [...t].slice(from.offset, to.offset).join('');
  }
  const parts = [];
  for (let b = from.block; b <= to.block; b++) {
    const cps = [...state.doc[b].text];
    parts.push(cps.slice(b === from.block ? from.offset : 0, b === to.block ? to.offset : cps.length).join(''));
  }
  return parts.join('\n');
}

/* ---- serialized UI actions not handled directly by beforeinput ---- */
async function perform(it: any): Promise<void> {
  const { from, to } = currentRange();
  switch (it.type) {
    case 'compose': return replace(it.from, it.to, it.text);
    case 'cut':
      return cmp(from, to) === 0 ? undefined : replace(from, to, '');
    case 'undo': return apply(await api({ cmd: 'undo' }), from);
    case 'redo': return apply(await api({ cmd: 'redo' }), from);
    case 'kind': {
      failedFlush = false;
      const bridge = await window.__leanBridgeReady;
      await sendLeanAndWait(bridge, 'intent', { cmd: 'setKind', block: from.block, kind: it.kind },
        snapshot => snapshot.pendingCount > state.pendingCount);
      setCaret(from);
      return;
    }
  }
}

const queue = [];
let running = false;

async function drain(): Promise<void> {
  running = true;
  while (queue.length) {
    const it = queue.shift();
    try { await perform(it); } catch (e) { showError(String(e)); }
  }
  running = false;
}
function enqueue(it: any): void { queue.push(it); if (!running) drain(); }

/* ---- DOM events ---- */
let composing = null;

editor.addEventListener('compositionstart', () => { composing = currentRange(); });
editor.addEventListener('compositionend', (e: CompositionEvent) => {
  const c = composing; composing = null;
  if (c) enqueue({ type: 'compose', from: c.from, to: c.to, text: e.data || '' });
});

// Read browser selection and clipboard payload only. The delegated Lasm
// listener sends these facts to Lean, which constructs and applies the edit.
document.addEventListener('beforeinput', (e: InputEvent) => {
  if (!editor.contains(e.target as Node)) return;
  const range = currentRange();
  const from = range.from, to = range.to;
  e.otFromBlock = from.block; e.otFromOffset = from.offset;
  e.otToBlock = to.block; e.otToOffset = to.offset;
  e.otData = e.data || (e.dataTransfer ? e.dataTransfer.getData('text/plain') : '');
  let caret = from;
  if (['insertText', 'insertParagraph', 'insertLineBreak', 'insertFromPaste',
       'insertFromDrop', 'insertReplacementText'].includes(e.inputType)) {
    const text = e.inputType === 'insertParagraph' || e.inputType === 'insertLineBreak'
      ? '\n' : e.otData.replace(/\r\n?/g, '\n');
    const lines = text.split('\n');
    caret = { block: from.block + lines.length - 1,
      offset: lines.length === 1 ? from.offset + cpLen(lines[0]) : cpLen(lines[lines.length - 1]) };
  } else if (e.inputType === 'deleteContentBackward' && cmp(from, to) === 0) {
    if (from.offset > 0) caret = { block: from.block, offset: from.offset - 1 };
    else if (from.block > 0) caret = { block: from.block - 1, offset: blockLen(from.block - 1) };
  }
  e.otCaretBlock = caret.block; e.otCaretOffset = caret.offset;
}, true);
document.addEventListener('beforeinput', (e: InputEvent) => {
  // Lasm handles the event at the editor mount root and patches its view
  // before bubbling reaches document. Restore the browser selection afterward.
  if (e.defaultPrevented && editor.contains(e.target as Node) &&
      Number.isInteger(e.otCaretBlock) && Number.isInteger(e.otCaretOffset)) {
    setCaret({ block: e.otCaretBlock, offset: e.otCaretOffset });
  }
}, false);

editor.addEventListener('cut', (e: ClipboardEvent) => {
  const { from, to } = currentRange();
  if (cmp(from, to) === 0) return;
  if (e.clipboardData) e.clipboardData.setData('text/plain', rangeText(from, to));
  e.preventDefault();
  enqueue({ type: 'cut' });
});

editor.addEventListener('keydown', (e: KeyboardEvent) => {
  const mod = e.ctrlKey || e.metaKey;
  const k = (e.key || '').toLowerCase();
  if (mod && k === 'z') { e.preventDefault(); enqueue({ type: e.shiftKey ? 'redo' : 'undo' }); }
  else if (mod && k === 'y') { e.preventDefault(); enqueue({ type: 'redo' }); }
});

/* ---- toolbar ---- */
for (const b of [els.undo, els.redo]) b.addEventListener('mousedown', (e: MouseEvent) => e.preventDefault());
els.undo.addEventListener('click', () => enqueue({ type: 'undo' }));
els.redo.addEventListener('click', () => enqueue({ type: 'redo' }));
els.kind.addEventListener('change', () => enqueue({ type: 'kind', kind: els.kind.value }));

/* ---- Lean client bridge + initial room state ---- */
window.__editorBridgeSnapshot = (raw: LeanSnapshot) => {
  const focused = document.activeElement === editorContent;
  const caret = focused ? currentRange().to : lastPos;
  const next = raw;
  if (!next || next.ok === false) {
    failedFlush = true;
    const message = next && next.error ? next.error : 'Lean client rejected an update';
    showError(message);
    const waiters = bridgeSnapshotWaiters;
    bridgeSnapshotWaiters = [];
    waiters.forEach(waiter => waiter.reject(new Error(message)));
    return;
  }
  const readyWaiters = [];
  const remainingWaiters = [];
  for (const waiter of bridgeSnapshotWaiters) {
    if (waiter.matches(next)) readyWaiters.push(waiter);
    else remainingWaiters.push(waiter);
  }
  bridgeSnapshotWaiters = remainingWaiters;
  state = { ...next, canUndo: state.canUndo, canRedo: state.canRedo };
  render();
  if (focused) setCaret(caret);
  readyWaiters.forEach(waiter => waiter.resolve(next));
  if (roomReady && state.pendingOps && state.pendingOps.length && !networkBusy && !failedFlush) {
    void flushPending();
  }
};
window.__editorBridgeError = message => showError(String(message));
window.__editorServerAction = action => enqueue({ type: String(action) });

async function flushPending(): Promise<void> {
  if (networkBusy || failedFlush || !roomReady || !window.__leanBridgeReady) return;
  if (!state.pendingOps || !state.pendingOps.length) return;
  networkBusy = true;
  if (!pendingRequest) {
    pendingRequest = {
      requestId: (window.crypto && crypto.randomUUID)
        ? crypto.randomUUID() : clientId + '-' + Date.now() + '-' + Math.random(),
      baseRevision: state.rev,
      ops: state.pendingOps
    };
  }
  try {
    const resp = await api({
      cmd: 'submitOps',
      ops: pendingRequest.ops,
      requestId: pendingRequest.requestId,
      baseRevision: pendingRequest.baseRevision
    });
    if (!resp.ok) {
      const latest = await api({ cmd: 'state' });
      if (latest.ok && latest.rev > state.rev && latest.changes && latest.changes.length) {
        const bridge = await window.__leanBridgeReady;
        await sendLeanAndWait(bridge, 'remote', latest.changes,
          snapshot => snapshot.rev >= latest.rev);
        state.canUndo = !!latest.canUndo;
        state.canRedo = !!latest.canRedo;
        render();
        // The server rejected the stale base; the transformed pending queue
        // will be submitted as a fresh request at the new revision.
        pendingRequest = null;
      } else {
        failedFlush = true;
        showError(resp.error || 'request failed');
      }
    } else {
      const bridge = await window.__leanBridgeReady;
      if (resp.changes && resp.changes.length) await sendLeanAndWait(bridge, 'remote', resp.changes,
         snapshot => snapshot.rev >= state.rev + resp.changes.length);
      const pendingAfterAck = state.pendingCount - resp.acceptedEdit.length;
      await sendLeanAndWait(bridge, 'ack', {
        acceptedEdit: resp.acceptedEdit,
        acceptedRevision: resp.acceptedRevision
      }, snapshot => snapshot.rev >= resp.acceptedRevision &&
        snapshot.pendingCount === pendingAfterAck);
      if (state.rev !== resp.acceptedRevision) {
        failedFlush = true;
        showError('Lean client could not confirm the accepted batch');
      } else {
        pendingRequest = null;
        state.canUndo = !!resp.canUndo;
        state.canRedo = !!resp.canRedo;
        render();
        collabStatus.textContent = 'Connected · revision ' + state.rev;
      }
    }
  } catch (e) {
    // Keep the same request ID and exact payload: the server may have accepted
    // the batch even if its HTTP response was lost.
    failedFlush = true;
    showError(String(e));
  } finally {
    networkBusy = false;
  }
  if (!failedFlush && state.pendingOps && state.pendingOps.length) void flushPending();
}

if (window.__leanBridgeReady) {
  window.__leanBridgeReady.then(async bridge => {
    // Lasm mounts its editor root inside #editor. Discard the empty HTML
    // placeholder and bind selection handling to the mounted Lean view.
    const editorRoots = Array.from(editor.children).filter((el): el is HTMLElement => el instanceof HTMLElement && el.id === 'editor-content');
    editorContent = editorRoots[editorRoots.length - 1] as HTMLElement;
    if (!editorContent) throw new Error('Lean editor root was not mounted');
    for (const root of editorRoots) {
      if (root !== editorContent) root.remove();
    }
    await sendLeanAndWait(bridge, 'snapshot-request', 'ready',
      snapshot => snapshot.rev === state.rev);
    const r = await api({ cmd: 'state' });
    if (!r.ok) throw new Error(r.error || 'cannot load room state');
    if (r.changes && r.changes.length) await sendLeanAndWait(bridge, 'remote', r.changes,
        snapshot => snapshot.rev >= r.rev);
    state.canUndo = !!r.canUndo;
    state.canRedo = !!r.canRedo;
    roomReady = true;
    render();
    collabStatus.textContent = 'Connected · revision ' + state.rev;
    if (state.pendingOps && state.pendingOps.length) void flushPending();
  }).catch(error => {
    collabStatus.textContent = 'Client unavailable';
    showError('cannot start Lean client: ' + String(error));
  });
} else {
  collabStatus.textContent = 'Client unavailable';
  showError('Lean browser client is missing; build it with npm run wasm:build');
}



// Poll the authoritative room snapshot. Local input remains serialized through
// the request queue; remote snapshots are integrated only when no local request
// or IME composition is in flight.
setInterval(async () => {
  if (running || queue.length || composing || networkBusy || state.pendingCount ||
      (window.__leanBridgeReady && !roomReady)) return;
  try {
    const r = await fetch('/collab?room=' + encodeURIComponent(roomName) + '&since=' + encodeURIComponent(state.rev), { cache: 'no-store' });
    const remote = await r.json();
    if (!remote.ok) {
      collabStatus.textContent = 'Disconnected';
      return;
    }
    if (remote.rev > state.rev) {
      const focused = document.activeElement === editor;
      const caret = focused ? currentRange().to : lastPos;
      if (window.__leanBridgeReady) {
        const bridge = await window.__leanBridgeReady;
        await sendLeanAndWait(bridge, 'remote', remote.changes || [],
          snapshot => snapshot.rev >= remote.rev);
        state.canUndo = !!remote.canUndo;
        state.canRedo = !!remote.canRedo;
      } else {
        state = remote;
      }
      render();
      if (focused) setCaret(caret);
    }
    collabStatus.textContent = 'Connected · revision ' + state.rev;
  } catch (_) {
    collabStatus.textContent = 'Reconnecting…';
  }
}, 500);

document.getElementById('share-room')!.addEventListener('click', async () => {
  const url = new URL(window.location.href);
  url.searchParams.set('room', roomName);
  try {
    await navigator.clipboard.writeText(url.toString());
    collabStatus.textContent = 'Invite link copied';
  } catch (_) {
    collabStatus.textContent = url.toString();
  }
});

})();
