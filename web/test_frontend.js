// End-to-end UI test: real page + real Lean backend, simulated with jsdom.
//   npm install jsdom && node web/test_frontend.js
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const require = createRequire(import.meta.url);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const { JSDOM } = require(process.env.JSDOM_PATH || 'jsdom');
const { spawn } = require('child_process');
const assert = require('assert');

const PORT = 8770 + Math.floor(Math.random() * 100);
const base = `http://127.0.0.1:${PORT}`;
const sleep = ms => new Promise(r => setTimeout(r, ms));
const waitIdle = async (win, label) => Promise.race([
  win.__editor.whenIdle(),
  sleep(15000).then(() => { throw new Error(label + " timed out: " +
    JSON.stringify({state: win.__editor.state, collab: win.document.getElementById('collab-status').textContent,
      status: win.document.getElementById('status').textContent})); }),
]);

async function main() {
  const server = spawn('python3', [path.join(__dirname, 'server.py'), String(PORT)], { stdio: 'ignore', env: { ...process.env, OT_COLLAB_DELAY_MS: "300" } });
  try {
    for (let i = 0; i < 50; i++) { try { await fetch(base + '/'); break; } catch { await sleep(100); } }
    const dom = await JSDOM.fromFile(path.join(__dirname, 'index.html'), {
      runScripts: 'dangerously', resources: 'usable', pretendToBeVisual: true,
      beforeParse(w) { w.fetch = (u, o) => fetch(base + u, o); },
    });
    const w = dom.window, d = w.document;
    const ed = d.getElementById('editor');
    await sleep(300); await waitIdle(w, 'initial editor');

    const texts = () => [...ed.children].map(c => c.textContent);
    const kinds = () => [...ed.children].map(c => c.className.replace('block k-', ''));
    const caret = () => { const s = w.getSelection(); return [s.anchorNode, s.anchorOffset]; };
    const place = (block, off) => {   // collapse caret inside a block's text node
      const r = d.createRange(); const t = ed.children[block].firstChild;
      if (t.nodeType === 3) r.setStart(t, off); else r.setStart(ed.children[block], 0);
      r.collapse(true); const s = w.getSelection(); s.removeAllRanges(); s.addRange(r);
    };
    const select = (b1, o1, b2, o2) => {
      const t1 = ed.children[b1].firstChild, t2 = ed.children[b2].firstChild;
      w.getSelection().setBaseAndExtent(t1, o1, t2, o2);
    };
    const input = async (inputType, data, extra = {}) => {
      const ev = new w.InputEvent('beforeinput', { inputType, data, bubbles: true, cancelable: true });
      Object.assign(ev, extra);
      ed.dispatchEvent(ev);
      assert(ev.defaultPrevented, 'beforeinput must be intercepted: ' + inputType);
      await waitIdle(w, 'editor operation');
    };
    const key = async (k, mods = {}) => {
      ed.dispatchEvent(new w.KeyboardEvent('keydown', { key: k, bubbles: true, cancelable: true, ...mods }));
      await waitIdle(w, 'editor operation');
    };

    assert.strictEqual(texts().length, 3);
    assert.strictEqual(kinds()[0], 'h1');
    const original = texts();

    // typing: three fast keystrokes queued back to back must land in order
    place(1, 0);
    const p1 = input('insertText', 'a');
    const p2 = input('insertText', 'b');
    const p3 = input('insertText', 'c');
    assert.strictEqual(texts()[1].slice(0, 3), 'abc',
      'all local keystrokes render before the delayed server acknowledgement');
    assert.strictEqual(w.__editor.state.rev, 0,
      'optimistic edits do not wait for the server revision');
    await Promise.all([p1, p2, p3]);
    assert.strictEqual(texts()[1].slice(0, 3), 'abc');
    assert.strictEqual(w.__editor.state.rev, 2,
      'the first request and the queued suffix are acknowledged as two batches');
    let [typingNode, typingOffset] = caret();
    assert.strictEqual(typingNode.data.slice(0, typingOffset), 'abc',
      'caret must advance to the end of each accepted insertion');
    await key('z', { ctrlKey: true });
    assert(!texts()[1].startsWith('abc'), 'Ctrl+Z undoes the latest shared text edit');
    await key('z', { ctrlKey: true, shiftKey: true });
    assert(texts()[1].startsWith('abc'), 'Ctrl+Shift+Z redoes the shared text edit');

    // Enter in the middle splits; Backspace at start of block merges back
    place(1, 3);
    await input('insertParagraph');
    assert.strictEqual(texts().length, 4);
    assert.strictEqual(texts()[1], 'abc');
    let [n, o] = caret(); const caretBlock = n.nodeType === 3 ? n.parentNode : n; assert.strictEqual(caretBlock.dataset.i, '2'); assert.strictEqual(o, 0);
    await input('deleteContentBackward');
    assert.strictEqual(texts().length, 3);
    assert.strictEqual(texts()[1].slice(0, 3), 'abc');
    [n, o] = caret(); assert.strictEqual(o, 3);

    // Enter inside a heading creates a paragraph
    place(0, 5);
    await input('insertParagraph');
    assert.deepStrictEqual(kinds().slice(0, 2), ['h1', 'para']);

    // selection across blocks, typed over
    select(0, 2, 1, 3);
    await input('insertText', 'ZZ');
    assert(texts()[0].startsWith('A ZZ'), texts()[0]);

    // astral characters count as one character (Lean counts code points)
    place(2, 0);
    await input('insertText', '😀');
    await input('insertText', 'x');
    assert(texts()[2].startsWith('😀x'), texts()[2]);
    await input('deleteContentBackward');            // removes 'x'
    await input('deleteContentBackward');            // removes the emoji, as one character
    assert(!texts()[2].startsWith('😀'), 'emoji removed in one step');

    // paste with newlines
    place(2, 0);
    await input('insertFromPaste', null, { dataTransfer: { getData: () => 'one\ntwo' } });
    const before = texts().length;
    assert(texts()[2].startsWith('one') && texts()[3].startsWith('two'));

    // block kind via the toolbar
    place(2, 1);
    const sel = d.getElementById('kind'); sel.value = 'item';
    sel.dispatchEvent(new w.Event('change', { bubbles: true }));
    await waitIdle(w, 'editor operation');
    assert.strictEqual(kinds()[2], 'item');

    // a stale/invalid request is rejected without corrupting the view
    const r = await (await fetch(base + '/api', { method: 'POST', body: JSON.stringify(
      { cmd: 'replace', from: { block: 50, offset: 0 }, to: { block: 50, offset: 0 }, text: 'x' }) })).json();
    assert.strictEqual(r.ok, false);

    // Two browser clients edit the same position concurrently. The client-side
    // pending queue must rebase one edit over the other's accepted operation.
    const openRoom = async room => JSDOM.fromFile(path.join(__dirname, 'index.html'), {
      url: base + '/?room=' + room, runScripts: 'dangerously', resources: 'usable',
      pretendToBeVisual: true,
      beforeParse(win) { win.fetch = (u, o) => fetch(base + u, o); },
    });
    const d1 = await openRoom('ot-race'), d2 = await openRoom('ot-race');
    const w1 = d1.window, w2 = d2.window;
    for (let i=0;i<30 && (!w1.__editor.state || !w2.__editor.state);i++) await sleep(50);
    const typeAtStart = (win, ch) => {
      const ed2 = win.document.getElementById('editor');
      const range = win.document.createRange(), text = ed2.children[1].firstChild;
      range.setStart(text, 0); range.collapse(true);
      win.getSelection().removeAllRanges(); win.getSelection().addRange(range);
      ed2.dispatchEvent(new win.InputEvent('beforeinput', {
        inputType: 'insertText', data: ch, bubbles: true, cancelable: true,
      }));
      return ed2.children[1].textContent;
    };
    assert(typeAtStart(w1, 'A').startsWith('A'));
    assert(typeAtStart(w2, 'B').startsWith('B'));
    await Promise.all([waitIdle(w1, 'client one'), waitIdle(w2, 'client two')]);
    await sleep(450); // allow the peer polling cycle to integrate the final revision
    const authoritative = await (await fetch(base + '/collab?room=ot-race')).json();
    assert(authoritative.ok);
    assert(authoritative.doc[1].text.includes('A') && authoritative.doc[1].text.includes('B'),
      'server retains both concurrent edits');
    assert.strictEqual(JSON.stringify(w1.__editor.state.doc), JSON.stringify(authoritative.doc));
    assert.strictEqual(JSON.stringify(w2.__editor.state.doc), JSON.stringify(authoritative.doc));
    d1.window.close(); d2.window.close();

    console.log('frontend end-to-end tests passed');
    w.close();
  } finally { server.kill(); }
}
main().catch(e => { console.error(e); process.exit(1); });
