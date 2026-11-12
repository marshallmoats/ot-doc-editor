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

async function main() {
  const server = spawn('python3', [path.join(__dirname, 'server.py'), String(PORT)], { stdio: 'ignore' });
  try {
    for (let i = 0; i < 50; i++) { try { await fetch(base + '/'); break; } catch { await sleep(100); } }
    const dom = await JSDOM.fromFile(path.join(__dirname, 'index.html'), {
      runScripts: 'dangerously', pretendToBeVisual: true,
      beforeParse(w) { w.fetch = (u, o) => fetch(base + u, o); },
    });
    const w = dom.window, d = w.document;
    const ed = d.getElementById('editor');
    await sleep(300); await w.__editor.whenIdle();

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
      await w.__editor.whenIdle();
    };
    const key = async (k, mods = {}) => {
      ed.dispatchEvent(new w.KeyboardEvent('keydown', { key: k, bubbles: true, cancelable: true, ...mods }));
      await w.__editor.whenIdle();
    };

    assert.strictEqual(texts().length, 3);
    assert.strictEqual(kinds()[0], 'h1');
    const original = texts();

    // typing: three fast keystrokes queued back to back must land in order
    place(1, 0);
    input('insertText', 'a'); input('insertText', 'b'); await input('insertText', 'c');
    assert.strictEqual(texts()[1].slice(0, 3), 'abc');
    assert.strictEqual(w.__editor.state.rev, 3);
    let [typingNode, typingOffset] = caret();
    assert.strictEqual(typingNode.data.slice(0, typingOffset), 'abc',
      'caret must advance to the end of each accepted insertion');

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
    await w.__editor.whenIdle();
    assert.strictEqual(kinds()[2], 'item');

    // Shared undo/redo is wired through the room server and toolbar/shortcuts.
    assert.strictEqual(kinds()[2], 'item');
    await key('z', { ctrlKey: true });
    assert.strictEqual(kinds()[2], 'para', 'Ctrl+Z undoes the most recent shared formatting edit');
    assert.strictEqual(d.getElementById('redo').disabled, false);
    await key('z', { ctrlKey: true, shiftKey: true });
    assert.strictEqual(kinds()[2], 'item', 'Ctrl+Shift+Z redoes the shared formatting edit');
    d.getElementById('undo').click(); await w.__editor.whenIdle();
    assert.strictEqual(kinds()[2], 'para');

    // a stale/invalid request is rejected without corrupting the view
    const r = await (await fetch(base + '/api', { method: 'POST', body: JSON.stringify(
      { cmd: 'replace', from: { block: 50, offset: 0 }, to: { block: 50, offset: 0 }, text: 'x' }) })).json();
    assert.strictEqual(r.ok, false);

    console.log('frontend end-to-end tests passed');
    w.close();
  } finally { server.kill(); }
}
main().catch(e => { console.error(e); process.exit(1); });
