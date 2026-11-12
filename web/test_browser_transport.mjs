import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { JSDOM } from "jsdom";

const html = await readFile(new URL("./index.html", import.meta.url), "utf8");
const inline = html.match(/<script>\s*([\s\S]*?)<\/script>/);
assert.ok(inline, "production editor script was not found");

const dom = new JSDOM(html, {
  url: "http://127.0.0.1/?room=transport-test",
  pretendToBeVisual: true,
  runScripts: "outside-only"
});
const { window } = dom;
const editorContent = window.document.getElementById("editor-content");
const block = window.document.createElement("div");
block.className = "block k-para";
block.dataset.i = "0";
block.appendChild(window.document.createTextNode("hello"));
editorContent.appendChild(block);
window.setInterval = () => 0;

const operation = {
  tag: "blk", block: 0,
  core: { op: "setKind", old: "para", kind: "h1" }
};
let clientSnapshot = {
  ok: true,
  doc: [{ kind: "para", text: "hello" }],
  confirmedDoc: [{ kind: "para", text: "hello" }],
  rev: 0, pendingCount: 0, pendingOps: [],
  canUndo: false, canRedo: false
};
let postCount = 0;

const snapshot = () => window.__editorBridgeSnapshot({ ...clientSnapshot });
const delayedPort = handler => ({
  send(payload) {
    // Deliberately resolve the send promise before Lean publishes its output
    // snapshot. Production must wait for the snapshot, not just port.send().
    setTimeout(() => handler(payload), 15);
    return Promise.resolve();
  }
});
const bridge = {
  ports: {
    "snapshot-request": delayedPort(() => snapshot()),
    intent: delayedPort(() => {
      clientSnapshot = {
        ...clientSnapshot,
        doc: [{ kind: "h1", text: "hello" }],
        pendingCount: 1,
        pendingOps: [operation],
        canUndo: true
      };
      snapshot();
    }),
    remote: delayedPort(() => snapshot()),
    ack: delayedPort(payload => {
      clientSnapshot = {
        ...clientSnapshot,
        confirmedDoc: [{ kind: "h1", text: "hello" }],
        rev: payload.acceptedRevision,
        pendingCount: 0,
        pendingOps: [],
        canUndo: true
      };
      snapshot();
    })
  }
};
window.__leanBridgeReady = Promise.resolve(bridge);
window.fetch = async (_url, init = {}) => {
  if (!init.method || init.method === "GET") {
    return new Response(JSON.stringify({
      ok: true, doc: clientSnapshot.doc, rev: 0, changes: [],
      canUndo: false, canRedo: false
    }), { headers: { "Content-Type": "application/json" } });
  }
  postCount++;
  const request = JSON.parse(init.body);
  assert.equal(request.cmd, "submitOps");
  assert.deepEqual(request.ops, [operation]);
  return new Response(JSON.stringify({
    ok: true, acceptedEdit: [operation], acceptedRevision: 1,
    acceptedCount: 1, changes: [], rev: 1, canUndo: true, canRedo: false
  }), { headers: { "Content-Type": "application/json" } });
};

window.eval(inline[1]);
await new Promise(resolve => setTimeout(resolve, 60));
assert.equal(window.document.getElementById("collab-status").textContent,
  "Connected · revision 0");

const kind = window.document.getElementById("kind");
kind.value = "h1";
kind.dispatchEvent(new window.Event("change", { bubbles: true }));
const deadline = Date.now() + 2000;
while (Date.now() < deadline &&
       window.document.getElementById("collab-status").textContent !== "Connected · revision 1") {
  await new Promise(resolve => setTimeout(resolve, 10));
}
assert.equal(postCount, 1, "Lean pending operation was not submitted exactly once");
assert.equal(clientSnapshot.rev, 1);
assert.equal(clientSnapshot.pendingCount, 0);
assert.equal(window.document.getElementById("status").style.display, "none");
assert.equal(window.document.getElementById("collab-status").textContent,
  "Connected · revision 1",
  "transport checked the cached revision before Lean published its acknowledgement snapshot");

dom.window.close();
console.log("browser transport waits for the matching Lean acknowledgement snapshot");
