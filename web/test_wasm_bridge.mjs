import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import { JSDOM } from "jsdom";
import { TextDecoder, TextEncoder } from "node:util";

const root = process.cwd();
const dist = join(root, "dist");
const loader = readdirSync(dist).find(
  name => name.startsWith("app.") && name.endsWith(".js")
);
assert.ok(loader, "missing generated Lasm app loader");

const dom = new JSDOM('<!doctype html><html><body><div id="root"></div></body></html>', {
  url: "http://127.0.0.1/",
  pretendToBeVisual: true
});
for (const name of [
  "window", "document", "navigator", "HTMLElement", "Element", "Node",
  "Text", "Document", "MutationObserver", "Event", "CustomEvent",
  "DOMParser", "getComputedStyle"
]) {
  const value = name === "getComputedStyle"
    ? dom.window.getComputedStyle.bind(dom.window)
    : dom.window[name];
  if (value !== undefined) {
    Object.defineProperty(globalThis, name, {
      value, configurable: true, writable: true
    });
  }
}
globalThis.requestAnimationFrame = dom.window.requestAnimationFrame.bind(dom.window);
globalThis.cancelAnimationFrame = dom.window.cancelAnimationFrame.bind(dom.window);
globalThis.TextEncoder = TextEncoder;
globalThis.TextDecoder = TextDecoder;

const { mount } = await import(pathToFileURL(join(dist, loader)).href);
const app = await mount(document.getElementById("root"));
const snapshots = [];
app.ports.snapshot.subscribe(snapshot => snapshots.push(snapshot));

async function sendAndRead(portName, payload) {
  const before = snapshots.length;
  await app.ports[portName].send(payload);
  const deadline = Date.now() + 5000;
  while (snapshots.length === before && Date.now() < deadline) {
    await new Promise(resolve => setTimeout(resolve, 5));
  }
  assert.ok(snapshots.length > before, `no Lean snapshot after ${portName}`);
  return snapshots.at(-1);
}

await sendAndRead("snapshot-request", "ready");
const initial = snapshots.at(-1);
assert.equal(initial.ok, true);
assert.equal(initial.pendingCount, 0);

const optimistic = await sendAndRead("intent", {
  cmd: "replace",
  from: { block: 0, offset: 0 },
  to: { block: 0, offset: 0 },
  text: "!"
});
assert.equal(optimistic.ok, true);
assert.equal(optimistic.pendingCount, 1);
assert.equal(optimistic.pendingOps.length, 1);

const rebased = await sendAndRead("remote", [[{
  tag: "blk",
  block: 0,
  core: { op: "ins", offset: 0, char: "?" }
}]]);
assert.equal(rebased.ok, true);
assert.equal(rebased.rev, 1);
assert.equal(rebased.pendingCount, 1);
assert.equal(rebased.pendingOps[0].core.offset, 1);
assert.ok(rebased.doc[0].text.startsWith("?!"));

const acknowledged = await sendAndRead("ack", {
  acceptedEdit: [{
    tag: "blk",
    block: 0,
    core: { op: "ins", offset: 1, char: "!" }
  }],
  acceptedRevision: 2
});
assert.equal(acknowledged.ok, true);
assert.equal(acknowledged.rev, 2);
assert.equal(acknowledged.pendingCount, 0);
assert.ok(acknowledged.doc[0].text.startsWith("?!"));

dom.window.close();
console.log("Lean/WASM browser client intent, remote rebase, and prefix acknowledgement passed");
