/* Browser-side implementation of the verified OT operation algebra.
   Operation shapes mirror OT.lean and CollaborationMain.lean. */
(() => {
  "use strict";
  const cp = s => Array.from(s);
  const nop = () => ({ tag: "nop" });
  const blk = (index, core) => ({ tag: "blk", index, core });
  const inline = (index, op) => blk(index, { tag: "inl", op });
  const cloneDoc = d => d.map(b => ({ kind: b.kind, text: b.text }));

  function applyInline(op, text) {
    const a = cp(text);
    if (op.tag === "nop") return text;
    if (op.tag === "ins") { a.splice(op.pos, 0, op.char); return a.join(""); }
    if (op.tag === "del") { a.splice(op.pos, 1); return a.join(""); }
    throw new Error("unknown inline operation");
  }
  function applyOne(doc, op) {
    if (op.tag === "nop") return doc;
    const i = op.index, c = op.core;
    if (c.tag === "nop") return doc;
    const b = doc[i];
    if (!b) throw new Error("operation references missing block " + i);
    switch (c.tag) {
      case "inl": doc[i] = { ...b, text: applyInline(c.op, b.text) }; break;
      case "setK": doc[i] = { ...b, kind: c.new }; break;
      case "split": {
        const chars = cp(b.text);
        doc.splice(i, 1, { kind: b.kind, text: chars.slice(0, c.pos).join("") },
          { kind: c.kind, text: chars.slice(c.pos).join("") });
        break;
      }
      case "merge": {
        const next = doc[i + 1];
        if (!next) throw new Error("merge references missing next block");
        doc.splice(i, 2, { kind: b.kind, text: b.text + next.text });
        break;
      }
      default: throw new Error("unknown block operation " + c.tag);
    }
    return doc;
  }
  const applyAll = (ops, doc) => ops.reduce((d, op) => applyOne(d, op), cloneDoc(doc));

  function xpos(o, q) {
    if (o.tag === "ins") return o.pos <= q ? q + 1 : q;
    if (o.tag === "del") return o.pos < q ? q - 1 : q;
    return q;
  }
  function splitOp(o, q) {
    if (o.tag === "nop") return [0, o];
    if (o.tag === "ins") return o.pos <= q ? [0, o] : [1, { ...o, pos: o.pos - q }];
    return o.pos < q ? [0, o] : [1, { ...o, pos: o.pos - q }];
  }
  function shiftUp(q, o) {
    return o.tag === "nop" ? o : { ...o, pos: o.pos + q };
  }
  function xfInline(a, b, side) {
    if (a.tag === "nop" || b.tag === "nop") return a;
    if (a.tag === "ins" && b.tag === "ins") {
      if (a.pos < b.pos) return a;
      if (b.pos < a.pos) return { ...a, pos: a.pos + 1 };
      return { ...a, pos: side === "left" ? a.pos : a.pos + 1 };
    }
    if (a.tag === "ins" && b.tag === "del")
      return { ...a, pos: a.pos <= b.pos ? a.pos : a.pos - 1 };
    if (a.tag === "del" && b.tag === "ins")
      return { ...a, pos: a.pos < b.pos ? a.pos : a.pos + 1 };
    if (a.tag === "del" && b.tag === "del") {
      if (a.pos < b.pos) return a;
      if (a.pos === b.pos) return nop();
      return { ...a, pos: a.pos - 1 };
    }
    throw new Error("invalid inline operation pair");
  }
  function transform(a, b, side) {
    if (a.tag === "nop" || b.tag === "nop") return a;
    const i = a.index, j = b.index, x = a.core, y = b.core;
    if (x.tag === "nop") return nop();
    if (y.tag === "nop") return a;
    if (x.tag === "inl" && y.tag === "inl")
      return blk(i, { tag: "inl", op: i === j ? xfInline(x.op, y.op, side) : x.op });
    if (x.tag === "inl" && y.tag === "setK") return a;
    if (x.tag === "inl" && y.tag === "split") {
      if (i < j) return a;
      if (j < i) return blk(i + 1, x);
      const [half, op] = splitOp(x.op, y.pos);
      return blk(j + half, { tag: "inl", op });
    }
    if (x.tag === "inl" && y.tag === "merge") {
      if (i <= j) return a;
      if (i === j + 1) return blk(j, { tag: "inl", op: shiftUp(y.pos, x.op) });
      return blk(i - 1, x);
    }
    if (x.tag === "setK" && y.tag === "inl") return a;
    if (x.tag === "setK" && y.tag === "setK") {
      if (i !== j) return a;
      return side === "left" ? blk(i, { tag: "setK", old: y.new, new: x.new }) : nop();
    }
    if (x.tag === "setK" && y.tag === "split") return j < i ? blk(i + 1, x) : a;
    if (x.tag === "setK" && y.tag === "merge") {
      if (i <= j) return a;
      if (i === j + 1) return nop();
      return blk(i - 1, x);
    }
    if (x.tag === "split" && y.tag === "inl")
      return blk(i, { tag: "split", pos: i === j ? xpos(y.op, x.pos) : x.pos, kind: x.kind });
    if (x.tag === "split" && y.tag === "setK") return a;
    if (x.tag === "split" && y.tag === "split") {
      if (i < j) return a;
      if (j < i) return blk(i + 1, x);
      if (x.pos < y.pos) return a;
      if (y.pos < x.pos) return blk(i + 1, { ...x, pos: x.pos - y.pos });
      return side === "left" ? a : blk(i + 1, { ...x, pos: 0 });
    }
    if (x.tag === "split" && y.tag === "merge") {
      if (i <= j) return a;
      if (i === j + 1) return blk(j, { ...x, pos: y.pos + x.pos });
      return blk(i - 1, x);
    }
    if (x.tag === "merge" && y.tag === "inl")
      return blk(i, { ...x, pos: i === j ? xpos(y.op, x.pos) : x.pos });
    if (x.tag === "merge" && y.tag === "setK")
      return j === i + 1 ? blk(i, { ...x, kind: y.new }) : a;
    if (x.tag === "merge" && y.tag === "split") {
      if (j < i) return blk(i + 1, x);
      if (j === i) return blk(i + 1, { ...x, pos: x.pos - y.pos });
      return a;
    }
    if (x.tag === "merge" && y.tag === "merge") {
      if (j + 1 < i) return blk(i - 1, x);
      if (j + 1 === i) return blk(j, { ...x, pos: y.pos + x.pos });
      if (j === i) return nop();
      return a;
    }
    throw new Error("unknown block transform pair " + x.tag + "/" + y.tag);
  }
  function xformOne(a, bs, side) {
    let left = a, right = [];
    for (const b of bs) {
      const nextLeft = transform(left, b, side);
      right.push(transform(b, left, side === "left" ? "right" : "left"));
      left = nextLeft;
    }
    return [left, right];
  }
  function xformSeq(as, bs, side) {
    let rightBase = bs, leftOut = [];
    for (const a of as) {
      const pair = xformOne(a, rightBase, side);
      leftOut.push(pair[0]);
      rightBase = pair[1];
    }
    return [leftOut, rightBase];
  }

  function nextKind(k) { return k === "h1" || k === "h2" ? "para" : k; }
  function buildReplace(doc, from, to, text) {
    const out = [], i = from.block, p = from.offset, j = to.block, q = to.offset;
    if (i === j) {
      const chars = cp(doc[i].text);
      for (let n = p; n < q; n++) out.push(inline(i, { tag: "del", pos: p, char: chars[n] }));
    } else {
      const first = cp(doc[i].text), last = cp(doc[j].text);
      for (let n = 0; n < q; n++) out.push(inline(j, { tag: "del", pos: 0, char: last[n] }));
      for (let b = i + 1; b < j; b++) {
        for (const ch of cp(doc[b].text)) out.push(inline(b, { tag: "del", pos: 0, char: ch }));
      }
      for (let n = p; n < first.length; n++) out.push(inline(i, { tag: "del", pos: p, char: first[n] }));
      for (let b = i + 1; b <= j; b++) out.push(blk(i, { tag: "merge", pos: p, kind: doc[b].kind }));
    }
    let bi = i, off = p, kind = doc[i].kind;
    for (const ch of cp(text.replace(/\r\n?/g, "\n"))) {
      if (ch === "\n") {
        out.push(blk(bi, { tag: "split", pos: off, kind: nextKind(kind) }));
        bi++; off = 0; kind = nextKind(kind);
      } else out.push(inline(bi, { tag: "ins", pos: off++, char: ch }));
    }
    return out;
  }
  function buildKind(doc, block, kind) {
    const old = doc[block].kind;
    return old === kind ? [] : [blk(block, { tag: "setK", old, new: kind })];
  }
  function createClient(snapshot) {
    return { confirmedDoc: cloneDoc(snapshot.doc), doc: cloneDoc(snapshot.doc),
      revision: snapshot.rev, pending: [], canUndo: snapshot.canUndo, canRedo: snapshot.canRedo };
  }
  function local(client, ops) {
    client.doc = applyAll(ops, client.doc);
    client.pending.push(...ops);
    return ops;
  }
  function receiveRemote(client, change) {
    const [remote, pending] = xformSeq(change.edit, client.pending, "left");
    client.confirmedDoc = applyAll(change.edit, client.confirmedDoc);
    client.pending = pending;
    client.doc = applyAll(remote, client.doc);
    client.revision = change.revision;
    return remote;
  }
  function acknowledge(client, change, count) {
    client.confirmedDoc = applyAll(change.edit, client.confirmedDoc);
    client.pending.splice(0, count);
    client.revision = change.revision;
  }
  function encode(op) { return op; }
  window.OTClient = { applyAll, buildReplace, buildKind, createClient, local,
    receiveRemote, acknowledge, xformSeq, encode, cloneDoc };
})();