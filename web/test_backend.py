import json, random, subprocess, sys, os

EXE = os.path.join(os.path.dirname(__file__), "..", ".lake", "build", "bin", "ot-editor")

class Backend:
    def __init__(self):
        self.p = subprocess.Popen([EXE], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    def call(self, **msg):
        self.p.stdin.write(json.dumps(msg) + "\n"); self.p.stdin.flush()
        return json.loads(self.p.stdout.readline())
    def close(self):
        self.p.stdin.close(); self.p.wait()

NEXT = {"h1": "para", "h2": "para"}

def model_replace(doc, i, p, j, q, text):
    """Reference semantics: delete range, keep first block's kind, then insert (\\n splits)."""
    doc = [dict(b) for b in doc]
    head = doc[i]["text"][:p]; tail = doc[j]["text"][q:]
    kind = doc[i]["kind"]
    new = doc[:i] + [{"kind": kind, "text": head + tail}] + doc[j+1:]
    cur_i, cur_p, cur_kind = i, p, kind
    for ch in text:
        if ch == "\r": continue
        b = new[cur_i]
        if ch == "\n":
            nk = NEXT.get(cur_kind, cur_kind)
            new[cur_i:cur_i+1] = [{"kind": b["kind"], "text": b["text"][:cur_p]},
                                  {"kind": nk, "text": b["text"][cur_p:]}]
            cur_i, cur_p, cur_kind = cur_i + 1, 0, nk
        else:
            b["text"] = b["text"][:cur_p] + ch + b["text"][cur_p:]
            cur_p += 1
    return new

def rand_pos(doc):
    i = random.randrange(len(doc)); return i, random.randint(0, len(doc[i]["text"]))

def main(seed):
    random.seed(seed)
    be = Backend()
    st = be.call(cmd="state"); assert st["ok"]
    doc = st["doc"]
    history = [doc]
    last_rev = st["rev"]
    alphabet = "abcdefg hi\n😀é"
    for step in range(120):
        r = random.random()
        if r < 0.15:
            i = random.randrange(len(doc)); k = random.choice(["para", "h1", "h2", "item", "quote"])
            resp = be.call(cmd="setKind", block=i, kind=k)
            assert resp["ok"], resp
            new = [dict(b) for b in doc]; new[i]["kind"] = k
        else:
            a = rand_pos(doc); b = rand_pos(doc)
            if (b[0], b[1]) < (a[0], a[1]): a, b = b, a
            if random.random() < 0.3: b = a
            text = "".join(random.choice(alphabet) for _ in range(random.randint(0, 4)))
            resp = be.call(cmd="replace", **{"from": {"block": a[0], "offset": a[1]},
                                              "to": {"block": b[0], "offset": b[1]}, "text": text})
            assert resp["ok"], (resp, a, b, text)
            new = model_replace(doc, a[0], a[1], b[0], b[1], text)
        assert resp["doc"] == new, f"seed {seed} step {step}: backend {resp['doc']} != model {new}"
        if resp["rev"] != last_rev:      # a log entry was committed (even if the text is unchanged)
            history.append(new)
            last_rev = resp["rev"]
        doc = new
    # undo everything, checking each intermediate state
    for expect in reversed(history[:-1]):
        resp = be.call(cmd="undo"); assert resp["ok"]
        assert resp["doc"] == expect, f"undo mismatch: {resp['doc']} != {expect}"
    assert not be.call(cmd="state")["canUndo"]
    # redo everything
    for expect in history[1:]:
        resp = be.call(cmd="redo"); assert resp["ok"]
        assert resp["doc"] == expect, f"redo mismatch: {resp['doc']} != {expect}"
    assert not be.call(cmd="state")["canRedo"]
    # rejected edits leave state untouched
    before = be.call(cmd="state")
    bad = be.call(cmd="replace", **{"from": {"block": 99, "offset": 0}, "to": {"block": 99, "offset": 0}, "text": "x"})
    assert not bad["ok"]
    bad2 = be.call(cmd="replace", **{"from": {"block": 0, "offset": 999}, "to": {"block": 0, "offset": 999}, "text": "x"})
    assert not bad2["ok"]
    assert be.call(cmd="state")["doc"] == before["doc"]
    be.close()
    return len(history)

if __name__ == "__main__":
    for seed in range(int(sys.argv[1]) if len(sys.argv) > 1 else 20):
        n = main(seed)
    print("backend tests passed; last run had", n, "distinct states")
