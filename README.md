# Verified OT editor

A single-user web editor (paragraphs, headings, list items, quotes, undo/redo) whose
core is written and verified in Lean 4. A tiny Python bridge serves the page.

## Run

    lake build                 # needs Lean 4.20 (elan reads lean-toolchain); first build compiles the proofs
    python3 web/server.py      # then open http://127.0.0.1:8000

## Test

    python3 web/test_backend.py 60                 # randomized: backend vs. reference model, full undo/redo
    npm install jsdom && node web/test_frontend.js # real page + real backend under jsdom

## Layout

- `OT.lean`   — the verified library: `OTAlg`, TP1 for text and block algebras, the keyed product
                (referenced tables), edits, server convergence, undo lemmas.
- `Main.lean` — the backend: session with proof-carrying invariants, edit builders, JSON-lines protocol.
- `web/`      — bridge (`server.py`), UI (`index.html`), tests.

## Trust model

Every committed edit goes through `if h : ValidSeq e doc`, so the session carries proofs that
(1) the whole log replays without an invalid op and (2) the undo/redo stacks are valid chains.
The edit *builders* (keystroke → ops) and the browser code are **not** verified: a builder bug can
only make an edit be rejected or produce a different valid edit, never corrupt the document.
Undo/redo apply exact inverses (`invSeq_correct`).

## Protocol (one JSON object per line on stdin/stdout, also `POST /api`)

    {"cmd":"state"}
    {"cmd":"replace","from":{"block":i,"offset":p},"to":{"block":j,"offset":q},"text":"..."}
    {"cmd":"setKind","block":i,"kind":"para|h1|h2|item|quote"}
    {"cmd":"undo"}   {"cmd":"redo"}

Offsets count Unicode code points. Replies: `{ok, doc:[{kind,text}], rev, canUndo, canRedo, cursor}`.

## Not done yet

Collaboration (clients, remote cursors, transforming undo entries over remote edits), tables in the UI
(the verified `WOp` layer exists, see `OT.lean`), persistence, inline marks, IME beyond composition end,
typing-run coalescing for undo (currently one undo step per keystroke).
