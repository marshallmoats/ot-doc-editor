# Verified OT editor

A web editor whose document model and operational-transformation algebra are
implemented and verified in Lean 4. A small Python bridge serves the native
single-user UI; an experimental browser client runs the Lean engine in
WebAssembly.

## Run the native editor

```sh
lake build
python3 web/server.py
```

Open http://127.0.0.1:8000.

## Test

```sh
python3 web/test_backend.py 60
npm install jsdom && node web/test_frontend.js
```

CI also runs `lake build` with the pinned Lean toolchain and builds the
browser/WebAssembly target.

## Browser/WebAssembly client

The browser entry point is `BrowserMain.lean`. It imports the shared Lean
editor core; it does not duplicate OT logic in JavaScript.

```sh
npm install
npm run wasm:dev
npm run wasm:build
```

See [docs/wasm-client.md](docs/wasm-client.md) for the current browser scope
and collaboration architecture.

## Layout

- `OT.lean` — verified OT algebra, TP1 proofs, block operations, server convergence, selective undo.
- `Editor/Core.lean` — document/session types, proof-carrying undo/redo, and edit builders.
- `Editor/Collaboration.lean` — optimistic client state, pending local edits, remote rebasing, and acknowledgement.
- `Main.lean` — native JSON-lines server protocol.
- `BrowserMain.lean` — experimental browser/WebAssembly UI.
- `web/` — Python bridge, native UI, and tests.

## Trust model

Every committed edit is checked against `ValidSeq`. Session and collaborative
client state carry proofs that the document, pending queue, and undo/redo
chains remain valid. The UI/edit builders are not verified; malformed edits
are rejected rather than corrupting the document.

## Current limitations

The collaborative state machine is a Lean core milestone. A network transport,
multi-client browser UI, remote cursors, persistence, and end-to-end browser
convergence tests remain to be implemented.
