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

## Browser/WebAssembly demo

The browser entry point is `BrowserMain.lean`. It runs the shared Lean editor
core in WebAssembly and includes a deterministic two-client collaboration
replay using the revisioned server core.

```sh
npm install
npm run wasm:dev
```

Open the local URL printed by Lasm. Use the interactive editor controls to
append, undo, and redo; the second panel shows two stale-base client edits
serialized by the Lean collaboration server. Build the production bundle with
`npm run wasm:build`.

See [docs/wasm-client.md](docs/wasm-client.md) for prerequisites, architecture,
and limitations. The collaboration panel is a local deterministic replay,
not a live multi-user network session.

## Layout

- `OT.lean` — verified OT algebra, TP1 proofs, block operations, server convergence, selective undo.
- `Editor/Core.lean` — document/session types, proof-carrying undo/redo, and edit builders.
- `Editor/Collaboration.lean` — optimistic client state, pending local edits, remote rebasing, and acknowledgement.
- `Editor/Collaboration/Server.lean` — revisioned server acceptance, stale-base transformation, and client/request receipts.
- `Main.lean` — native JSON-lines server protocol.
- `BrowserMain.lean` — browser/WebAssembly demo.
- `web/` — Python bridge, native UI, and tests.

## Trust model

Every committed edit is checked against `ValidSeq`. Session and collaborative
client state carry proofs that the document, pending queue, and undo/redo
chains remain valid. The UI/edit builders are not verified; malformed edits
are rejected rather than corrupting the document.

## Current limitations

The collaborative state machine and revisioned server boundary are Lean core
milestones. A network transport, live multi-client browser UI, remote cursors,
persistence, and end-to-end browser convergence tests remain to be implemented.
