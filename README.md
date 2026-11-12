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

## Live browser collaboration (demo server)

The native browser editor at `web/index.html` can now join an in-memory shared
room. The Python HTTP bridge provides room routing and polling; each room owns
a long-lived `ot-collab` Lean process. Every edit is rebuilt against the
client's declared base revision and accepted by `CollaborationServer`, which
performs the authoritative stale-base transformation and validity check.

```sh
lake build
python3 web/server.py
```

Open `http://127.0.0.1:8000/?room=demo` in two separate browser tabs. Edits
made in either tab are serialized by the same room server and appear in the
other tab. Use **Copy invite link** to share the room URL. To let another
computer on your trusted LAN connect, start the server with
`OT_HOST=0.0.0.0 python3 web/server.py` and share the host machine's LAN
address. Do not expose this unauthenticated demo server to the public internet.

The `npm run wasm:dev` page remains the self-contained WebAssembly/Lean demo;
its collaboration panel is still a deterministic local replay. The live-room
transport is currently provided by the native browser page and Lean server
process, not by WebAssembly.

## Demo limitations

Rooms and request de-duplication are held in server memory and are lost when
the process restarts. This demo has no authentication, authorization, TLS,
durable storage, shared undo/redo, presence, or remote cursors. Room names are
not access controls. CI runs a real Lean-process integration test in which two
clients submit edits from revision zero and converge at revision two. Treat
this as a LAN/demo milestone, not a production multi-tenant service.
