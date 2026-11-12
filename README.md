# Verified OT editor

A web editor whose document model and operational-transformation algebra are
implemented and verified in Lean 4. The production browser editor runs the
optimistic collaboration client in Lean/WebAssembly; JavaScript is limited to
DOM, selection/IME, rendering, and HTTP transport.

## Run the live editor

Build the native collaboration server and browser client bundle, then start the
Python HTTP adapter:

```sh
lake build
npm install
npm run wasm:build
python3 web/server.py
```

Open http://127.0.0.1:8000/?room=demo in two browser tabs. Edits in either tab
appear in the other. Use **Copy invite link** to share the room URL. The server
serves the generated hashed JavaScript/WASM assets from `dist/` and mounts the
Lean client bridge into the editor page.

For a trusted local-network demo, bind to all interfaces:

```sh
OT_HOST=0.0.0.0 python3 web/server.py
```

This demo server is unauthenticated and unencrypted. Do not expose it to the
public internet.

## Client/server consistency model

- Browser input is converted to a small edit intent using DOM selection and
  input events. The intent is sent through a Lasm port to `BrowserBridge.lean`.
- Lean constructs and validates the operation against its optimistic document,
  applies it, and maintains the pending operation queue.
- JavaScript forwards Lean-generated operation batches to the server. It does
  not construct operations or implement OT transformations.
- The server returns the transformed accepted batch plus intervening log
  entries. The Lean client rebases pending operations over those entries and
  acknowledges only when the accepted operation sequence matches the pending
  prefix.
- Later local edits remain pending while earlier batches are in flight. The
  next batch is submitted from the Lean-rebased queue.
- Polling requests only changes since the client's confirmed revision. Remote
  changes are passed to Lean for validation and rebasing before the UI renders
  the resulting document.

The server serializes room mutations and performs authoritative stale-base
transformation. The browser Lean client maintains optimistic state so typing
does not wait for each HTTP acknowledgement.

To make overlapping requests easier to reproduce, set
`OT_COLLAB_DELAY_MS` to add a delay (0–60000 ms) before each mutation enters
the room's serialization lock:

```sh
OT_COLLAB_DELAY_MS=250 python3 web/server.py
```

The delay is disabled by default and does not affect reads.

## Standalone WebAssembly exercise

`BrowserMain.lean` remains a deterministic Lean/WASM exercise for the shared
editor core and collaboration server. Run it with:

```sh
npm install
npm run wasm:dev
```

This standalone page is a local replay, not a network session. The production
browser bridge is `BrowserBridge.lean`, built by `npm run wasm:build`.

## Test

```sh
lake build
python3 web/test_backend.py 60
npm install jsdom && node web/test_frontend.js
python3 web/test_server_delay.py
python3 web/test_collaboration.py
```

CI additionally builds the browser/WASM target and verifies that the Python
server injects the Lasm mount bootstrap and serves the generated JavaScript and
WASM assets.

## Layout

- `OT.lean` — verified OT algebra, TP1 proofs, block operations, server
  convergence, and selective undo.
- `Editor/Core.lean` — document/session types, proof-carrying undo/redo, and
  edit builders.
- `Editor/Collaboration.lean` — optimistic client state, pending local edits,
  remote rebasing, and prefix acknowledgement.
- `Editor/Collaboration/Server.lean` — revisioned server acceptance,
  stale-base transformation, and client/request receipts.
- `BrowserBridge.lean` — Lean/WASM state machine and structured Lasm ports for
  the production browser editor.
- `BrowserMain.lean` — standalone deterministic browser exercise.
- `CollaborationMain.lean` — JSON-lines protocol for the native room server.
- `web/` — DOM/IME UI, HTTP adapter, and integration tests.

## Trust model and limitations

Every committed edit is checked against `ValidSeq`. Client state carries
proofs that the document and pending queue remain valid. Browser selection and
input-intent interpretation are UI integration code, not verified Lean
logic; malformed intents and operation batches are rejected.

Rooms, the revision log, and request de-duplication are in memory and are lost
when the process restarts. The demo has no authentication, authorization, TLS,
durable storage, presence, or remote cursors. Room names are identifiers, not
access controls. Treat this as a LAN/demo milestone, not a production
multi-tenant service.
