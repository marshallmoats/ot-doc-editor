# Browser clients and live collaboration

## WebAssembly demo

The browser entry point is `BrowserMain.lean`. It runs the shared Lean editor
model in WebAssembly; the browser does not reimplement the OT/document logic in
JavaScript.

```sh
npm install
npm run wasm:dev
```

This page demonstrates local editing and a deterministic two-client replay
inside the Lean/WebAssembly build. The replay is not a network session.

## Live shared-room demo

The live shared-room browser UI is served by `web/server.py`. Its Python
bridge routes HTTP requests to one long-lived Lean collaboration process per
room. The Lean process owns the authoritative revision log and accepts edits
through `CollaborationServer.accept`.

```sh
lake build
python3 web/server.py
```

Open `http://127.0.0.1:8000/?room=demo` in two browser tabs. Edit in either
tab; the other tab polls the room snapshot and updates automatically. The
**Copy invite link** button copies the URL for the current room. Use another
room name in the query string to create an independent room, for example
`?room=review`.

For a trusted local network demo, bind to all interfaces:

```sh
OT_HOST=0.0.0.0 python3 web/server.py
```

Then share the host computer's LAN address and room URL. This server is
unauthenticated and unencrypted: do not expose it to the public internet.

## Request and consistency model

- Each browser tab has a client ID and sends a unique request ID per edit.
- Each edit includes the revision and document coordinates on which it was
  composed.
- The Lean room process reconstructs the edit against that historical
  snapshot, checks `ValidSeq`, and submits it through the verified revisioned
  server. Stale edits are transformed over intervening accepted edits.
- The server serializes accepted requests into a single monotonically
  increasing revision sequence. Browser tabs poll for newer snapshots.
- The Python adapter caches successful request receipts to make a repeated
  request ID idempotent for the lifetime of that room process.

## Current demo boundaries

Rooms, the revision log, and the adapter's request cache live in memory and
are lost on restart. Shared undo/redo, presence, remote cursors, authentication,
authorization, durable persistence, and TLS are not implemented. Room names
are identifiers, not access controls. The live shared-room UI is the existing
native browser page; the WebAssembly page remains a separate deterministic
proof-of-concept. CI exercises two independent stale-base submissions against
the real Lean room executable and checks that both edits survive at revision 2.
