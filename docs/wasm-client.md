# Browser clients and live collaboration

## Production Lean/WASM client

The production editor page is `web/index.html`. Its DOM and transport shell is
JavaScript, but the optimistic collaboration state machine runs in
`BrowserBridge.lean` compiled to WebAssembly by Lasm.

Build and serve it with:

```sh
lake build
npm install
npm run wasm:build
python3 web/server.py
```

The Python server serves the hashed files generated in `dist/` and injects
the Lasm `mount` bootstrap into the editor page. Open
`http://127.0.0.1:8000/?room=demo` in two tabs to collaborate.

The production editor is mounted as the Lasm root. A browser `beforeinput` event
reaches a Lean handler synchronously: Lean constructs and validates the edit,
updates `ClientState`, and Lasm patches the editor DOM in the same browser task.
The JavaScript adapter only samples DOM selection and clipboard/IME data before
the event reaches Lasm. It does not maintain an optimistic document or construct
operations. Network submission remains asynchronous; server operation-log
entries and acknowledgements return to Lean through ports.

## Standalone Lean/WASM exercise

`BrowserMain.lean` is a separate deterministic UI exercise:

```sh
npm install
npm run wasm:dev
```

It demonstrates local editing and a deterministic collaboration replay. It
is not a network session.

## Request and consistency model

- Each browser tab has a client ID and sends a unique request ID per submitted
  batch.
- Lean builds operations from DOM-derived ranges and text, validates them
  against its optimistic document, and stores them in a pending queue.
- The browser sends the pending Lean operation batch with its confirmed base
  revision. The server validates it against that historical snapshot and
  transforms it over intervening accepted edits.
- The server returns the accepted transformed batch and the intervening log
  entries. The client passes those entries to Lean, which rebases all pending
  local operations and verifies that the accepted batch is exactly the pending
  prefix before retiring it.
- Local edits arriving while a request is in flight remain in Lean's pending
  queue. After acknowledgement, the next request uses the rebased remainder.
- Polling is revision-scoped. Remote batches are applied and transformed by
  Lean before the document snapshot is rendered.

The server serializes room mutations into one monotonically increasing
revision sequence. Its Python adapter is transport and room routing only.

## Current demo boundaries

Rooms, the revision log, and request de-duplication live in memory and are
lost on restart. Authentication, authorization, durable persistence, TLS,
presence, and remote cursors are not implemented. Room names are identifiers,
not access controls. Do not expose the demo server to the public internet.
CI tests the native Lean server, browser UI fallback, operation-batch
submission, browser/WASM compilation, generated asset serving, and the direct
DOM-event-to-Lean transition including same-task rendering.
