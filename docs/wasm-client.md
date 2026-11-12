# Browser OT client

The browser entry point is `BrowserMain.lean`. It imports the shared
`Editor.Core` module and runs the real Lean session, edit builders,
validation, undo, and redo inside the browser-targeted WebAssembly runtime.

## Prerequisites

- Node.js 24 or newer
- npm
- Lasm CLI (`@lasm/cli` 0.7.0)
- Lean 4.35.0, pinned in `lean-toolchain`

## Develop

```sh
npm install
npm run wasm:dev
```

## Production build

```sh
npm run wasm:build
```

## Collaboration core

`Editor/Collaboration.lean` provides a proof-carrying optimistic client state:

- a confirmed server document and revision;
- a pending local operation queue and optimistic document;
- remote operation rebasing using the verified `xformSeq` transformation;
- undo and redo history rebasing, with `ValidChain` proofs maintained;
- acknowledgement of a prefix of the pending queue without losing subsequent local edits.

The remote-receive function expects a server-accepted operation batch expressed
against the client's current confirmed revision. The acknowledgement function
requires the accepted batch to match a prefix of pending operations. This
makes protocol ordering explicit and rejects mismatched acknowledgements.

## Not yet implemented

`Editor/Collaboration/Server.lean` adds a transport-independent, revisioned
server boundary. It accepts edits against historical snapshots, transforms them
over the intervening server log, preserves the server replay-validity proof,
and returns receipts carrying client/request identity and the new revision. A
Lean smoke scenario submits two edits from revision zero and exercises the
server's total ordering.

The server boundary is not yet wired to HTTP/WebSocket transport or the browser
UI. Authentication, request de-duplication, persistence, remote delivery, and
two-browser convergence tests remain. Do not treat this as a production-ready
multi-user editor until those pieces and tests are complete.
