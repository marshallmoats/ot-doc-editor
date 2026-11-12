# Browser OT client

The browser entry point is `BrowserMain.lean`. It imports the existing
`Main` module and runs the real `Session`, edit builders, validation,
undo, and redo inside the browser-targeted Lean/WebAssembly runtime.

## Prerequisites

- Node.js 24 or newer
- npm
- The Lasm compiler pinned by `package.json` (currently 0.7.0)
- Lean 4.35.0, pinned in `lean-toolchain` and provisioned by Lasm

## Develop

```sh
npm install
npm run wasm:dev
```

Lasm serves the browser build with live reload, normally at
http://127.0.0.1:5173.

## Production build

```sh
npm run wasm:build
```

The static browser application is written to `dist/`. Serve that directory
from any static web host or CDN.

## Current scope

This is the first compilation and execution milestone, not yet the complete
collaborative editor. It intentionally imports `Main` so the browser invokes
the existing Lean implementation instead of duplicating OT logic in
JavaScript. The next refactor should move the session, edit builders, and
protocol-independent document functions into an IO-free `Editor.Core`
module, leaving JSON-lines and process IO in the native server entry point.

After that extraction, add a client state with a confirmed server revision,
optimistic document, and pending local operation queue. Remote operations must
be transformed over pending local operations using `OT.xformSeq`, with the
undo/redo chains transformed and their validity invariants re-established.
Do not enable multi-client editing until those rebase and convergence cases
have property tests.
