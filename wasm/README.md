# talk-wasm

```
npm run build
```

Then:

```js
import { loadTalk } from "./js/index.js";

const talk = await loadTalk();
console.log(await talk.runProgram("1 + 2 + 3") );
```

## Threaded WASM

The production build uses Web Worker-backed threads over shared WASM
memory. It requires nightly Rust with `rust-src`, `wasm-pack`, and a
cross-origin-isolated server that sends these headers on the document and
worker resources. GitHub Pages does not apply the checked-in `_headers`
manifest, so production must serve `www/assets` through the controlled
server rather than the repository's legacy Pages deployment:

```text
Cross-Origin-Opener-Policy: same-origin
Cross-Origin-Embedder-Policy: require-corp
Cross-Origin-Resource-Policy: same-origin
```

`npm run build` invokes `build-threads.sh`, which enables WASM atomics and
shared memory. The playground intentionally has no single-thread fallback;
it refuses to initialize when `crossOriginIsolated` or `SharedArrayBuffer`
is unavailable.

`./test-threads.sh` runs the parallel corpus (ADR 0058/0059) in headless
Chrome against the same pinned outputs as the native backends. It also needs
a version-matched chromedriver (set `CHROMEDRIVER`, or let `wasm-pack`
download one; with nix: `nix build nixpkgs#chromedriver --no-link
--print-out-paths`).
