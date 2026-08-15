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

## Threaded-wasm tests

`./test-threads.sh` runs the parallel corpus (ADR 0058/0059) in
headless Chrome on Web-Worker-backed threads over shared wasm memory,
against the same pinned outputs the native backends hold. It needs
nightly Rust with `rust-src`, `wasm-pack`, and a Chrome/Chromium with a
version-matched chromedriver (set `CHROMEDRIVER`, or let wasm-pack
download one; with nix: `nix build nixpkgs#chromedriver --no-link
--print-out-paths`).

The playground build stays single-threaded on purpose: threads need
cross-origin isolation (COOP/COEP response headers) for
`SharedArrayBuffer`, which the playground hosting does not send. The
threading build flags therefore live only in `test-threads.sh`, never
in a `.cargo/config.toml` that would leak into `npm run build`.
