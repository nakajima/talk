#!/usr/bin/env bash
# Threads-WASM validation harness (ADR 0058/0059): runs the parallel
# corpus in headless Chrome on Web-Worker threads over shared wasm
# memory (wasm/tests/parallel.rs), against the native backends' pins.
#
# The flags live here, not in .cargo/config.toml, on purpose: the
# playground build from this directory must stay single-threaded (its
# hosting has no COOP/COEP headers, so SharedArrayBuffer is absent and
# a shared-memory module would fail to instantiate).
#
# Requires: nightly rustc + rust-src, wasm-pack, and a Chrome/Chromium
# with a version-matched chromedriver. CHROMEDRIVER overrides driver
# discovery; with nix, a matching driver is one command away:
#   nix build nixpkgs#chromedriver --no-link --print-out-paths
set -euo pipefail
cd "$(dirname "$0")"

# rustc adds the wasm shared-memory link flags for cdylibs only; test
# binaries need every one spelled out, plus the TLS entry points
# wasm-bindgen's threading transform patches (the linker GCs them
# unless exported).
export RUSTFLAGS="-C target-feature=+atomics,+bulk-memory,+mutable-globals \
-C link-arg=--shared-memory \
-C link-arg=--import-memory \
-C link-arg=--export-memory \
-C link-arg=--max-memory=1073741824 \
-C link-arg=--export=__wasm_init_tls \
-C link-arg=--export=__tls_size \
-C link-arg=--export=__tls_align \
-C link-arg=--export=__tls_base"
# Threads need std built with atomics.
export CARGO_UNSTABLE_BUILD_STD="std,panic_abort"
# The workspace release profile strips symbols, which would also strip
# the custom section the test runner reads to pick its harness.
export CARGO_PROFILE_RELEASE_STRIP=false
export WASM_BINDGEN_TEST_TIMEOUT="${WASM_BINDGEN_TEST_TIMEOUT:-180}"

driver_args=()
if [[ -n "${CHROMEDRIVER:-}" ]]; then
    driver_args=(--chromedriver "$CHROMEDRIVER")
fi

# chromedriver only auto-discovers `google-chrome`; give a bare
# chromium install that name for the duration of the run.
if ! command -v google-chrome > /dev/null && command -v chromium > /dev/null; then
    shim="$(mktemp -d)"
    printf '#!/bin/sh\nexec chromium "$@"\n' > "$shim/google-chrome"
    chmod +x "$shim/google-chrome"
    export PATH="$shim:$PATH"
    trap 'rm -rf "$shim"' EXIT
fi

exec wasm-pack test --headless --chrome "${driver_args[@]}" --release --test parallel "$@"
