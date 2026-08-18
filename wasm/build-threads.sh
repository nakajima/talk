#!/usr/bin/env bash
set -euo pipefail

export RUSTFLAGS="-C target-feature=+atomics,+bulk-memory,+mutable-globals \
-C link-arg=--shared-memory \
-C link-arg=--import-memory \
-C link-arg=--export-memory \
-C link-arg=--max-memory=1073741824 \
-C link-arg=--export=__wasm_init_tls \
-C link-arg=--export=__tls_size \
-C link-arg=--export=__tls_align \
-C link-arg=--export=__tls_base"
export CARGO_UNSTABLE_BUILD_STD="std,panic_abort"

exec wasm-pack build --release --target web --out-dir pkg
