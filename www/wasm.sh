#!/bin/bash
set -euo pipefail

rm -rf assets/pkg/
# The wasm build embeds bootstrap/core.bin.gz; regenerate it so it
# matches the current compiler before wasm-pack bakes it in.
pushd ..
cargo run --release -- core-artifact
popd
pushd ../wasm
npm run build
mv pkg/ ../www/assets/pkg
popd