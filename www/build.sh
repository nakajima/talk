#!/bin/bash
set -euo pipefail

pushd ..
cargo build
popd
./wasm.sh
cargo run -- build