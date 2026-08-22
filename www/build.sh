#!/bin/bash
set -euo pipefail

pushd ..
cargo build --release
popd
./wasm.sh
TALK_COMPILER=../target/release/talk cargo run -- build