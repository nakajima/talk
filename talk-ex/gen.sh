
#! /usr/bin/bash

echo "Generating component"
cargo component build --target wasm32-wasip1 --release --artifact-dir dist/wit -Z unstable-options --verbose
wasm-tools component unbundle target/wasm32-wasip1/release/talk_ex.wasm --module-dir dist/unbundled -o dist/unbundled/talk_ex_core.wasm

mkdir -p ../../talk.swift/talk_ex_core
cp dist/unbundled/* ../../talk.swift/talk_ex_core