pushd ..
cargo build
popd
./wasm.sh
cargo run > ./assets/index.html