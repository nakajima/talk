#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
package_dir="$(cd "$script_dir/.." && pwd)"
repo_dir="$(cd "$package_dir/.." && pwd)"

cd "$repo_dir"

rust_targets=(
  aarch64-apple-ios
  aarch64-apple-ios-sim
  x86_64-apple-ios
  aarch64-apple-darwin
  x86_64-apple-darwin
)
rustup target add "${rust_targets[@]}"

for target in "${rust_targets[@]}"; do
  CARGO_PROFILE_RELEASE_DEBUG=false cargo +nightly build \
    -p talk-ffi \
    --release \
    --locked \
    --target "$target"
done

work_dir="$package_dir/.build/TalkFFI.xcframework"
headers_dir="$work_dir/Headers"
rm -rf "$work_dir" "$package_dir/Artifacts/TalkFFI.xcframework"
mkdir -p "$headers_dir" "$package_dir/Artifacts"

cp "$repo_dir/talk-ffi/include/talk_ffi.h" "$headers_dir/talk_ffi.h"
cat > "$headers_dir/module.modulemap" <<'MODULEMAP'
module CTalkFFI {
  umbrella header "talk_ffi.h"
  export *
}
MODULEMAP

lipo -create \
  "$repo_dir/target/aarch64-apple-ios-sim/release/libtalk_ffi.a" \
  "$repo_dir/target/x86_64-apple-ios/release/libtalk_ffi.a" \
  -output "$work_dir/libtalk_ffi-ios-simulator.a"

lipo -create \
  "$repo_dir/target/aarch64-apple-darwin/release/libtalk_ffi.a" \
  "$repo_dir/target/x86_64-apple-darwin/release/libtalk_ffi.a" \
  -output "$work_dir/libtalk_ffi-macos.a"

xcodebuild -create-xcframework \
  -library "$repo_dir/target/aarch64-apple-ios/release/libtalk_ffi.a" \
  -headers "$headers_dir" \
  -library "$work_dir/libtalk_ffi-ios-simulator.a" \
  -headers "$headers_dir" \
  -library "$work_dir/libtalk_ffi-macos.a" \
  -headers "$headers_dir" \
  -output "$package_dir/Artifacts/TalkFFI.xcframework"
