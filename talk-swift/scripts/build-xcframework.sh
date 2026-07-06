#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
package_dir="$(cd "$script_dir/.." && pwd)"
repo_dir="$(cd "$package_dir/.." && pwd)"

cd "$repo_dir"

rustup target add aarch64-apple-ios aarch64-apple-ios-sim x86_64-apple-ios

cargo +nightly build -p talk-c --release --locked --target aarch64-apple-ios
cargo +nightly build -p talk-c --release --locked --target aarch64-apple-ios-sim
cargo +nightly build -p talk-c --release --locked --target x86_64-apple-ios

work_dir="$package_dir/.build/TalkC.xcframework"
headers_dir="$work_dir/Headers"
rm -rf "$work_dir" "$package_dir/Artifacts/TalkC.xcframework"
mkdir -p "$headers_dir" "$package_dir/Artifacts"

cp "$repo_dir/talk-c/include/talk_c.h" "$headers_dir/talk_c.h"
cat > "$headers_dir/module.modulemap" <<'MODULEMAP'
module CTalkC {
  umbrella header "talk_c.h"
  export *
}
MODULEMAP

lipo -create \
  "$repo_dir/target/aarch64-apple-ios-sim/release/libtalk_c.a" \
  "$repo_dir/target/x86_64-apple-ios/release/libtalk_c.a" \
  -output "$work_dir/libtalk_c-ios-simulator.a"

xcodebuild -create-xcframework \
  -library "$repo_dir/target/aarch64-apple-ios/release/libtalk_c.a" \
  -headers "$headers_dir" \
  -library "$work_dir/libtalk_c-ios-simulator.a" \
  -headers "$headers_dir" \
  -output "$package_dir/Artifacts/TalkC.xcframework"
