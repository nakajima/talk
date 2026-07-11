# TalkSwift

Swift package wrapper around the `talk-c` C ABI facade. The repository root `Package.swift` is the canonical package manifest for both local development and remote SwiftPM consumption.

Version tags produced by the release workflow point the root package at the matching `TalkC.xcframework.zip` asset and checksum on the same GitHub release.

The package has three dependency resolution modes:

1. If `talk-swift/Artifacts/TalkC.xcframework` exists, it consumes the local binary target.
2. Otherwise, if a host `talk-c` archive exists under `target/debug` or `target/release`, it imports `talk-c/include/talk_c.h` and links that archive.
3. Version-tagged packages without local artifacts download the matching XCFramework from the GitHub release.

For local development on the host, run these commands from the repository root:

```sh
cargo build -p talk-c
swift test -Xlinker -L -Xlinker "$PWD/target/debug"
```

To build and test the production XCFramework on macOS:

```sh
./talk-swift/scripts/build-xcframework.sh
swift package reset
swift test
xcodebuild -scheme TalkSwift -destination "generic/platform=iOS Simulator" build
```

The Swift API copies borrowed C strings into Swift values before freeing result handles. Public editor APIs use byte offsets and ranges to match the Rust analysis layer.

`TalkPackage.create(at:name:version:binaryName:)` creates a package directory with a `main` binary, lockfile, and starter test. `TalkPackage.install(at:provider:offline:update:)` installs dependencies, while `TalkPackage.run(at:binaryName:provider:offline:)` and `TalkPackage.test(at:provider:offline:)` run a package from a file URL.

For iOS, implement `PackageSourceProvider` with the `.tar` capability. Its synchronous `fetchTar(_:)` method returns tar or tar.gz bytes downloaded or retrieved from an app-managed cache; Talk verifies the SHA-256 and safely extracts the archive. Git dependencies require the built-in host provider and are unavailable through the Swift tar-only provider. Prefetch archive data asynchronously with `URLSession` before invoking the synchronous package operation.

This package is heavily WIP. The C ABI, Swift names, result shapes, and packaging flow are expected to change.
