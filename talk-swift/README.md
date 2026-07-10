# TalkSwift

Swift package wrapper around the local `talk-c` C ABI facade.

For remote SwiftPM/Xcode consumption, use the repository root package from a version tag produced by the `TalkSwift XCFramework release` workflow. That tag's root `Package.swift` points at the matching GitHub Release `TalkC.xcframework.zip` asset and checksum.

This nested package is mainly for local development. It has two modes:

1. If `Artifacts/TalkC.xcframework` exists, `Package.swift` consumes it as a binary target.
2. Otherwise it falls back to a `systemLibrary` target that imports `../talk-c/include/talk_c.h` and links `libtalk_c` from the build/linker search path.

For local development on the host:

```sh
cargo build -p talk-c
cd talk-swift
swift build -Xlinker -L -Xlinker ../target/debug
```

For iOS packaging on macOS:

```sh
cd talk-swift
./scripts/build-xcframework.sh
swift build
```

The Swift API copies borrowed C strings into Swift values before freeing result handles. Public editor APIs use byte offsets/ranges to match the Rust analysis layer.

`TalkPackage.create(at:name:version:binaryName:)` creates a package directory with a `main` binary, lockfile, and starter test. `TalkPackage.install(at:provider:offline:update:)` installs dependencies, while `TalkPackage.run(at:binaryName:provider:offline:)` and `TalkPackage.test(at:provider:offline:)` run a package from a file URL.

For iOS, implement `PackageSourceProvider` with the `.tar` capability. Its synchronous `fetchTar(_:)` method returns tar or tar.gz bytes downloaded or retrieved from an app-managed cache; Talk verifies the SHA-256 and safely extracts the archive. Git dependencies require the built-in host provider and are unavailable through the Swift tar-only provider. Prefetch archive data asynchronously with `URLSession` before invoking the synchronous package operation.

This package is heavily WIP. The C ABI, Swift names, result shapes, and packaging flow are expected to change.
