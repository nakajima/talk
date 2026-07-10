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

`TalkPackage.create(at:name:version:binaryName:)` creates a package directory with a `main` binary, lockfile, and starter test. `TalkPackage.run(at:binaryName:offline:)` and `TalkPackage.test(at:offline:)` run that package from a file URL. Remote package dependencies still require the host tools used by the package resolver (`git`, or `curl` and `tar`), so iOS apps should use dependency-free or local-path packages.

This package is heavily WIP. The C ABI, Swift names, result shapes, and packaging flow are expected to change.
