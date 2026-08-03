// swift-tools-version: 5.9
// Builds against the talk-ffi static library:
//   cargo build -p talk-ffi --release
//   swift test -Xlinker -L../target/release
import PackageDescription

let package = Package(
    name: "TalkSwift",
    products: [
        .library(name: "TalkSwift", targets: ["TalkSwift"])
    ],
    targets: [
        .systemLibrary(name: "CTalkFFI", path: "Sources/CTalkFFI"),
        .target(name: "TalkSwift", dependencies: ["CTalkFFI"]),
        .testTarget(name: "TalkSwiftTests", dependencies: ["TalkSwift"]),
    ]
)
