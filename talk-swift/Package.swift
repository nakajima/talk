// swift-tools-version: 5.9
// Builds against the talk-c static library:
//   cargo build -p talk-c --release
//   swift test -Xlinker -L../target/release
import PackageDescription

let package = Package(
    name: "TalkSwift",
    products: [
        .library(name: "TalkSwift", targets: ["TalkSwift"])
    ],
    targets: [
        .systemLibrary(name: "CTalkC", path: "Sources/CTalkC"),
        .target(name: "TalkSwift", dependencies: ["CTalkC"]),
        .testTarget(name: "TalkSwiftTests", dependencies: ["TalkSwift"]),
    ]
)
