// swift-tools-version: 5.9

import Foundation
import PackageDescription

let packageDirectory = URL(fileURLWithPath: #filePath).deletingLastPathComponent()
let xcframeworkPath = packageDirectory.appendingPathComponent("Artifacts/TalkC.xcframework").path
let hasLocalXCFramework = FileManager.default.fileExists(atPath: xcframeworkPath)

let cTarget: Target = if hasLocalXCFramework {
    .binaryTarget(name: "CTalkC", path: "Artifacts/TalkC.xcframework")
} else {
    .systemLibrary(name: "CTalkC", path: "Sources/CTalkC")
}

let package = Package(
    name: "TalkSwift",
    platforms: [
        .iOS(.v13),
        .macOS(.v12),
    ],
    products: [
        .library(name: "TalkSwift", targets: ["TalkSwift"]),
    ],
    targets: [
        cTarget,
        .target(
            name: "TalkSwift",
            dependencies: ["CTalkC"]
        ),
        .testTarget(
            name: "TalkSwiftTests",
            dependencies: ["TalkSwift"]
        ),
    ]
)
