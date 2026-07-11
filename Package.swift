// swift-tools-version: 5.9

import Foundation
import PackageDescription

let packageDirectory = URL(fileURLWithPath: #filePath).deletingLastPathComponent()
let localXCFrameworkPath = packageDirectory.appendingPathComponent("talk-swift/Artifacts/TalkC.xcframework").path
let localDebugArchivePath = packageDirectory.appendingPathComponent("target/debug/libtalk_c.a").path
let localReleaseArchivePath = packageDirectory.appendingPathComponent("target/release/libtalk_c.a").path
let hasLocalXCFramework = FileManager.default.fileExists(atPath: localXCFrameworkPath)
let hasLocalArchive = FileManager.default.fileExists(atPath: localDebugArchivePath)
    || FileManager.default.fileExists(atPath: localReleaseArchivePath)

// The TalkSwift release workflow rewrites these constants on version tags.
let talkCReleaseURL = "https://github.com/nakajima/talk/releases/download/v0.1.52-swift/TalkC.xcframework.zip"
let talkCReleaseChecksum = "ce9556c19c3e6890915b9c5fd6acd9719118f74c84fbe966c37faf737d41bb79"

let cTarget: Target
if hasLocalXCFramework {
    cTarget = .binaryTarget(
        name: "CTalkC",
        path: "talk-swift/Artifacts/TalkC.xcframework"
    )
} else if hasLocalArchive {
    cTarget = .systemLibrary(
        name: "CTalkC",
        path: "talk-swift/Sources/CTalkC"
    )
} else {
    cTarget = .binaryTarget(
        name: "CTalkC",
        url: talkCReleaseURL,
        checksum: talkCReleaseChecksum
    )
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
            dependencies: ["CTalkC"],
            path: "talk-swift/Sources/TalkSwift"
        ),
        .testTarget(
            name: "TalkSwiftTests",
            dependencies: ["TalkSwift"],
            path: "talk-swift/Tests/TalkSwiftTests"
        ),
    ]
)
