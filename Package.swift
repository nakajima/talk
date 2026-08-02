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

// The release workflow rewrites these constants in the tagged release commit.
let talkCReleaseURL = "https://github.com/nakajima/talk/releases/download/v0.1.80/TalkC.xcframework.zip"
let talkCReleaseChecksum = "d6124af35f0d160014bad3de0e53f70b14fce180f15f36556d8f018833545bf3"

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
