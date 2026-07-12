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
let talkCReleaseURL = "https://github.com/nakajima/talk/releases/download/v0.1.61/TalkC.xcframework.zip"
let talkCReleaseChecksum = "c2b9cbb7fd3c5efb6aa9d425a9bf9d4de0b1c85a19b5834854d56b3903d37cb6"

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
