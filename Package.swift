// swift-tools-version: 5.9

import Foundation
import PackageDescription

let packageDirectory = URL(fileURLWithPath: #filePath).deletingLastPathComponent()
let localXCFrameworkPath = packageDirectory.appendingPathComponent("talk-swift/Artifacts/TalkFFI.xcframework").path
let localDebugArchivePath = packageDirectory.appendingPathComponent("target/debug/libtalk_ffi.a").path
let localReleaseArchivePath = packageDirectory.appendingPathComponent("target/release/libtalk_ffi.a").path
let hasLocalXCFramework = FileManager.default.fileExists(atPath: localXCFrameworkPath)
let hasLocalArchive = FileManager.default.fileExists(atPath: localDebugArchivePath)
    || FileManager.default.fileExists(atPath: localReleaseArchivePath)

// The release workflow rewrites these constants in the tagged release commit.
let talkFFIReleaseURL = "https://github.com/nakajima/talk/releases/download/v0.1.90/TalkFFI.xcframework.zip"
let talkFFIReleaseChecksum = "7cfc0363966d4a275972bf1592175e313b306b480c3bac793d63b4554084f881"

let cTarget: Target
if hasLocalXCFramework {
    cTarget = .binaryTarget(
        name: "CTalkFFI",
        path: "talk-swift/Artifacts/TalkFFI.xcframework"
    )
} else if hasLocalArchive {
    cTarget = .systemLibrary(
        name: "CTalkFFI",
        path: "talk-swift/Sources/CTalkFFI"
    )
} else {
    cTarget = .binaryTarget(
        name: "CTalkFFI",
        url: talkFFIReleaseURL,
        checksum: talkFFIReleaseChecksum
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
            dependencies: ["CTalkFFI"],
            path: "talk-swift/Sources/TalkSwift"
        ),
        .testTarget(
            name: "TalkSwiftTests",
            dependencies: ["TalkSwift"],
            path: "talk-swift/Tests/TalkSwiftTests"
        ),
    ]
)
