import XCTest
@testable import TalkSwift

final class TalkSwiftTests: XCTestCase {
    func testDiagnostics() throws {
        let diagnostics = try Talk.check(path: "test.tlk", source: "let x: Int = true\n")
        XCTAssertFalse(diagnostics.isEmpty)
        XCTAssertEqual(diagnostics.first?.severity, .error)
    }

    func testHighlightTokens() throws {
        let tokens = try Talk.highlightTokens("let x = 1\n")
        XCTAssertFalse(tokens.isEmpty)
    }

    func testPackageCreateRunAndTest() throws {
        let directory = FileManager.default.temporaryDirectory
            .appendingPathComponent("talk-swift-package-\(UUID().uuidString)", isDirectory: true)
        defer { try? FileManager.default.removeItem(at: directory) }

        try TalkPackage.create(at: directory, name: "sample")

        let run = try TalkPackage.run(at: directory, offline: true)
        guard case .output(let stdout, _, _) = run else {
            return XCTFail("expected package output, got \(run)")
        }
        XCTAssertEqual(stdout, "Hello, Talk!\n")

        let result = try TalkPackage.test(at: directory, offline: true)
        guard case .finished(_, let failures) = result else {
            return XCTFail("expected package tests to run")
        }
        XCTAssertEqual(failures, 0)
    }
}
