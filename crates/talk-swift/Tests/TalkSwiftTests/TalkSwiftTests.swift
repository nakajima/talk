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

    func testRunProgram() throws {
        let result = try Talk.runProgram(source: "print(40 + 2)\n")
        XCTAssertEqual(result, .output(stdout: "42\n", stderr: "", value: nil))
    }

    func testPackageCreateInstallAndRun() throws {
        let directory = FileManager.default.temporaryDirectory
            .appendingPathComponent("talk-swift-package-\(UUID().uuidString)", isDirectory: true)
        defer { try? FileManager.default.removeItem(at: directory) }

        final class TarProvider: PackageSourceProvider {
            func fetchTar(_ request: PackageTarRequest) throws -> Data {
                XCTFail("the starter package has no remote dependencies")
                return Data()
            }
        }

        try TalkPackage.create(at: directory, name: "sample")
        try TalkPackage.install(at: directory, provider: TarProvider(), offline: true)

        let result = try TalkPackage.run(at: directory, offline: true)
        XCTAssertEqual(result, .output(stdout: "Hello, Talk!\n", stderr: "", value: nil))

        // The starter package ships one passing test suite.
        let tests = try TalkPackage.test(at: directory, offline: true)
        guard case .finished(let output, let failures) = tests else {
            return XCTFail("expected a finished test run, got \(tests)")
        }
        XCTAssertEqual(failures, 0)
        XCTAssertTrue(output.contains("1 tests passed"), output)
    }
}
