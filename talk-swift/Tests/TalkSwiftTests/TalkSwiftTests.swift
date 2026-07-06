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
}
