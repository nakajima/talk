import CTalkC
import Foundation

public enum TalkError: Error, LocalizedError, Equatable {
    case invalidInput(String)
    case failed(String)
    case panic(String)
    case unknownStatus(Int32, String)
    case nullHandle(String)

    public var errorDescription: String? {
        switch self {
        case .invalidInput(let message),
             .failed(let message),
             .panic(let message),
             .unknownStatus(_, let message),
             .nullHandle(let message):
            message
        }
    }
}

public struct TextRange: Equatable, Sendable {
    public var start: UInt32
    public var end: UInt32

    public init(start: UInt32, end: UInt32) {
        self.start = start
        self.end = end
    }
}

public enum DiagnosticSeverity: Int32, Sendable {
    case error = 1
    case warning = 2
    case info = 3
}

public struct Diagnostic: Equatable, Sendable {
    public var document: String
    public var range: TextRange
    public var severity: DiagnosticSeverity
    public var message: String
}

public enum CompletionKind: Int32, Sendable {
    case none = 0
    case `struct` = 1
    case `enum` = 2
    case interface = 3
    case `class` = 4
    case typeParameter = 5
    case variable = 6
    case field = 7
    case method = 8
    case constructor = 9
    case enumMember = 10
    case keyword = 11
    case module = 12
    case effect = 13
}

public struct Completion: Equatable, Sendable {
    public var label: String
    public var kind: CompletionKind
    public var detail: String?
    public var insertText: String?
    public var insertTextIsSnippet: Bool
}

public enum OwnershipInlayHintKind: Int32, Sendable {
    case move = 1
    case borrow = 2
    case drop = 3
    case clone = 4
}

public struct OwnershipInlayHint: Equatable, Sendable {
    public var position: UInt32
    public var label: String
    public var tooltip: String
    public var kind: OwnershipInlayHintKind
}

public enum HighlightKind: Int32, Sendable {
    case decorator = 1
    case namespace = 2
    case type = 3
    case `class` = 4
    case `enum` = 5
    case interface = 6
    case `struct` = 7
    case typeParameter = 8
    case parameter = 9
    case variable = 10
    case property = 11
    case enumMember = 12
    case event = 13
    case function = 14
    case method = 15
    case macro = 16
    case keyword = 17
    case modifier = 18
    case comment = 19
    case string = 20
    case number = 21
    case regexp = 22
    case `operator` = 23
    case effect = 24
}

public struct HighlightToken: Equatable, Sendable {
    public var kind: HighlightKind
    public var range: TextRange
}

public struct Location: Equatable, Sendable {
    public var document: String
    public var range: TextRange
}

public struct Hover: Equatable, Sendable {
    public var contents: String
    public var range: TextRange
}

public struct TextEdit: Equatable, Sendable {
    public var range: TextRange
    public var replacement: String
}

public struct DocumentEdit: Equatable, Sendable {
    public var document: String
    public var edits: [TextEdit]
}

public struct WorkspaceEdit: Equatable, Sendable {
    public var documents: [DocumentEdit]
}

public enum EvaluationResult: Equatable, Sendable {
    case output(stdout: String, stderr: String, value: String?)
    case diagnostics(source: String, message: String?, diagnostics: [Diagnostic])
    case error(message: String?)
}

public struct ReplCompletion: Equatable, Sendable {
    public var display: String
    public var replacement: String
}

public struct ReplCompletions: Equatable, Sendable {
    public var start: Int
    public var items: [ReplCompletion]
}

public enum Talk {
    public static func version() throws -> String {
        try stringResult(talk_version_utf8())
    }

    public static func format(_ source: String) throws -> String {
        try withBytes(source) { sourcePointer, sourceLength in
            try stringResult(talk_format_utf8(sourcePointer, sourceLength))
        }
    }

    public static func highlightHTML(_ source: String) throws -> String {
        try withBytes(source) { sourcePointer, sourceLength in
            try stringResult(talk_highlight_html_utf8(sourcePointer, sourceLength))
        }
    }

    public static func highlightTokens(_ source: String) throws -> [HighlightToken] {
        try withBytes(source) { sourcePointer, sourceLength in
            let handle = try requireHandle(
                talk_highlight_tokens_utf8(sourcePointer, sourceLength),
                name: "highlight tokens"
            )
            defer { talk_highlight_tokens_free(handle) }
            try checkStatus(
                talk_highlight_tokens_status(handle),
                error: talk_highlight_tokens_error(handle)
            )
            return readHighlightTokens(handle)
        }
    }

    public static func check(path: String = "<stdin>", source: String) throws -> [Diagnostic] {
        try withBytes(path) { pathPointer, pathLength in
            try withBytes(source) { sourcePointer, sourceLength in
                let handle = try requireHandle(
                    talk_check_utf8(pathPointer, pathLength, sourcePointer, sourceLength),
                    name: "diagnostics"
                )
                defer { talk_diagnostics_free(handle) }
                try checkStatus(talk_diagnostics_status(handle), error: talk_diagnostics_error(handle))
                return readDiagnostics(handle)
            }
        }
    }

    public static func runProgram(path: String = "<stdin>", source: String) throws -> EvaluationResult {
        try withBytes(path) { pathPointer, pathLength in
            try withBytes(source) { sourcePointer, sourceLength in
                let handle = try requireHandle(
                    talk_run_program_utf8(pathPointer, pathLength, sourcePointer, sourceLength),
                    name: "evaluation result"
                )
                defer { talk_eval_result_free(handle) }
                return try readEvaluationResult(handle)
            }
        }
    }

    public static func renderLowered(path: String = "<stdin>", source: String) throws -> String {
        try withBytes(path) { pathPointer, pathLength in
            try withBytes(source) { sourcePointer, sourceLength in
                try stringResult(talk_render_lowered_utf8(pathPointer, pathLength, sourcePointer, sourceLength))
            }
        }
    }

    public static func renderBytecode(path: String = "<stdin>", source: String) throws -> String {
        try withBytes(path) { pathPointer, pathLength in
            try withBytes(source) { sourcePointer, sourceLength in
                try stringResult(talk_render_bytecode_utf8(pathPointer, pathLength, sourcePointer, sourceLength))
            }
        }
    }

    public static func compileBytecode(path: String = "<stdin>", source: String) throws -> Data {
        try withBytes(path) { pathPointer, pathLength in
            try withBytes(source) { sourcePointer, sourceLength in
                try dataResult(talk_compile_bytecode_utf8(pathPointer, pathLength, sourcePointer, sourceLength))
            }
        }
    }
}

public final class Workspace {
    private let handle: OpaquePointer

    public init() throws {
        guard let handle = talk_workspace_new() else {
            throw TalkError.nullHandle("talk-c returned a null workspace handle")
        }
        self.handle = handle
    }

    deinit {
        talk_workspace_free(handle)
    }

    public func clear() throws {
        try emptyResult(talk_workspace_clear(handle))
    }

    public func setDocument(id: String, path: String, version: Int32, text: String) throws {
        try withBytes(id) { idPointer, idLength in
            try withBytes(path) { pathPointer, pathLength in
                try withBytes(text) { textPointer, textLength in
                    try emptyResult(
                        talk_workspace_set_document_utf8(
                            handle,
                            idPointer,
                            idLength,
                            pathPointer,
                            pathLength,
                            version,
                            textPointer,
                            textLength
                        )
                    )
                }
            }
        }
    }

    public func removeDocument(id: String) throws {
        try withBytes(id) { idPointer, idLength in
            try emptyResult(talk_workspace_remove_document_utf8(handle, idPointer, idLength))
        }
    }

    public func analyze() throws -> [Diagnostic] {
        let diagnostics = try requireHandle(talk_workspace_analyze(handle), name: "diagnostics")
        defer { talk_diagnostics_free(diagnostics) }
        try checkStatus(talk_diagnostics_status(diagnostics), error: talk_diagnostics_error(diagnostics))
        return readDiagnostics(diagnostics)
    }

    public func diagnostics() throws -> [Diagnostic] {
        let diagnostics = try requireHandle(talk_workspace_diagnostics(handle), name: "diagnostics")
        defer { talk_diagnostics_free(diagnostics) }
        try checkStatus(talk_diagnostics_status(diagnostics), error: talk_diagnostics_error(diagnostics))
        return readDiagnostics(diagnostics)
    }

    public func diagnostics(document id: String) throws -> [Diagnostic] {
        try withBytes(id) { idPointer, idLength in
            let diagnostics = try requireHandle(
                talk_workspace_document_diagnostics_utf8(handle, idPointer, idLength),
                name: "diagnostics"
            )
            defer { talk_diagnostics_free(diagnostics) }
            try checkStatus(talk_diagnostics_status(diagnostics), error: talk_diagnostics_error(diagnostics))
            return readDiagnostics(diagnostics)
        }
    }

    public func hover(document id: String, byteOffset: UInt32) throws -> Hover? {
        try withBytes(id) { idPointer, idLength in
            let hover = try requireHandle(
                talk_workspace_hover_utf8(handle, idPointer, idLength, byteOffset),
                name: "hover"
            )
            defer { talk_hover_free(hover) }
            try checkStatus(talk_hover_status(hover), error: talk_hover_error(hover))
            let value = talk_hover_value(hover)
            guard value.present != 0 else { return nil }
            return Hover(
                contents: string(value.contents),
                range: range(value.range)
            )
        }
    }

    public func completions(document id: String, byteOffset: UInt32) throws -> [Completion] {
        try withBytes(id) { idPointer, idLength in
            let completions = try requireHandle(
                talk_workspace_completions_utf8(handle, idPointer, idLength, byteOffset),
                name: "completions"
            )
            defer { talk_completions_free(completions) }
            try checkStatus(talk_completions_status(completions), error: talk_completions_error(completions))
            return readCompletions(completions)
        }
    }

    public func inlayHints(document id: String, range: TextRange) throws -> [OwnershipInlayHint] {
        try withBytes(id) { idPointer, idLength in
            let hints = try requireHandle(
                talk_workspace_inlay_hints_utf8(handle, idPointer, idLength, range.start, range.end),
                name: "inlay hints"
            )
            defer { talk_inlay_hints_free(hints) }
            try checkStatus(talk_inlay_hints_status(hints), error: talk_inlay_hints_error(hints))
            return readInlayHints(hints)
        }
    }

    public func gotoDefinition(document id: String, byteOffset: UInt32) throws -> Location? {
        try withBytes(id) { idPointer, idLength in
            let location = try requireHandle(
                talk_workspace_goto_definition_utf8(handle, idPointer, idLength, byteOffset),
                name: "location"
            )
            defer { talk_location_free(location) }
            try checkStatus(talk_location_status(location), error: talk_location_error(location))
            let value = talk_location_value(location)
            guard value.present != 0 else { return nil }
            return Location(document: string(value.document), range: range(value.range))
        }
    }

    public func rename(document id: String, byteOffset: UInt32, newName: String) throws -> WorkspaceEdit? {
        try withBytes(id) { idPointer, idLength in
            try withBytes(newName) { newNamePointer, newNameLength in
                let edit = try requireHandle(
                    talk_workspace_rename_utf8(
                        handle,
                        idPointer,
                        idLength,
                        byteOffset,
                        newNamePointer,
                        newNameLength
                    ),
                    name: "workspace edit"
                )
                defer { talk_workspace_edit_free(edit) }
                try checkStatus(talk_workspace_edit_status(edit), error: talk_workspace_edit_error(edit))
                return readWorkspaceEdit(edit)
            }
        }
    }
}

public final class ReplSession {
    private let handle: OpaquePointer

    public init() throws {
        guard let handle = talk_repl_new() else {
            throw TalkError.nullHandle("talk-c returned a null REPL handle")
        }
        self.handle = handle
    }

    deinit {
        talk_repl_free(handle)
    }

    public func reset() throws {
        try emptyResult(talk_repl_reset(handle))
    }

    public func eval(_ input: String) throws -> EvaluationResult {
        try withBytes(input) { inputPointer, inputLength in
            let result = try requireHandle(
                talk_repl_eval_utf8(handle, inputPointer, inputLength),
                name: "evaluation result"
            )
            defer { talk_eval_result_free(result) }
            return try readEvaluationResult(result)
        }
    }

    public func typeOf(_ input: String) throws -> EvaluationResult {
        try withBytes(input) { inputPointer, inputLength in
            let result = try requireHandle(
                talk_repl_type_of_utf8(handle, inputPointer, inputLength),
                name: "evaluation result"
            )
            defer { talk_eval_result_free(result) }
            return try readEvaluationResult(result)
        }
    }

    public func completions(for input: String, byteOffset: Int) throws -> ReplCompletions {
        try withBytes(input) { inputPointer, inputLength in
            let completions = try requireHandle(
                talk_repl_complete_utf8(handle, inputPointer, inputLength, byteOffset),
                name: "REPL completions"
            )
            defer { talk_repl_completions_free(completions) }
            try checkStatus(
                talk_repl_completions_status(completions),
                error: talk_repl_completions_error(completions)
            )
            return readReplCompletions(completions)
        }
    }

    public static func needsMoreInput(_ input: String) -> Bool {
        withBytes(input) { inputPointer, inputLength in
            talk_repl_needs_more_input_utf8(inputPointer, inputLength)
        }
    }
}

private func withBytes<R>(_ value: String, _ body: (UnsafePointer<UInt8>?, Int) throws -> R) rethrows -> R {
    let bytes = Array(value.utf8)
    return try bytes.withUnsafeBufferPointer { buffer in
        try body(buffer.baseAddress, buffer.count)
    }
}

private func requireHandle(_ handle: OpaquePointer?, name: String) throws -> OpaquePointer {
    guard let handle else {
        throw TalkError.nullHandle("talk-c returned a null \(name) handle")
    }
    return handle
}

private func string(_ ref: TalkStringRef) -> String {
    guard let pointer = ref.ptr, ref.len > 0 else {
        return ""
    }
    let buffer = UnsafeBufferPointer(start: pointer, count: Int(ref.len))
    return String(decoding: buffer, as: UTF8.self)
}

private func optionalString(_ ref: TalkOptionalStringRef) -> String? {
    ref.present == 0 ? nil : string(ref.value)
}

private func data(_ buffer: TalkBuffer) -> Data {
    guard let pointer = buffer.ptr, buffer.len > 0 else {
        return Data()
    }
    return Data(bytes: pointer, count: Int(buffer.len))
}

private func stringResult(_ result: TalkResult) throws -> String {
    defer { talk_result_free(result) }
    try checkStatus(result.status, error: result.error)
    return String(decoding: data(result.data), as: UTF8.self)
}

private func dataResult(_ result: TalkResult) throws -> Data {
    defer { talk_result_free(result) }
    try checkStatus(result.status, error: result.error)
    return data(result.data)
}

private func emptyResult(_ result: TalkResult) throws {
    defer { talk_result_free(result) }
    try checkStatus(result.status, error: result.error)
}

private func checkStatus(_ status: Int32, error: TalkStringRef) throws {
    guard status == TALK_STATUS_OK else {
        throw talkError(status: status, message: string(error))
    }
}

private func checkStatus(_ status: Int32, error: TalkBuffer) throws {
    guard status == TALK_STATUS_OK else {
        throw talkError(status: status, message: String(decoding: data(error), as: UTF8.self))
    }
}

private func talkError(status: Int32, message: String) -> TalkError {
    switch status {
    case Int32(TALK_STATUS_INVALID_INPUT):
        .invalidInput(message)
    case Int32(TALK_STATUS_FAILED):
        .failed(message)
    case Int32(TALK_STATUS_PANIC):
        .panic(message)
    default:
        .unknownStatus(status, message)
    }
}

private func range(_ value: TalkTextRange) -> TextRange {
    TextRange(start: value.start, end: value.end)
}

private func readDiagnostics(_ handle: OpaquePointer) -> [Diagnostic] {
    let count = talk_diagnostics_count(handle)
    return (0..<count).map { index in
        diagnostic(talk_diagnostics_get(handle, index))
    }
}

private func diagnostic(_ view: TalkDiagnosticView) -> Diagnostic {
    Diagnostic(
        document: string(view.document),
        range: range(view.range),
        severity: DiagnosticSeverity(rawValue: view.severity) ?? .error,
        message: string(view.message)
    )
}

private func readCompletions(_ handle: OpaquePointer) -> [Completion] {
    let count = talk_completions_count(handle)
    return (0..<count).map { index in
        let view = talk_completions_get(handle, index)
        return Completion(
            label: string(view.label),
            kind: CompletionKind(rawValue: view.kind) ?? .none,
            detail: optionalString(view.detail),
            insertText: optionalString(view.insert_text),
            insertTextIsSnippet: view.insert_text_is_snippet != 0
        )
    }
}

private func readInlayHints(_ handle: OpaquePointer) -> [OwnershipInlayHint] {
    let count = talk_inlay_hints_count(handle)
    return (0..<count).map { index in
        let view = talk_inlay_hints_get(handle, index)
        return OwnershipInlayHint(
            position: view.position,
            label: string(view.label),
            tooltip: string(view.tooltip),
            kind: OwnershipInlayHintKind(rawValue: view.kind) ?? .move
        )
    }
}

private func readHighlightTokens(_ handle: OpaquePointer) -> [HighlightToken] {
    let count = talk_highlight_tokens_count(handle)
    return (0..<count).map { index in
        let view = talk_highlight_tokens_get(handle, index)
        return HighlightToken(
            kind: HighlightKind(rawValue: view.kind) ?? .variable,
            range: TextRange(start: view.start, end: view.end)
        )
    }
}

private func readWorkspaceEdit(_ handle: OpaquePointer) -> WorkspaceEdit? {
    let documentCount = talk_workspace_edit_document_count(handle)
    guard documentCount > 0 else {
        return nil
    }
    let documents = (0..<documentCount).map { documentIndex in
        let document = talk_workspace_edit_document(handle, documentIndex)
        let edits = (0..<document.edit_count).map { editIndex in
            let edit = talk_workspace_edit_text_edit(handle, documentIndex, editIndex)
            return TextEdit(range: range(edit.range), replacement: string(edit.replacement))
        }
        return DocumentEdit(document: string(document.document), edits: edits)
    }
    return WorkspaceEdit(documents: documents)
}

private func readEvaluationResult(_ handle: OpaquePointer) throws -> EvaluationResult {
    try checkStatus(talk_eval_result_status(handle), error: talk_eval_result_error(handle))
    switch talk_eval_result_kind(handle) {
    case Int32(TALK_EVAL_OUTPUT):
        return .output(
            stdout: string(talk_eval_result_stdout(handle)),
            stderr: string(talk_eval_result_stderr(handle)),
            value: optionalString(talk_eval_result_value(handle))
        )
    case Int32(TALK_EVAL_DIAGNOSTICS):
        let count = talk_eval_result_diagnostic_count(handle)
        let diagnostics = (0..<count).map { index in
            diagnostic(talk_eval_result_diagnostic(handle, index))
        }
        return .diagnostics(
            source: string(talk_eval_result_source(handle)),
            message: optionalString(talk_eval_result_message(handle)),
            diagnostics: diagnostics
        )
    case Int32(TALK_EVAL_ERROR):
        return .error(message: optionalString(talk_eval_result_message(handle)))
    default:
        return .error(message: "unknown evaluation result kind")
    }
}

private func readReplCompletions(_ handle: OpaquePointer) -> ReplCompletions {
    let count = talk_repl_completions_count(handle)
    let items = (0..<count).map { index in
        let view = talk_repl_completions_get(handle, index)
        return ReplCompletion(display: string(view.display), replacement: string(view.replacement))
    }
    return ReplCompletions(start: talk_repl_completions_start(handle), items: items)
}
