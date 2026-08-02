#ifndef TALK_FFI_H
#define TALK_FFI_H

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

/*
 * talk_ffi: language-neutral C ABI for embedding the Talk compiler,
 * bytecode adapter, and VM.
 *
 * Interface version
 * -----------------
 * TALK_FFI_ABI_VERSION identifies this interface, independently of the
 * compiler version returned by talk_version_utf8. It changes only when an
 * exported signature, result layout, ownership rule, or lifetime rule
 * changes. talk_ffi_abi_version() returns the same value at run time.
 *
 * Status and error conventions
 * ----------------------------
 * Functions returning TalkResult report TALK_STATUS_OK,
 * TALK_STATUS_INVALID_INPUT, TALK_STATUS_FAILED, or TALK_STATUS_PANIC in
 * `status`; on non-OK status, `error` holds a UTF-8 message. Functions
 * returning opaque handles report status through the handle's
 * `talk_*_status` and `talk_*_error` accessors.
 *
 * Ownership
 * ---------
 * Every returned value is freed by its matching free function, exactly
 * once:
 *   TalkResult                 -> talk_result_free
 *   TalkBuffer                 -> talk_buffer_free
 *   TalkDiagnostics *          -> talk_diagnostics_free
 *   TalkHover *                -> talk_hover_free
 *   TalkCompletions *          -> talk_completions_free
 *   TalkInlayHints *           -> talk_inlay_hints_free
 *   TalkHighlightTokens *      -> talk_highlight_tokens_free
 *   TalkLocationResult *       -> talk_location_free
 *   TalkWorkspaceEditResult *  -> talk_workspace_edit_free
 *   TalkEvalResult *           -> talk_eval_result_free
 *   TalkTestResult *           -> talk_test_result_free
 *   TalkReplCompletions *      -> talk_repl_completions_free
 *   TalkWorkspace *            -> talk_workspace_free
 *   TalkReplSession *          -> talk_repl_free
 *   TalkPackageProvider *      -> talk_package_provider_free
 * Freeing NULL is allowed. A TalkResult's `data` and `error` buffers are
 * owned by the TalkResult and freed by talk_result_free; do not free them
 * separately.
 *
 * Borrowed data
 * -------------
 * TalkStringRef and view structs (TalkDiagnosticView, TalkHoverView, and
 * the other *View types) borrow from the handle they were read from. They
 * remain valid only until that handle is freed or, for TalkWorkspace and
 * TalkReplSession handles, until the next mutating call on the same
 * handle. Copy anything that must outlive the handle.
 *
 * Callbacks
 * ---------
 * TalkPackageFetchTarCallback is invoked synchronously on the calling
 * thread during a package operation and must finish or fail the supplied
 * TalkPackageArchiveSink before returning. The callback's `context`,
 * `url`, and `sha256` arguments are valid only for the duration of the
 * call.
 *
 * Threading
 * ---------
 * Distinct handles may be used on distinct threads. One handle (and the
 * views borrowed from it) is confined to one thread at a time; handles
 * carry no internal synchronization.
 *
 * Strings
 * -------
 * All input strings are UTF-8; functions are named `_utf8` accordingly.
 * Invalid UTF-8 yields TALK_STATUS_INVALID_INPUT.
 *
 * Panics
 * ------
 * Rust panics are contained at every exported entry point and surface as
 * TALK_STATUS_PANIC; no unwind crosses the C boundary.
 */

#define TALK_FFI_ABI_VERSION 1

#ifdef __cplusplus
extern "C" {
#endif

enum {
    TALK_STATUS_OK = 0,
    TALK_STATUS_INVALID_INPUT = 1,
    TALK_STATUS_FAILED = 2,
    TALK_STATUS_PANIC = 3
};

enum {
    TALK_DIAGNOSTIC_ERROR = 1,
    TALK_DIAGNOSTIC_WARNING = 2,
    TALK_DIAGNOSTIC_INFO = 3
};

enum {
    TALK_COMPLETION_NONE = 0,
    TALK_COMPLETION_STRUCT = 1,
    TALK_COMPLETION_ENUM = 2,
    TALK_COMPLETION_INTERFACE = 3,
    TALK_COMPLETION_CLASS = 4,
    TALK_COMPLETION_TYPE_PARAMETER = 5,
    TALK_COMPLETION_VARIABLE = 6,
    TALK_COMPLETION_FIELD = 7,
    TALK_COMPLETION_METHOD = 8,
    TALK_COMPLETION_CONSTRUCTOR = 9,
    TALK_COMPLETION_ENUM_MEMBER = 10,
    TALK_COMPLETION_KEYWORD = 11,
    TALK_COMPLETION_MODULE = 12,
    TALK_COMPLETION_EFFECT = 13
};

enum {
    TALK_INLAY_MOVE = 1,
    TALK_INLAY_BORROW = 2,
    TALK_INLAY_DROP = 3,
    TALK_INLAY_CLONE = 4
};

enum {
    TALK_EVAL_OUTPUT = 1,
    TALK_EVAL_DIAGNOSTICS = 2,
    TALK_EVAL_ERROR = 3
};

enum {
    TALK_TEST_NO_TESTS = 1,
    TALK_TEST_FINISHED = 2
};

enum {
    TALK_PACKAGE_SOURCE_TAR = 1
};

enum {
    TALK_HIGHLIGHT_DECORATOR = 1,
    TALK_HIGHLIGHT_NAMESPACE = 2,
    TALK_HIGHLIGHT_TYPE = 3,
    TALK_HIGHLIGHT_CLASS = 4,
    TALK_HIGHLIGHT_ENUM = 5,
    TALK_HIGHLIGHT_INTERFACE = 6,
    TALK_HIGHLIGHT_STRUCT = 7,
    TALK_HIGHLIGHT_TYPE_PARAMETER = 8,
    TALK_HIGHLIGHT_PARAMETER = 9,
    TALK_HIGHLIGHT_VARIABLE = 10,
    TALK_HIGHLIGHT_PROPERTY = 11,
    TALK_HIGHLIGHT_ENUM_MEMBER = 12,
    TALK_HIGHLIGHT_EVENT = 13,
    TALK_HIGHLIGHT_FUNCTION = 14,
    TALK_HIGHLIGHT_METHOD = 15,
    TALK_HIGHLIGHT_MACRO = 16,
    TALK_HIGHLIGHT_KEYWORD = 17,
    TALK_HIGHLIGHT_MODIFIER = 18,
    TALK_HIGHLIGHT_COMMENT = 19,
    TALK_HIGHLIGHT_STRING = 20,
    TALK_HIGHLIGHT_NUMBER = 21,
    TALK_HIGHLIGHT_REGEXP = 22,
    TALK_HIGHLIGHT_OPERATOR = 23,
    TALK_HIGHLIGHT_EFFECT = 24
};

typedef struct TalkStringRef {
    const uint8_t *ptr;
    size_t len;
} TalkStringRef;

typedef struct TalkOptionalStringRef {
    int32_t present;
    TalkStringRef value;
} TalkOptionalStringRef;

typedef struct TalkBuffer {
    uint8_t *ptr;
    size_t len;
} TalkBuffer;

typedef struct TalkResult {
    int32_t status;
    TalkBuffer data;
    TalkBuffer error;
} TalkResult;

typedef struct TalkTextRange {
    uint32_t start;
    uint32_t end;
} TalkTextRange;

typedef struct TalkDiagnosticView {
    TalkStringRef document;
    TalkTextRange range;
    int32_t severity;
    TalkStringRef message;
} TalkDiagnosticView;

typedef struct TalkHoverView {
    int32_t present;
    TalkStringRef contents;
    TalkTextRange range;
} TalkHoverView;

typedef struct TalkCompletionView {
    TalkStringRef label;
    int32_t kind;
    TalkOptionalStringRef detail;
    TalkOptionalStringRef insert_text;
    int32_t insert_text_is_snippet;
} TalkCompletionView;

typedef struct TalkInlayHintView {
    uint32_t position;
    TalkStringRef label;
    TalkStringRef tooltip;
    int32_t kind;
} TalkInlayHintView;

typedef struct TalkHighlightTokenView {
    int32_t kind;
    uint32_t start;
    uint32_t end;
} TalkHighlightTokenView;

typedef struct TalkLocationView {
    int32_t present;
    TalkStringRef document;
    TalkTextRange range;
} TalkLocationView;

typedef struct TalkDocumentEditView {
    TalkStringRef document;
    size_t edit_count;
} TalkDocumentEditView;

typedef struct TalkTextEditView {
    TalkTextRange range;
    TalkStringRef replacement;
} TalkTextEditView;

typedef struct TalkReplCompletionView {
    TalkStringRef display;
    TalkStringRef replacement;
} TalkReplCompletionView;

typedef struct TalkWorkspace TalkWorkspace;
typedef struct TalkReplSession TalkReplSession;
typedef struct TalkDiagnostics TalkDiagnostics;
typedef struct TalkHover TalkHover;
typedef struct TalkCompletions TalkCompletions;
typedef struct TalkInlayHints TalkInlayHints;
typedef struct TalkHighlightTokens TalkHighlightTokens;
typedef struct TalkLocationResult TalkLocationResult;
typedef struct TalkWorkspaceEditResult TalkWorkspaceEditResult;
typedef struct TalkEvalResult TalkEvalResult;
typedef struct TalkTestResult TalkTestResult;
typedef struct TalkReplCompletions TalkReplCompletions;
typedef struct TalkPackageProvider TalkPackageProvider;
typedef struct TalkPackageArchiveSink TalkPackageArchiveSink;

typedef void (*TalkPackageFetchTarCallback)(
    void *context,
    TalkStringRef url,
    TalkStringRef sha256,
    TalkPackageArchiveSink *sink
);

void talk_result_free(TalkResult result);
void talk_buffer_free(TalkBuffer buffer);

uint32_t talk_ffi_abi_version(void);
TalkResult talk_version_utf8(void);
TalkResult talk_format_utf8(const uint8_t *source_ptr, size_t source_len);
TalkResult talk_highlight_html_utf8(const uint8_t *source_ptr, size_t source_len);

TalkHighlightTokens *talk_highlight_tokens_utf8(
    const uint8_t *source_ptr,
    size_t source_len
);

TalkDiagnostics *talk_check_utf8(
    const uint8_t *path_ptr,
    size_t path_len,
    const uint8_t *source_ptr,
    size_t source_len
);

/* Compile and execute a program through the bytecode backend. The
 * supplied path names the document: relative local imports resolve
 * from it and diagnostics cite it. */
TalkEvalResult *talk_run_program_utf8(
    const uint8_t *path_ptr,
    size_t path_len,
    const uint8_t *source_ptr,
    size_t source_len
);

TalkPackageProvider *talk_package_provider_new(
    int32_t capabilities,
    TalkPackageFetchTarCallback fetch_tar,
    void *context
);
void talk_package_provider_free(TalkPackageProvider *provider);

void talk_package_archive_sink_write(
    TalkPackageArchiveSink *sink,
    const uint8_t *bytes_ptr,
    size_t bytes_len
);
void talk_package_archive_sink_finish(TalkPackageArchiveSink *sink);
void talk_package_archive_sink_fail_utf8(
    TalkPackageArchiveSink *sink,
    const uint8_t *message_ptr,
    size_t message_len
);

TalkResult talk_package_install_utf8(
    const uint8_t *root_ptr,
    size_t root_len,
    bool offline,
    bool update
);

TalkResult talk_package_install_with_provider_utf8(
    const TalkPackageProvider *provider,
    const uint8_t *root_ptr,
    size_t root_len,
    bool offline,
    bool update
);

TalkResult talk_package_create_utf8(
    const uint8_t *root_ptr,
    size_t root_len,
    const uint8_t *name_ptr,
    size_t name_len,
    const uint8_t *version_ptr,
    size_t version_len,
    const uint8_t *binary_name_ptr,
    size_t binary_name_len
);

/* Compile and execute a package binary (with an optional dependency
 * provider below). */
TalkEvalResult *talk_package_run_utf8(
    const uint8_t *root_ptr,
    size_t root_len,
    const uint8_t *binary_name_ptr,
    size_t binary_name_len,
    bool offline
);

TalkEvalResult *talk_package_run_with_provider_utf8(
    const TalkPackageProvider *provider,
    const uint8_t *root_ptr,
    size_t root_len,
    const uint8_t *binary_name_ptr,
    size_t binary_name_len,
    bool offline
);

TalkTestResult *talk_package_test_utf8(
    const uint8_t *root_ptr,
    size_t root_len,
    bool offline
);

TalkTestResult *talk_package_test_with_provider_utf8(
    const TalkPackageProvider *provider,
    const uint8_t *root_ptr,
    size_t root_len,
    bool offline
);

/* Render the middle representation / bytecode compiled from the
 * source (the inspection surfaces behind `talk mir` and
 * `talk bytecode`). */
TalkResult talk_render_lowered_utf8(
    const uint8_t *path_ptr,
    size_t path_len,
    const uint8_t *source_ptr,
    size_t source_len
);

TalkResult talk_render_bytecode_utf8(
    const uint8_t *path_ptr,
    size_t path_len,
    const uint8_t *source_ptr,
    size_t source_len
);

TalkResult talk_compile_bytecode_utf8(
    const uint8_t *path_ptr,
    size_t path_len,
    const uint8_t *source_ptr,
    size_t source_len
);

TalkWorkspace *talk_workspace_new(void);
void talk_workspace_free(TalkWorkspace *workspace);
TalkResult talk_workspace_clear(TalkWorkspace *workspace);

TalkResult talk_workspace_set_document_utf8(
    TalkWorkspace *workspace,
    const uint8_t *id_ptr,
    size_t id_len,
    const uint8_t *path_ptr,
    size_t path_len,
    int32_t version,
    const uint8_t *text_ptr,
    size_t text_len
);

TalkResult talk_workspace_remove_document_utf8(
    TalkWorkspace *workspace,
    const uint8_t *id_ptr,
    size_t id_len
);

TalkDiagnostics *talk_workspace_analyze(TalkWorkspace *workspace);
TalkDiagnostics *talk_workspace_diagnostics(TalkWorkspace *workspace);

TalkDiagnostics *talk_workspace_document_diagnostics_utf8(
    TalkWorkspace *workspace,
    const uint8_t *id_ptr,
    size_t id_len
);

TalkHover *talk_workspace_hover_utf8(
    TalkWorkspace *workspace,
    const uint8_t *id_ptr,
    size_t id_len,
    uint32_t byte_offset
);

TalkCompletions *talk_workspace_completions_utf8(
    TalkWorkspace *workspace,
    const uint8_t *id_ptr,
    size_t id_len,
    uint32_t byte_offset
);

/* Compatibility entry point: ownership analysis is unavailable. */
TalkInlayHints *talk_workspace_inlay_hints_utf8(
    TalkWorkspace *workspace,
    const uint8_t *id_ptr,
    size_t id_len,
    uint32_t start,
    uint32_t end
);

TalkLocationResult *talk_workspace_goto_definition_utf8(
    TalkWorkspace *workspace,
    const uint8_t *id_ptr,
    size_t id_len,
    uint32_t byte_offset
);

TalkWorkspaceEditResult *talk_workspace_rename_utf8(
    TalkWorkspace *workspace,
    const uint8_t *id_ptr,
    size_t id_len,
    uint32_t byte_offset,
    const uint8_t *new_name_ptr,
    size_t new_name_len
);

TalkReplSession *talk_repl_new(void);
void talk_repl_free(TalkReplSession *repl);
TalkResult talk_repl_reset(TalkReplSession *repl);

TalkEvalResult *talk_repl_eval_utf8(
    TalkReplSession *repl,
    const uint8_t *input_ptr,
    size_t input_len
);

TalkEvalResult *talk_repl_type_of_utf8(
    TalkReplSession *repl,
    const uint8_t *input_ptr,
    size_t input_len
);

TalkReplCompletions *talk_repl_complete_utf8(
    TalkReplSession *repl,
    const uint8_t *input_ptr,
    size_t input_len,
    size_t byte_offset
);

bool talk_repl_needs_more_input_utf8(
    const uint8_t *input_ptr,
    size_t input_len
);

int32_t talk_diagnostics_status(const TalkDiagnostics *ptr);
TalkStringRef talk_diagnostics_error(const TalkDiagnostics *ptr);
size_t talk_diagnostics_count(const TalkDiagnostics *ptr);
TalkDiagnosticView talk_diagnostics_get(const TalkDiagnostics *ptr, size_t index);
void talk_diagnostics_free(TalkDiagnostics *ptr);

int32_t talk_hover_status(const TalkHover *ptr);
TalkStringRef talk_hover_error(const TalkHover *ptr);
TalkHoverView talk_hover_value(const TalkHover *ptr);
void talk_hover_free(TalkHover *ptr);

int32_t talk_completions_status(const TalkCompletions *ptr);
TalkStringRef talk_completions_error(const TalkCompletions *ptr);
size_t talk_completions_count(const TalkCompletions *ptr);
TalkCompletionView talk_completions_get(const TalkCompletions *ptr, size_t index);
void talk_completions_free(TalkCompletions *ptr);

int32_t talk_inlay_hints_status(const TalkInlayHints *ptr);
TalkStringRef talk_inlay_hints_error(const TalkInlayHints *ptr);
size_t talk_inlay_hints_count(const TalkInlayHints *ptr);
TalkInlayHintView talk_inlay_hints_get(const TalkInlayHints *ptr, size_t index);
void talk_inlay_hints_free(TalkInlayHints *ptr);

int32_t talk_highlight_tokens_status(const TalkHighlightTokens *ptr);
TalkStringRef talk_highlight_tokens_error(const TalkHighlightTokens *ptr);
size_t talk_highlight_tokens_count(const TalkHighlightTokens *ptr);
TalkHighlightTokenView talk_highlight_tokens_get(
    const TalkHighlightTokens *ptr,
    size_t index
);
void talk_highlight_tokens_free(TalkHighlightTokens *ptr);

int32_t talk_location_status(const TalkLocationResult *ptr);
TalkStringRef talk_location_error(const TalkLocationResult *ptr);
TalkLocationView talk_location_value(const TalkLocationResult *ptr);
void talk_location_free(TalkLocationResult *ptr);

int32_t talk_workspace_edit_status(const TalkWorkspaceEditResult *ptr);
TalkStringRef talk_workspace_edit_error(const TalkWorkspaceEditResult *ptr);
size_t talk_workspace_edit_document_count(const TalkWorkspaceEditResult *ptr);
TalkDocumentEditView talk_workspace_edit_document(
    const TalkWorkspaceEditResult *ptr,
    size_t document_index
);
TalkTextEditView talk_workspace_edit_text_edit(
    const TalkWorkspaceEditResult *ptr,
    size_t document_index,
    size_t edit_index
);
void talk_workspace_edit_free(TalkWorkspaceEditResult *ptr);

int32_t talk_eval_result_status(const TalkEvalResult *ptr);
TalkStringRef talk_eval_result_error(const TalkEvalResult *ptr);
int32_t talk_eval_result_kind(const TalkEvalResult *ptr);
TalkStringRef talk_eval_result_stdout(const TalkEvalResult *ptr);
TalkStringRef talk_eval_result_stderr(const TalkEvalResult *ptr);
TalkOptionalStringRef talk_eval_result_value(const TalkEvalResult *ptr);
TalkStringRef talk_eval_result_source(const TalkEvalResult *ptr);
TalkOptionalStringRef talk_eval_result_message(const TalkEvalResult *ptr);
size_t talk_eval_result_diagnostic_count(const TalkEvalResult *ptr);
TalkDiagnosticView talk_eval_result_diagnostic(const TalkEvalResult *ptr, size_t index);
void talk_eval_result_free(TalkEvalResult *ptr);

int32_t talk_test_result_status(const TalkTestResult *ptr);
TalkStringRef talk_test_result_error(const TalkTestResult *ptr);
int32_t talk_test_result_kind(const TalkTestResult *ptr);
TalkStringRef talk_test_result_output(const TalkTestResult *ptr);
int64_t talk_test_result_failures(const TalkTestResult *ptr);
void talk_test_result_free(TalkTestResult *ptr);

int32_t talk_repl_completions_status(const TalkReplCompletions *ptr);
TalkStringRef talk_repl_completions_error(const TalkReplCompletions *ptr);
size_t talk_repl_completions_start(const TalkReplCompletions *ptr);
size_t talk_repl_completions_count(const TalkReplCompletions *ptr);
TalkReplCompletionView talk_repl_completions_get(
    const TalkReplCompletions *ptr,
    size_t index
);
void talk_repl_completions_free(TalkReplCompletions *ptr);

#ifdef __cplusplus
}
#endif

#endif
