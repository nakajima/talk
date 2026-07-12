#![allow(clippy::not_unsafe_ptr_arg_deref)]

use std::any::Any;
use std::ffi::c_void;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::PathBuf;
use std::sync::Arc;

use talk::analysis::{
    CompletionItem, CompletionItemKind, Diagnostic, DiagnosticSeverity, DocumentId, DocumentInput,
    Hover, Location, OwnershipInlayHint, OwnershipInlayHintKind, TextRange, Workspace,
};
use talk::compiling::{
    driver::{Driver, DriverConfig, Source},
    package::{PackageProject, PackageSourceCapabilities, PackageSourceProvider},
};
use talk::repl::{ReplCompletions, ReplEvalResult, ReplSession};

const STATUS_OK: i32 = 0;
const STATUS_INVALID_INPUT: i32 = 1;
const STATUS_FAILED: i32 = 2;
const STATUS_PANIC: i32 = 3;

const OPTIONAL_ABSENT: i32 = 0;
const OPTIONAL_PRESENT: i32 = 1;

const DIAGNOSTIC_ERROR: i32 = 1;
const DIAGNOSTIC_WARNING: i32 = 2;
const DIAGNOSTIC_INFO: i32 = 3;

const COMPLETION_NONE: i32 = 0;
const COMPLETION_STRUCT: i32 = 1;
const COMPLETION_ENUM: i32 = 2;
const COMPLETION_INTERFACE: i32 = 3;
const COMPLETION_CLASS: i32 = 4;
const COMPLETION_TYPE_PARAMETER: i32 = 5;
const COMPLETION_VARIABLE: i32 = 6;
const COMPLETION_FIELD: i32 = 7;
const COMPLETION_METHOD: i32 = 8;
const COMPLETION_CONSTRUCTOR: i32 = 9;
const COMPLETION_ENUM_MEMBER: i32 = 10;
const COMPLETION_KEYWORD: i32 = 11;
const COMPLETION_MODULE: i32 = 12;
const COMPLETION_EFFECT: i32 = 13;

const INLAY_MOVE: i32 = 1;
const INLAY_BORROW: i32 = 2;
const INLAY_DROP: i32 = 3;
const INLAY_CLONE: i32 = 4;

const EVAL_OUTPUT: i32 = 1;
const EVAL_DIAGNOSTICS: i32 = 2;
const EVAL_ERROR: i32 = 3;

const TEST_NO_TESTS: i32 = 1;
const TEST_FINISHED: i32 = 2;

const PACKAGE_SOURCE_TAR: i32 = 1;

const HIGHLIGHT_DECORATOR: i32 = 1;
const HIGHLIGHT_NAMESPACE: i32 = 2;
const HIGHLIGHT_TYPE: i32 = 3;
const HIGHLIGHT_CLASS: i32 = 4;
const HIGHLIGHT_ENUM: i32 = 5;
const HIGHLIGHT_INTERFACE: i32 = 6;
const HIGHLIGHT_STRUCT: i32 = 7;
const HIGHLIGHT_TYPE_PARAMETER: i32 = 8;
const HIGHLIGHT_PARAMETER: i32 = 9;
const HIGHLIGHT_VARIABLE: i32 = 10;
const HIGHLIGHT_PROPERTY: i32 = 11;
const HIGHLIGHT_ENUM_MEMBER: i32 = 12;
const HIGHLIGHT_EVENT: i32 = 13;
const HIGHLIGHT_FUNCTION: i32 = 14;
const HIGHLIGHT_METHOD: i32 = 15;
const HIGHLIGHT_MACRO: i32 = 16;
const HIGHLIGHT_KEYWORD: i32 = 17;
const HIGHLIGHT_MODIFIER: i32 = 18;
const HIGHLIGHT_COMMENT: i32 = 19;
const HIGHLIGHT_STRING: i32 = 20;
const HIGHLIGHT_NUMBER: i32 = 21;
const HIGHLIGHT_REGEXP: i32 = 22;
const HIGHLIGHT_OPERATOR: i32 = 23;
const HIGHLIGHT_EFFECT: i32 = 24;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkStringRef {
    pub ptr: *const u8,
    pub len: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkOptionalStringRef {
    pub present: i32,
    pub value: TalkStringRef,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkBuffer {
    pub ptr: *mut u8,
    pub len: usize,
}

#[repr(C)]
pub struct TalkResult {
    pub status: i32,
    pub data: TalkBuffer,
    pub error: TalkBuffer,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkTextRange {
    pub start: u32,
    pub end: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkDiagnosticView {
    pub document: TalkStringRef,
    pub range: TalkTextRange,
    pub severity: i32,
    pub message: TalkStringRef,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkHoverView {
    pub present: i32,
    pub contents: TalkStringRef,
    pub range: TalkTextRange,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkCompletionView {
    pub label: TalkStringRef,
    pub kind: i32,
    pub detail: TalkOptionalStringRef,
    pub insert_text: TalkOptionalStringRef,
    pub insert_text_is_snippet: i32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkInlayHintView {
    pub position: u32,
    pub label: TalkStringRef,
    pub tooltip: TalkStringRef,
    pub kind: i32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkHighlightTokenView {
    pub kind: i32,
    pub start: u32,
    pub end: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkLocationView {
    pub present: i32,
    pub document: TalkStringRef,
    pub range: TalkTextRange,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkDocumentEditView {
    pub document: TalkStringRef,
    pub edit_count: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkTextEditView {
    pub range: TalkTextRange,
    pub replacement: TalkStringRef,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TalkReplCompletionView {
    pub display: TalkStringRef,
    pub replacement: TalkStringRef,
}

pub struct TalkWorkspace {
    docs: Vec<DocumentInput>,
    workspace: Option<Workspace>,
    core: Option<Workspace>,
    dirty: bool,
}

pub struct TalkReplSession {
    session: ReplSession,
}

pub struct TalkDiagnostics {
    status: HandleStatus,
    items: Vec<DiagnosticRecord>,
}

pub struct TalkHover {
    status: HandleStatus,
    value: Option<HoverRecord>,
}

pub struct TalkCompletions {
    status: HandleStatus,
    items: Vec<CompletionRecord>,
}

pub struct TalkInlayHints {
    status: HandleStatus,
    items: Vec<InlayHintRecord>,
}

pub struct TalkHighlightTokens {
    status: HandleStatus,
    items: Vec<HighlightTokenRecord>,
}

pub struct TalkLocationResult {
    status: HandleStatus,
    value: Option<LocationRecord>,
}

pub struct TalkWorkspaceEditResult {
    status: HandleStatus,
    documents: Vec<DocumentEditRecord>,
}

pub struct TalkEvalResult {
    status: HandleStatus,
    kind: i32,
    stdout: String,
    stderr: String,
    value: Option<String>,
    source: String,
    message: Option<String>,
    diagnostics: Vec<DiagnosticRecord>,
}

pub struct TalkTestResult {
    status: HandleStatus,
    kind: i32,
    output: String,
    failures: i64,
}

pub struct TalkReplCompletions {
    status: HandleStatus,
    start: usize,
    items: Vec<ReplCompletionRecord>,
}

pub struct TalkPackageProvider {
    provider: Arc<CPackageSourceProvider>,
}

pub struct TalkPackageArchiveSink {
    bytes: Vec<u8>,
    error: Option<String>,
    finished: bool,
}

type PackageFetchTarCallback = unsafe extern "C" fn(
    context: *mut c_void,
    url: TalkStringRef,
    sha256: TalkStringRef,
    sink: *mut TalkPackageArchiveSink,
);

struct CPackageSourceProvider {
    fetch_tar: PackageFetchTarCallback,
    context: *mut c_void,
}

struct ApiError {
    status: i32,
    message: String,
}

type ApiResult<T> = Result<T, ApiError>;

#[derive(Default)]
struct HandleStatus {
    status: i32,
    error: String,
}

#[derive(Clone)]
struct DiagnosticRecord {
    document: String,
    range: TextRange,
    severity: i32,
    message: String,
}

struct HoverRecord {
    contents: String,
    range: TextRange,
}

struct CompletionRecord {
    label: String,
    kind: i32,
    detail: Option<String>,
    insert_text: Option<String>,
    insert_text_is_snippet: i32,
}

struct InlayHintRecord {
    position: u32,
    label: String,
    tooltip: String,
    kind: i32,
}

struct HighlightTokenRecord {
    kind: i32,
    start: u32,
    end: u32,
}

struct LocationRecord {
    document: String,
    range: TextRange,
}

struct DocumentEditRecord {
    document: String,
    edits: Vec<TextEditRecord>,
}

struct TextEditRecord {
    range: TextRange,
    replacement: String,
}

struct ReplCompletionRecord {
    display: String,
    replacement: String,
}

impl ApiError {
    fn invalid_input(message: impl Into<String>) -> Self {
        Self {
            status: STATUS_INVALID_INPUT,
            message: message.into(),
        }
    }

    fn failed(message: impl Into<String>) -> Self {
        Self {
            status: STATUS_FAILED,
            message: message.into(),
        }
    }

    fn panic(payload: &(dyn Any + Send)) -> Self {
        let detail = if let Some(message) = payload.downcast_ref::<&'static str>() {
            (*message).to_string()
        } else if let Some(message) = payload.downcast_ref::<String>() {
            message.clone()
        } else {
            "unknown panic payload".to_string()
        };
        Self {
            status: STATUS_PANIC,
            message: format!("talk-c: internal panic: {detail}"),
        }
    }
}

impl From<ApiError> for HandleStatus {
    fn from(error: ApiError) -> Self {
        Self {
            status: error.status,
            error: error.message,
        }
    }
}

impl HandleStatus {
    fn ok() -> Self {
        Self {
            status: STATUS_OK,
            error: String::new(),
        }
    }
}

impl TalkStringRef {
    fn empty() -> Self {
        Self {
            ptr: std::ptr::null(),
            len: 0,
        }
    }

    fn from_str(value: &str) -> Self {
        if value.is_empty() {
            Self::empty()
        } else {
            Self {
                ptr: value.as_ptr(),
                len: value.len(),
            }
        }
    }
}

impl TalkOptionalStringRef {
    fn none() -> Self {
        Self {
            present: OPTIONAL_ABSENT,
            value: TalkStringRef::empty(),
        }
    }

    fn from_option(value: Option<&str>) -> Self {
        match value {
            Some(value) => Self {
                present: OPTIONAL_PRESENT,
                value: TalkStringRef::from_str(value),
            },
            None => Self::none(),
        }
    }
}

impl TalkTextRange {
    fn empty() -> Self {
        Self { start: 0, end: 0 }
    }

    fn from_range(range: TextRange) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }
}

impl TalkBuffer {
    fn empty() -> Self {
        Self {
            ptr: std::ptr::null_mut(),
            len: 0,
        }
    }

    fn from_vec(bytes: Vec<u8>) -> Self {
        if bytes.is_empty() {
            return Self::empty();
        }

        let mut bytes = bytes.into_boxed_slice();
        let ptr = bytes.as_mut_ptr();
        let len = bytes.len();
        std::mem::forget(bytes);
        Self { ptr, len }
    }

    fn from_string(value: String) -> Self {
        Self::from_vec(value.into_bytes())
    }

    unsafe fn free(self) {
        if self.ptr.is_null() || self.len == 0 {
            return;
        }
        let raw = std::ptr::slice_from_raw_parts_mut(self.ptr, self.len);
        // SAFETY: TalkBuffer values returned by this crate are allocated as
        // boxed byte slices with exactly this pointer and length.
        unsafe { drop(Box::from_raw(raw)) };
    }
}

impl TalkPackageArchiveSink {
    fn new() -> Self {
        Self {
            bytes: Vec::new(),
            error: None,
            finished: false,
        }
    }

    fn write(&mut self, bytes: &[u8]) {
        if self.error.is_none() && !self.finished {
            self.bytes.extend_from_slice(bytes);
        }
    }

    fn finish(&mut self) {
        if self.error.is_none() {
            self.finished = true;
        }
    }

    fn fail(&mut self, message: String) {
        if !self.finished {
            self.error = Some(message);
        }
    }

    fn into_result(self) -> Result<Vec<u8>, String> {
        match (self.error, self.finished) {
            (Some(error), _) => Err(error),
            (None, true) => Ok(self.bytes),
            (None, false) => Err("package source provider did not finish the tar download".into()),
        }
    }
}

impl PackageSourceProvider for CPackageSourceProvider {
    fn capabilities(&self) -> PackageSourceCapabilities {
        PackageSourceCapabilities::TAR
    }

    fn fetch_tar(&self, url: &str, sha256: &str) -> Result<Vec<u8>, String> {
        let mut sink = TalkPackageArchiveSink::new();
        // SAFETY: The callback, context, and sink were supplied by the host
        // provider and are valid for this synchronous invocation.
        unsafe {
            (self.fetch_tar)(
                self.context,
                TalkStringRef::from_str(url),
                TalkStringRef::from_str(sha256),
                &mut sink,
            );
        }
        sink.into_result()
    }
}

impl TalkResult {
    fn ok_bytes(bytes: Vec<u8>) -> Self {
        Self {
            status: STATUS_OK,
            data: TalkBuffer::from_vec(bytes),
            error: TalkBuffer::empty(),
        }
    }

    fn ok_string(value: String) -> Self {
        Self {
            status: STATUS_OK,
            data: TalkBuffer::from_string(value),
            error: TalkBuffer::empty(),
        }
    }

    fn ok_empty() -> Self {
        Self {
            status: STATUS_OK,
            data: TalkBuffer::empty(),
            error: TalkBuffer::empty(),
        }
    }

    fn err(error: ApiError) -> Self {
        Self {
            status: error.status,
            data: TalkBuffer::empty(),
            error: TalkBuffer::from_string(error.message),
        }
    }
}

struct Boundary;

impl Boundary {
    fn string(call: impl FnOnce() -> ApiResult<String>) -> TalkResult {
        match catch_unwind(AssertUnwindSafe(call)) {
            Ok(Ok(value)) => TalkResult::ok_string(value),
            Ok(Err(error)) => TalkResult::err(error),
            Err(payload) => TalkResult::err(ApiError::panic(payload.as_ref())),
        }
    }

    fn bytes(call: impl FnOnce() -> ApiResult<Vec<u8>>) -> TalkResult {
        match catch_unwind(AssertUnwindSafe(call)) {
            Ok(Ok(value)) => TalkResult::ok_bytes(value),
            Ok(Err(error)) => TalkResult::err(error),
            Err(payload) => TalkResult::err(ApiError::panic(payload.as_ref())),
        }
    }

    fn empty(call: impl FnOnce() -> ApiResult<()>) -> TalkResult {
        match catch_unwind(AssertUnwindSafe(call)) {
            Ok(Ok(())) => TalkResult::ok_empty(),
            Ok(Err(error)) => TalkResult::err(error),
            Err(payload) => TalkResult::err(ApiError::panic(payload.as_ref())),
        }
    }

    fn handle<H, T>(
        call: impl FnOnce() -> ApiResult<T>,
        ok: impl FnOnce(T) -> *mut H,
        err: impl FnOnce(ApiError) -> *mut H,
    ) -> *mut H {
        match catch_unwind(AssertUnwindSafe(call)) {
            Ok(Ok(value)) => ok(value),
            Ok(Err(error)) => err(error),
            Err(payload) => err(ApiError::panic(payload.as_ref())),
        }
    }
}

struct RawBytes {
    ptr: *const u8,
    len: usize,
    name: &'static str,
}

impl RawBytes {
    fn new(ptr: *const u8, len: usize, name: &'static str) -> Self {
        Self { ptr, len, name }
    }

    fn bytes(&self) -> ApiResult<&[u8]> {
        if self.len == 0 {
            return Ok(&[]);
        }
        if self.ptr.is_null() {
            return Err(ApiError::invalid_input(format!(
                "{} pointer is null but length is {}",
                self.name, self.len
            )));
        }
        // SAFETY: The caller provides a pointer valid for len bytes for the
        // duration of the call. The slice is only read and never stored.
        Ok(unsafe { std::slice::from_raw_parts(self.ptr, self.len) })
    }

    fn string(&self) -> ApiResult<String> {
        let bytes = self.bytes()?;
        std::str::from_utf8(bytes)
            .map(|value| value.to_string())
            .map_err(|err| ApiError::invalid_input(format!("{} is not UTF-8: {err}", self.name)))
    }
}

struct WorkspacePtr(*mut TalkWorkspace);

impl WorkspacePtr {
    fn new(ptr: *mut TalkWorkspace) -> Self {
        Self(ptr)
    }

    fn get_mut(&mut self) -> ApiResult<&mut TalkWorkspace> {
        if self.0.is_null() {
            return Err(ApiError::invalid_input("workspace pointer is null"));
        }
        // SAFETY: The C API requires a pointer returned by talk_workspace_new
        // and exclusive use during this call.
        Ok(unsafe { &mut *self.0 })
    }
}

struct ReplPtr(*mut TalkReplSession);

struct PackageProviderPtr(*const TalkPackageProvider);

impl PackageProviderPtr {
    fn new(ptr: *const TalkPackageProvider) -> Self {
        Self(ptr)
    }

    fn get(&self) -> ApiResult<&TalkPackageProvider> {
        if self.0.is_null() {
            return Err(ApiError::invalid_input(
                "package source provider pointer is null",
            ));
        }
        // SAFETY: The C API requires a pointer returned by
        // talk_package_provider_new that remains alive during this call.
        Ok(unsafe { &*self.0 })
    }
}

impl ReplPtr {
    fn new(ptr: *mut TalkReplSession) -> Self {
        Self(ptr)
    }

    fn get_mut(&mut self) -> ApiResult<&mut TalkReplSession> {
        if self.0.is_null() {
            return Err(ApiError::invalid_input("repl pointer is null"));
        }
        // SAFETY: The C API requires a pointer returned by talk_repl_new and
        // exclusive use during this call.
        Ok(unsafe { &mut *self.0 })
    }
}

impl TalkWorkspace {
    fn new() -> Self {
        Self {
            docs: Vec::new(),
            workspace: None,
            core: None,
            dirty: true,
        }
    }

    fn clear(&mut self) {
        self.docs.clear();
        self.workspace = None;
        self.dirty = true;
    }

    fn set_document(&mut self, id: String, path: String, version: i32, text: String) {
        let input = DocumentInput {
            id: id.clone(),
            path,
            version,
            text,
        };
        if let Some(existing) = self.docs.iter_mut().find(|doc| doc.id == id) {
            *existing = input;
        } else {
            self.docs.push(input);
        }
        self.workspace = None;
        self.dirty = true;
    }

    fn remove_document(&mut self, id: &str) {
        self.docs.retain(|doc| doc.id != id);
        self.workspace = None;
        self.dirty = true;
    }

    fn analyze(&mut self) -> ApiResult<&Workspace> {
        if self.docs.is_empty() {
            return Err(ApiError::invalid_input("workspace has no documents"));
        }
        let workspace = Workspace::new(self.docs.clone())
            .ok_or_else(|| ApiError::failed("failed to analyze workspace"))?;
        self.workspace = Some(workspace);
        self.dirty = false;
        self.workspace
            .as_ref()
            .ok_or_else(|| ApiError::failed("failed to store workspace analysis"))
    }

    fn ensure_analysis(&mut self) -> ApiResult<&Workspace> {
        if self.dirty || self.workspace.is_none() {
            return self.analyze();
        }
        self.workspace
            .as_ref()
            .ok_or_else(|| ApiError::failed("workspace analysis is unavailable"))
    }

    fn ensure_core(&mut self) -> Option<&Workspace> {
        if self.core.is_none() {
            self.core = Workspace::core();
        }
        self.core.as_ref()
    }
}

impl TalkDiagnostics {
    fn ok(items: Vec<DiagnosticRecord>) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: HandleStatus::ok(),
            items,
        }))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            items: Vec::new(),
        }))
    }
}

impl TalkHover {
    fn ok(value: Option<HoverRecord>) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: HandleStatus::ok(),
            value,
        }))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            value: None,
        }))
    }
}

impl TalkCompletions {
    fn ok(items: Vec<CompletionRecord>) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: HandleStatus::ok(),
            items,
        }))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            items: Vec::new(),
        }))
    }
}

impl TalkInlayHints {
    fn ok(items: Vec<InlayHintRecord>) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: HandleStatus::ok(),
            items,
        }))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            items: Vec::new(),
        }))
    }
}

impl TalkHighlightTokens {
    fn ok(items: Vec<HighlightTokenRecord>) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: HandleStatus::ok(),
            items,
        }))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            items: Vec::new(),
        }))
    }
}

impl TalkLocationResult {
    fn ok(value: Option<LocationRecord>) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: HandleStatus::ok(),
            value,
        }))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            value: None,
        }))
    }
}

impl TalkWorkspaceEditResult {
    fn ok(documents: Vec<DocumentEditRecord>) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: HandleStatus::ok(),
            documents,
        }))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            documents: Vec::new(),
        }))
    }
}

impl TalkEvalResult {
    fn ok(value: ReplEvalResult) -> *mut Self {
        Box::into_raw(Box::new(Self::from_repl_result(HandleStatus::ok(), value)))
    }

    fn boxed(value: Self) -> *mut Self {
        Box::into_raw(Box::new(value))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            kind: EVAL_ERROR,
            stdout: String::new(),
            stderr: String::new(),
            value: None,
            source: String::new(),
            message: None,
            diagnostics: Vec::new(),
        }))
    }

    fn from_repl_result(status: HandleStatus, result: ReplEvalResult) -> Self {
        match result {
            ReplEvalResult::Output {
                stdout,
                stderr,
                value,
            } => Self {
                status,
                kind: EVAL_OUTPUT,
                stdout,
                stderr,
                value,
                source: String::new(),
                message: None,
                diagnostics: Vec::new(),
            },
            ReplEvalResult::Diagnostics {
                source,
                diagnostics,
                message,
            } => Self {
                status,
                kind: EVAL_DIAGNOSTICS,
                stdout: String::new(),
                stderr: String::new(),
                value: None,
                source,
                message,
                diagnostics: diagnostic_records_for_repl(diagnostics),
            },
            ReplEvalResult::Error(message) => Self {
                status,
                kind: EVAL_ERROR,
                stdout: String::new(),
                stderr: String::new(),
                value: None,
                source: String::new(),
                message: Some(message),
                diagnostics: Vec::new(),
            },
        }
    }

    fn diagnostics(
        source: String,
        diagnostics: Vec<DiagnosticRecord>,
        message: Option<String>,
    ) -> Self {
        Self {
            status: HandleStatus::ok(),
            kind: EVAL_DIAGNOSTICS,
            stdout: String::new(),
            stderr: String::new(),
            value: None,
            source,
            message,
            diagnostics,
        }
    }
}

impl TalkTestResult {
    fn no_tests() -> Self {
        Self {
            status: HandleStatus::ok(),
            kind: TEST_NO_TESTS,
            output: String::new(),
            failures: 0,
        }
    }

    fn finished(output: String, failures: i64) -> Self {
        Self {
            status: HandleStatus::ok(),
            kind: TEST_FINISHED,
            output,
            failures,
        }
    }

    fn boxed(value: Self) -> *mut Self {
        Box::into_raw(Box::new(value))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            kind: 0,
            output: String::new(),
            failures: 0,
        }))
    }
}

impl TalkReplCompletions {
    fn ok(value: ReplCompletions) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: HandleStatus::ok(),
            start: value.start,
            items: value
                .items
                .into_iter()
                .map(|item| ReplCompletionRecord {
                    display: item.display,
                    replacement: item.replacement,
                })
                .collect(),
        }))
    }

    fn err(error: ApiError) -> *mut Self {
        Box::into_raw(Box::new(Self {
            status: error.into(),
            start: 0,
            items: Vec::new(),
        }))
    }
}

struct ProgramRunner;

impl ProgramRunner {
    fn run(path: String, source: String) -> ApiResult<TalkEvalResult> {
        let doc = DocumentInput {
            id: path.clone(),
            path: path.clone(),
            version: 0,
            text: source.clone(),
        };
        let workspace = Workspace::new(vec![doc])
            .ok_or_else(|| ApiError::failed("failed to analyze program"))?;
        let diagnostics = diagnostic_records_from_workspace(&workspace, None);
        if !diagnostics.is_empty() {
            return Ok(TalkEvalResult::diagnostics(
                source,
                diagnostics,
                Some("program has diagnostics".to_string()),
            ));
        }

        let driver = Driver::new(
            vec![Source::in_memory(PathBuf::from(&path), source)],
            DriverConfig::new("App"),
        );
        let parsed = driver
            .parse()
            .map_err(|err| ApiError::failed(format!("failed to parse: {err:?}")))?;
        let resolved = parsed
            .resolve_names()
            .map_err(|err| ApiError::failed(format!("failed to resolve names: {err:?}")))?;
        let typed = resolved.type_check();
        if typed.has_errors() {
            let message = typed
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            return Ok(TalkEvalResult::from_repl_result(
                HandleStatus::ok(),
                ReplEvalResult::Error(message),
            ));
        }
        let names = Self::value_names(typed.phase.program.types());
        let mut lowered = typed.lower();
        if !lowered.phase.diagnostics.is_empty() {
            return Ok(TalkEvalResult::from_repl_result(
                HandleStatus::ok(),
                ReplEvalResult::Error(format!(
                    "not yet supported by the backend: {}",
                    lowered.phase.diagnostics.join("; ")
                )),
            ));
        }
        match lowered.run_vm_displayed(&names) {
            Ok((_, stdout, display)) => Ok(TalkEvalResult::from_repl_result(
                HandleStatus::ok(),
                ReplEvalResult::Output {
                    stdout,
                    stderr: String::new(),
                    value: Some(display),
                },
            )),
            Err(err) => Ok(TalkEvalResult::from_repl_result(
                HandleStatus::ok(),
                ReplEvalResult::Error(format!("evaluation failed: {err}")),
            )),
        }
    }

    fn value_names(types: &talk::types::TypeOutput) -> talk::vm::interp::ValueNames {
        let mut names = talk::vm::interp::ValueNames::default();
        for (symbol, info) in &types.catalog.structs {
            let display = types
                .display_names
                .get(symbol)
                .cloned()
                .unwrap_or_else(|| symbol.to_string());
            let fields: Vec<&str> = info.fields.keys().map(|name| name.as_str()).collect();
            if display == "String"
                && (fields == ["base", "byte_count", "capacity"]
                    || fields == ["storage", "byte_count", "capacity"])
            {
                names.string_struct = Some(talk::vm::runtime_symbol(*symbol));
            }
            let runtime_symbol = talk::vm::runtime_symbol(*symbol);
            names
                .fields
                .insert(runtime_symbol, info.fields.keys().cloned().collect());
            names.types.insert(runtime_symbol, display);
        }
        for (symbol, info) in &types.catalog.enums {
            let display = types
                .display_names
                .get(symbol)
                .cloned()
                .unwrap_or_else(|| symbol.to_string());
            let runtime_symbol = talk::vm::runtime_symbol(*symbol);
            names
                .cases
                .insert(runtime_symbol, info.variants.keys().cloned().collect());
            names.types.insert(runtime_symbol, display);
        }
        names
    }
}

struct PackageRunner;

impl PackageRunner {
    fn create(root: String, name: String, version: String, binary_name: String) -> ApiResult<()> {
        let root = Self::root(root)?;
        PackageProject::create_executable_at(root, &name, &version, &binary_name)
            .map_err(|error| ApiError::failed(error.to_string()))
    }

    fn install(
        root: String,
        offline: bool,
        update: bool,
        provider: Option<&TalkPackageProvider>,
    ) -> ApiResult<()> {
        let root = Self::root(root)?;
        match provider {
            Some(provider) => PackageProject::install_at_with_provider(
                root,
                offline,
                update,
                provider.provider.clone(),
            ),
            None => PackageProject::install_at(root, offline, update),
        }
        .map(|_| ())
        .map_err(|error| ApiError::failed(error.to_string()))
    }

    fn run(
        root: String,
        binary_name: Option<String>,
        offline: bool,
        provider: Option<&TalkPackageProvider>,
    ) -> ApiResult<TalkEvalResult> {
        let project = Self::open(root, offline, provider)?;
        let mut lowered = project
            .compile_binary(binary_name.as_deref())
            .map_err(|error| ApiError::failed(error.to_string()))?;
        match lowered.run_vm_with_output() {
            Ok((value, stdout)) => Ok(TalkEvalResult::from_repl_result(
                HandleStatus::ok(),
                ReplEvalResult::Output {
                    stdout,
                    stderr: String::new(),
                    value: (!matches!(value, talk::vm::interp::Value::Void))
                        .then(|| format!("{value:?}")),
                },
            )),
            Err(error) => Ok(TalkEvalResult::from_repl_result(
                HandleStatus::ok(),
                ReplEvalResult::Error(format!("evaluation failed: {error}")),
            )),
        }
    }

    fn test(
        root: String,
        offline: bool,
        provider: Option<&TalkPackageProvider>,
    ) -> ApiResult<TalkTestResult> {
        let project = Self::open(root, offline, provider)?;
        match project
            .run_tests()
            .map_err(|error| ApiError::failed(error.to_string()))?
        {
            talk::testing::Outcome::NoTests => Ok(TalkTestResult::no_tests()),
            talk::testing::Outcome::Finished(summary) => {
                Ok(TalkTestResult::finished(summary.output, summary.failures))
            }
        }
    }

    fn open(
        root: String,
        offline: bool,
        provider: Option<&TalkPackageProvider>,
    ) -> ApiResult<PackageProject> {
        let root = Self::root(root)?;
        match provider {
            Some(provider) => {
                PackageProject::open_at_with_provider(root, offline, provider.provider.clone())
            }
            None => PackageProject::open_at(root, offline),
        }
        .map_err(|error| ApiError::failed(error.to_string()))
    }

    fn root(root: String) -> ApiResult<PathBuf> {
        if root.is_empty() {
            return Err(ApiError::invalid_input("package root must not be empty"));
        }
        Ok(PathBuf::from(root))
    }
}

fn path_or_stdin(path: String) -> String {
    if path.is_empty() {
        "<stdin>".to_string()
    } else {
        path
    }
}

fn diagnostic_records_from_workspace(
    workspace: &Workspace,
    document_id: Option<&DocumentId>,
) -> Vec<DiagnosticRecord> {
    let mut doc_ids: Vec<&DocumentId> = workspace.diagnostics.keys().collect();
    doc_ids.sort();
    let mut records = Vec::new();
    for doc_id in doc_ids {
        if document_id.is_some_and(|wanted| wanted != doc_id) {
            continue;
        }
        let Some(diagnostics) = workspace.diagnostics.get(doc_id) else {
            continue;
        };
        for diagnostic in diagnostics {
            records.push(diagnostic_record(doc_id, diagnostic));
        }
    }
    records
}

fn diagnostic_records_for_repl(diagnostics: Vec<Diagnostic>) -> Vec<DiagnosticRecord> {
    diagnostics
        .into_iter()
        .map(|diagnostic| DiagnosticRecord {
            document: "<repl>".to_string(),
            range: diagnostic.range,
            severity: diagnostic_severity(diagnostic.severity),
            message: diagnostic.message,
        })
        .collect()
}

fn diagnostic_record(document_id: &str, diagnostic: &Diagnostic) -> DiagnosticRecord {
    DiagnosticRecord {
        document: document_id.to_string(),
        range: diagnostic.range,
        severity: diagnostic_severity(diagnostic.severity),
        message: diagnostic.message.clone(),
    }
}

fn diagnostic_severity(severity: DiagnosticSeverity) -> i32 {
    match severity {
        DiagnosticSeverity::Error => DIAGNOSTIC_ERROR,
        DiagnosticSeverity::Warning => DIAGNOSTIC_WARNING,
        DiagnosticSeverity::Info => DIAGNOSTIC_INFO,
    }
}

fn completion_kind(kind: Option<CompletionItemKind>) -> i32 {
    match kind {
        Some(CompletionItemKind::Struct) => COMPLETION_STRUCT,
        Some(CompletionItemKind::Enum) => COMPLETION_ENUM,
        Some(CompletionItemKind::Interface) => COMPLETION_INTERFACE,
        Some(CompletionItemKind::Class) => COMPLETION_CLASS,
        Some(CompletionItemKind::TypeParameter) => COMPLETION_TYPE_PARAMETER,
        Some(CompletionItemKind::Variable) => COMPLETION_VARIABLE,
        Some(CompletionItemKind::Field) => COMPLETION_FIELD,
        Some(CompletionItemKind::Method) => COMPLETION_METHOD,
        Some(CompletionItemKind::Constructor) => COMPLETION_CONSTRUCTOR,
        Some(CompletionItemKind::EnumMember) => COMPLETION_ENUM_MEMBER,
        Some(CompletionItemKind::Keyword) => COMPLETION_KEYWORD,
        Some(CompletionItemKind::Module) => COMPLETION_MODULE,
        Some(CompletionItemKind::Effect) => COMPLETION_EFFECT,
        None => COMPLETION_NONE,
    }
}

fn inlay_kind(kind: OwnershipInlayHintKind) -> i32 {
    match kind {
        OwnershipInlayHintKind::Move => INLAY_MOVE,
        OwnershipInlayHintKind::Borrow => INLAY_BORROW,
        OwnershipInlayHintKind::Drop => INLAY_DROP,
        OwnershipInlayHintKind::Clone => INLAY_CLONE,
    }
}

fn highlight_kind(kind: talk::highlighter::Kind) -> i32 {
    match kind {
        talk::highlighter::Kind::DECORATOR => HIGHLIGHT_DECORATOR,
        talk::highlighter::Kind::NAMESPACE => HIGHLIGHT_NAMESPACE,
        talk::highlighter::Kind::TYPE => HIGHLIGHT_TYPE,
        talk::highlighter::Kind::CLASS => HIGHLIGHT_CLASS,
        talk::highlighter::Kind::ENUM => HIGHLIGHT_ENUM,
        talk::highlighter::Kind::INTERFACE => HIGHLIGHT_INTERFACE,
        talk::highlighter::Kind::STRUCT => HIGHLIGHT_STRUCT,
        talk::highlighter::Kind::TYPE_PARAMETER => HIGHLIGHT_TYPE_PARAMETER,
        talk::highlighter::Kind::PARAMETER => HIGHLIGHT_PARAMETER,
        talk::highlighter::Kind::VARIABLE => HIGHLIGHT_VARIABLE,
        talk::highlighter::Kind::PROPERTY => HIGHLIGHT_PROPERTY,
        talk::highlighter::Kind::ENUM_MEMBER => HIGHLIGHT_ENUM_MEMBER,
        talk::highlighter::Kind::EVENT => HIGHLIGHT_EVENT,
        talk::highlighter::Kind::FUNCTION => HIGHLIGHT_FUNCTION,
        talk::highlighter::Kind::METHOD => HIGHLIGHT_METHOD,
        talk::highlighter::Kind::MACRO => HIGHLIGHT_MACRO,
        talk::highlighter::Kind::KEYWORD => HIGHLIGHT_KEYWORD,
        talk::highlighter::Kind::MODIFIER => HIGHLIGHT_MODIFIER,
        talk::highlighter::Kind::COMMENT => HIGHLIGHT_COMMENT,
        talk::highlighter::Kind::STRING => HIGHLIGHT_STRING,
        talk::highlighter::Kind::NUMBER => HIGHLIGHT_NUMBER,
        talk::highlighter::Kind::REGEXP => HIGHLIGHT_REGEXP,
        talk::highlighter::Kind::OPERATOR => HIGHLIGHT_OPERATOR,
        talk::highlighter::Kind::EFFECT => HIGHLIGHT_EFFECT,
    }
}

fn hover_record(hover: Hover) -> HoverRecord {
    HoverRecord {
        contents: hover.contents,
        range: hover.range,
    }
}

fn completion_records(items: Vec<CompletionItem>) -> Vec<CompletionRecord> {
    items
        .into_iter()
        .map(|item| CompletionRecord {
            label: item.label,
            kind: completion_kind(item.kind),
            detail: item.detail,
            insert_text: item.insert_text,
            insert_text_is_snippet: i32::from(item.insert_text_is_snippet),
        })
        .collect()
}

fn inlay_hint_records(items: Vec<OwnershipInlayHint>) -> Vec<InlayHintRecord> {
    items
        .into_iter()
        .map(|item| InlayHintRecord {
            position: item.position,
            label: item.label,
            tooltip: item.tooltip,
            kind: inlay_kind(item.kind),
        })
        .collect()
}

fn location_record(location: Location) -> LocationRecord {
    LocationRecord {
        document: location.document_id,
        range: location.range,
    }
}

fn workspace_edit_records(edit: Option<talk::analysis::WorkspaceEdit>) -> Vec<DocumentEditRecord> {
    edit.map(|edit| {
        edit.documents
            .into_iter()
            .map(|document| DocumentEditRecord {
                document: document.document_id,
                edits: document
                    .edits
                    .into_iter()
                    .map(|edit| TextEditRecord {
                        range: edit.range,
                        replacement: edit.replacement,
                    })
                    .collect(),
            })
            .collect()
    })
    .unwrap_or_default()
}

fn highlight_records(source: &str) -> Vec<HighlightTokenRecord> {
    let mut highlighter = talk::highlighter::Higlighter::new(source);
    let mut tokens = highlighter.highlight();
    tokens.sort_by(|a, b| a.start.cmp(&b.start).then_with(|| b.end.cmp(&a.end)));
    tokens
        .into_iter()
        .map(|token| HighlightTokenRecord {
            kind: highlight_kind(token.kind),
            start: token.start,
            end: token.end,
        })
        .collect()
}

unsafe fn free_box<T>(ptr: *mut T) {
    if ptr.is_null() {
        return;
    }
    // SAFETY: The pointer must have been allocated by Box::into_raw in this
    // crate for the same T and not already freed.
    unsafe { drop(Box::from_raw(ptr)) };
}

unsafe fn handle_ref<'a, T>(ptr: *const T) -> Option<&'a T> {
    if ptr.is_null() {
        None
    } else {
        // SAFETY: Callers must pass a valid pointer returned by this crate and
        // keep it alive for the duration of the call.
        Some(unsafe { &*ptr })
    }
}

fn status_of(status: Option<&HandleStatus>) -> i32 {
    status
        .map(|status| status.status)
        .unwrap_or(STATUS_INVALID_INPUT)
}

fn error_of(status: Option<&HandleStatus>) -> TalkStringRef {
    status
        .map(|status| TalkStringRef::from_str(&status.error))
        .unwrap_or_else(TalkStringRef::empty)
}

fn diagnostic_view(record: Option<&DiagnosticRecord>) -> TalkDiagnosticView {
    match record {
        Some(record) => TalkDiagnosticView {
            document: TalkStringRef::from_str(&record.document),
            range: TalkTextRange::from_range(record.range),
            severity: record.severity,
            message: TalkStringRef::from_str(&record.message),
        },
        None => TalkDiagnosticView {
            document: TalkStringRef::empty(),
            range: TalkTextRange::empty(),
            severity: 0,
            message: TalkStringRef::empty(),
        },
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_result_free(result: TalkResult) {
    // SAFETY: The buffers came from this crate or are empty.
    unsafe {
        result.data.free();
        result.error.free();
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_buffer_free(buffer: TalkBuffer) {
    // SAFETY: The buffer came from this crate or is empty.
    unsafe { buffer.free() }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_version_utf8() -> TalkResult {
    TalkResult::ok_string(env!("CARGO_PKG_VERSION").to_string())
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_format_utf8(source_ptr: *const u8, source_len: usize) -> TalkResult {
    Boundary::string(|| {
        let source = RawBytes::new(source_ptr, source_len, "source").string()?;
        Ok(talk::formatter::format_string(&source))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_highlight_tokens_utf8(
    source_ptr: *const u8,
    source_len: usize,
) -> *mut TalkHighlightTokens {
    Boundary::handle(
        || {
            let source = RawBytes::new(source_ptr, source_len, "source").string()?;
            Ok(highlight_records(&source))
        },
        TalkHighlightTokens::ok,
        TalkHighlightTokens::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_highlight_html_utf8(source_ptr: *const u8, source_len: usize) -> TalkResult {
    Boundary::string(|| {
        let source = RawBytes::new(source_ptr, source_len, "source").string()?;
        Ok(talk::highlighter::highlight_html(&source))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_check_utf8(
    path_ptr: *const u8,
    path_len: usize,
    source_ptr: *const u8,
    source_len: usize,
) -> *mut TalkDiagnostics {
    Boundary::handle(
        || {
            let path = path_or_stdin(RawBytes::new(path_ptr, path_len, "path").string()?);
            let source = RawBytes::new(source_ptr, source_len, "source").string()?;
            let doc = DocumentInput {
                id: path.clone(),
                path,
                version: 0,
                text: source,
            };
            let workspace = Workspace::new(vec![doc])
                .ok_or_else(|| ApiError::failed("failed to analyze document"))?;
            Ok(diagnostic_records_from_workspace(&workspace, None))
        },
        TalkDiagnostics::ok,
        TalkDiagnostics::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_run_program_utf8(
    path_ptr: *const u8,
    path_len: usize,
    source_ptr: *const u8,
    source_len: usize,
) -> *mut TalkEvalResult {
    Boundary::handle(
        || {
            let path = path_or_stdin(RawBytes::new(path_ptr, path_len, "path").string()?);
            let source = RawBytes::new(source_ptr, source_len, "source").string()?;
            ProgramRunner::run(path, source)
        },
        TalkEvalResult::boxed,
        TalkEvalResult::err,
    )
}

#[unsafe(no_mangle)]
#[allow(clippy::arc_with_non_send_sync)]
pub extern "C" fn talk_package_provider_new(
    capabilities: i32,
    fetch_tar: Option<PackageFetchTarCallback>,
    context: *mut c_void,
) -> *mut TalkPackageProvider {
    if capabilities != PACKAGE_SOURCE_TAR {
        return std::ptr::null_mut();
    }
    let Some(fetch_tar) = fetch_tar else {
        return std::ptr::null_mut();
    };
    Box::into_raw(Box::new(TalkPackageProvider {
        provider: Arc::new(CPackageSourceProvider { fetch_tar, context }),
    }))
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_provider_free(provider: *mut TalkPackageProvider) {
    // SAFETY: The pointer must have been returned by talk_package_provider_new
    // and not already freed.
    unsafe { free_box(provider) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_archive_sink_write(
    sink: *mut TalkPackageArchiveSink,
    bytes_ptr: *const u8,
    bytes_len: usize,
) {
    // SAFETY: The sink is valid only for the duration of its fetch callback.
    let Some(sink) = (unsafe { sink.as_mut() }) else {
        return;
    };
    match RawBytes::new(bytes_ptr, bytes_len, "package archive").bytes() {
        Ok(bytes) => sink.write(bytes),
        Err(error) => sink.fail(error.message),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_archive_sink_finish(sink: *mut TalkPackageArchiveSink) {
    // SAFETY: The sink is valid only for the duration of its fetch callback.
    if let Some(sink) = unsafe { sink.as_mut() } {
        sink.finish();
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_archive_sink_fail_utf8(
    sink: *mut TalkPackageArchiveSink,
    message_ptr: *const u8,
    message_len: usize,
) {
    // SAFETY: The sink is valid only for the duration of its fetch callback.
    let Some(sink) = (unsafe { sink.as_mut() }) else {
        return;
    };
    match RawBytes::new(message_ptr, message_len, "package source provider error").string() {
        Ok(message) => sink.fail(message),
        Err(error) => sink.fail(error.message),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_install_utf8(
    root_ptr: *const u8,
    root_len: usize,
    offline: bool,
    update: bool,
) -> TalkResult {
    Boundary::empty(|| {
        let root = RawBytes::new(root_ptr, root_len, "package root").string()?;
        PackageRunner::install(root, offline, update, None)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_install_with_provider_utf8(
    provider: *const TalkPackageProvider,
    root_ptr: *const u8,
    root_len: usize,
    offline: bool,
    update: bool,
) -> TalkResult {
    Boundary::empty(|| {
        let root = RawBytes::new(root_ptr, root_len, "package root").string()?;
        let provider_ptr = PackageProviderPtr::new(provider);
        let provider = provider_ptr.get()?;
        PackageRunner::install(root, offline, update, Some(provider))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_create_utf8(
    root_ptr: *const u8,
    root_len: usize,
    name_ptr: *const u8,
    name_len: usize,
    version_ptr: *const u8,
    version_len: usize,
    binary_name_ptr: *const u8,
    binary_name_len: usize,
) -> TalkResult {
    Boundary::empty(|| {
        let root = RawBytes::new(root_ptr, root_len, "package root").string()?;
        let name = RawBytes::new(name_ptr, name_len, "package name").string()?;
        let version = RawBytes::new(version_ptr, version_len, "package version").string()?;
        let binary_name =
            RawBytes::new(binary_name_ptr, binary_name_len, "binary name").string()?;
        PackageRunner::create(root, name, version, binary_name)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_run_utf8(
    root_ptr: *const u8,
    root_len: usize,
    binary_name_ptr: *const u8,
    binary_name_len: usize,
    offline: bool,
) -> *mut TalkEvalResult {
    Boundary::handle(
        || {
            let root = RawBytes::new(root_ptr, root_len, "package root").string()?;
            let binary_name =
                RawBytes::new(binary_name_ptr, binary_name_len, "binary name").string()?;
            PackageRunner::run(
                root,
                (!binary_name.is_empty()).then_some(binary_name),
                offline,
                None,
            )
        },
        TalkEvalResult::boxed,
        TalkEvalResult::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_run_with_provider_utf8(
    provider: *const TalkPackageProvider,
    root_ptr: *const u8,
    root_len: usize,
    binary_name_ptr: *const u8,
    binary_name_len: usize,
    offline: bool,
) -> *mut TalkEvalResult {
    Boundary::handle(
        || {
            let root = RawBytes::new(root_ptr, root_len, "package root").string()?;
            let binary_name =
                RawBytes::new(binary_name_ptr, binary_name_len, "binary name").string()?;
            let provider_ptr = PackageProviderPtr::new(provider);
            let provider = provider_ptr.get()?;
            PackageRunner::run(
                root,
                (!binary_name.is_empty()).then_some(binary_name),
                offline,
                Some(provider),
            )
        },
        TalkEvalResult::boxed,
        TalkEvalResult::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_test_utf8(
    root_ptr: *const u8,
    root_len: usize,
    offline: bool,
) -> *mut TalkTestResult {
    Boundary::handle(
        || {
            let root = RawBytes::new(root_ptr, root_len, "package root").string()?;
            PackageRunner::test(root, offline, None)
        },
        TalkTestResult::boxed,
        TalkTestResult::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_package_test_with_provider_utf8(
    provider: *const TalkPackageProvider,
    root_ptr: *const u8,
    root_len: usize,
    offline: bool,
) -> *mut TalkTestResult {
    Boundary::handle(
        || {
            let root = RawBytes::new(root_ptr, root_len, "package root").string()?;
            let provider_ptr = PackageProviderPtr::new(provider);
            let provider = provider_ptr.get()?;
            PackageRunner::test(root, offline, Some(provider))
        },
        TalkTestResult::boxed,
        TalkTestResult::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_render_lowered_utf8(
    path_ptr: *const u8,
    path_len: usize,
    source_ptr: *const u8,
    source_len: usize,
) -> TalkResult {
    Boundary::string(|| {
        let path = path_or_stdin(RawBytes::new(path_ptr, path_len, "path").string()?);
        let source = RawBytes::new(source_ptr, source_len, "source").string()?;
        let styles = talk::lambda_g::print::Styles::plain();
        talk::compiling::driver::render_lowered_from(
            "App",
            Source::in_memory(PathBuf::from(path), source),
            &styles,
        )
        .map_err(ApiError::failed)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_render_bytecode_utf8(
    path_ptr: *const u8,
    path_len: usize,
    source_ptr: *const u8,
    source_len: usize,
) -> TalkResult {
    Boundary::string(|| {
        let path = path_or_stdin(RawBytes::new(path_ptr, path_len, "path").string()?);
        let source = RawBytes::new(source_ptr, source_len, "source").string()?;
        let styles = talk::lambda_g::print::Styles::plain();
        talk::compiling::driver::render_bytecode_from(
            "App",
            Source::in_memory(PathBuf::from(path), source),
            &styles,
        )
        .map_err(ApiError::failed)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_compile_bytecode_utf8(
    path_ptr: *const u8,
    path_len: usize,
    source_ptr: *const u8,
    source_len: usize,
) -> TalkResult {
    Boundary::bytes(|| {
        let path = path_or_stdin(RawBytes::new(path_ptr, path_len, "path").string()?);
        let source = RawBytes::new(source_ptr, source_len, "source").string()?;
        talk::compiling::driver::compile_bytecode_from(
            "App",
            Source::in_memory(PathBuf::from(path), source),
        )
        .map_err(ApiError::failed)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_new() -> *mut TalkWorkspace {
    Box::into_raw(Box::new(TalkWorkspace::new()))
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_free(workspace: *mut TalkWorkspace) {
    // SAFETY: The pointer must have been returned by talk_workspace_new and
    // not already freed.
    unsafe { free_box(workspace) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_clear(workspace: *mut TalkWorkspace) -> TalkResult {
    Boundary::empty(|| {
        WorkspacePtr::new(workspace).get_mut()?.clear();
        Ok(())
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_set_document_utf8(
    workspace: *mut TalkWorkspace,
    id_ptr: *const u8,
    id_len: usize,
    path_ptr: *const u8,
    path_len: usize,
    version: i32,
    text_ptr: *const u8,
    text_len: usize,
) -> TalkResult {
    Boundary::empty(|| {
        let id = RawBytes::new(id_ptr, id_len, "id").string()?;
        let path = RawBytes::new(path_ptr, path_len, "path").string()?;
        let text = RawBytes::new(text_ptr, text_len, "text").string()?;
        WorkspacePtr::new(workspace)
            .get_mut()?
            .set_document(id, path, version, text);
        Ok(())
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_remove_document_utf8(
    workspace: *mut TalkWorkspace,
    id_ptr: *const u8,
    id_len: usize,
) -> TalkResult {
    Boundary::empty(|| {
        let id = RawBytes::new(id_ptr, id_len, "id").string()?;
        WorkspacePtr::new(workspace).get_mut()?.remove_document(&id);
        Ok(())
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_analyze(workspace: *mut TalkWorkspace) -> *mut TalkDiagnostics {
    Boundary::handle(
        || {
            let mut handle = WorkspacePtr::new(workspace);
            let workspace = handle.get_mut()?.analyze()?;
            Ok(diagnostic_records_from_workspace(workspace, None))
        },
        TalkDiagnostics::ok,
        TalkDiagnostics::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_diagnostics(
    workspace: *mut TalkWorkspace,
) -> *mut TalkDiagnostics {
    Boundary::handle(
        || {
            let mut handle = WorkspacePtr::new(workspace);
            let workspace = handle.get_mut()?.ensure_analysis()?;
            Ok(diagnostic_records_from_workspace(workspace, None))
        },
        TalkDiagnostics::ok,
        TalkDiagnostics::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_document_diagnostics_utf8(
    workspace: *mut TalkWorkspace,
    id_ptr: *const u8,
    id_len: usize,
) -> *mut TalkDiagnostics {
    Boundary::handle(
        || {
            let id = RawBytes::new(id_ptr, id_len, "id").string()?;
            let mut handle = WorkspacePtr::new(workspace);
            let workspace = handle.get_mut()?.ensure_analysis()?;
            Ok(diagnostic_records_from_workspace(workspace, Some(&id)))
        },
        TalkDiagnostics::ok,
        TalkDiagnostics::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_hover_utf8(
    workspace: *mut TalkWorkspace,
    id_ptr: *const u8,
    id_len: usize,
    byte_offset: u32,
) -> *mut TalkHover {
    Boundary::handle(
        || {
            let id = RawBytes::new(id_ptr, id_len, "id").string()?;
            let mut handle = WorkspacePtr::new(workspace);
            let workspace = handle.get_mut()?.ensure_analysis()?;
            Ok(talk::analysis::hover_at(workspace, &id, byte_offset).map(hover_record))
        },
        TalkHover::ok,
        TalkHover::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_completions_utf8(
    workspace: *mut TalkWorkspace,
    id_ptr: *const u8,
    id_len: usize,
    byte_offset: u32,
) -> *mut TalkCompletions {
    Boundary::handle(
        || {
            let id = RawBytes::new(id_ptr, id_len, "id").string()?;
            let mut handle = WorkspacePtr::new(workspace);
            let workspace = handle.get_mut()?.ensure_analysis()?;
            let items =
                talk::analysis::completion::complete_in_workspace(workspace, &id, byte_offset);
            Ok(completion_records(items))
        },
        TalkCompletions::ok,
        TalkCompletions::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_inlay_hints_utf8(
    workspace: *mut TalkWorkspace,
    id_ptr: *const u8,
    id_len: usize,
    start: u32,
    end: u32,
) -> *mut TalkInlayHints {
    Boundary::handle(
        || {
            let id = RawBytes::new(id_ptr, id_len, "id").string()?;
            let mut handle = WorkspacePtr::new(workspace);
            let workspace = handle.get_mut()?.ensure_analysis()?;
            let items =
                talk::analysis::ownership_inlay_hints(workspace, &id, TextRange::new(start, end));
            Ok(inlay_hint_records(items))
        },
        TalkInlayHints::ok,
        TalkInlayHints::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_goto_definition_utf8(
    workspace: *mut TalkWorkspace,
    id_ptr: *const u8,
    id_len: usize,
    byte_offset: u32,
) -> *mut TalkLocationResult {
    Boundary::handle(
        || {
            let id = RawBytes::new(id_ptr, id_len, "id").string()?;
            let mut handle = WorkspacePtr::new(workspace);
            let workspace = handle.get_mut()?;
            let analysis = workspace.ensure_analysis()?.clone();
            let core = workspace.ensure_core();
            Ok(
                talk::analysis::goto_definition(&analysis, core, &id, byte_offset)
                    .map(location_record),
            )
        },
        TalkLocationResult::ok,
        TalkLocationResult::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_rename_utf8(
    workspace: *mut TalkWorkspace,
    id_ptr: *const u8,
    id_len: usize,
    byte_offset: u32,
    new_name_ptr: *const u8,
    new_name_len: usize,
) -> *mut TalkWorkspaceEditResult {
    Boundary::handle(
        || {
            let id = RawBytes::new(id_ptr, id_len, "id").string()?;
            let new_name = RawBytes::new(new_name_ptr, new_name_len, "new_name").string()?;
            let mut handle = WorkspacePtr::new(workspace);
            let workspace = handle.get_mut()?.ensure_analysis()?;
            let edit = talk::analysis::rename_at(workspace, &id, byte_offset, &new_name);
            Ok(workspace_edit_records(edit))
        },
        TalkWorkspaceEditResult::ok,
        TalkWorkspaceEditResult::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_new() -> *mut TalkReplSession {
    Box::into_raw(Box::new(TalkReplSession {
        session: ReplSession::new(),
    }))
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_free(repl: *mut TalkReplSession) {
    // SAFETY: The pointer must have been returned by talk_repl_new and not
    // already freed.
    unsafe { free_box(repl) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_reset(repl: *mut TalkReplSession) -> TalkResult {
    Boundary::empty(|| {
        ReplPtr::new(repl).get_mut()?.session.clear();
        Ok(())
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_eval_utf8(
    repl: *mut TalkReplSession,
    input_ptr: *const u8,
    input_len: usize,
) -> *mut TalkEvalResult {
    Boundary::handle(
        || {
            let input = RawBytes::new(input_ptr, input_len, "input").string()?;
            Ok(ReplPtr::new(repl).get_mut()?.session.eval(&input))
        },
        TalkEvalResult::ok,
        TalkEvalResult::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_type_of_utf8(
    repl: *mut TalkReplSession,
    input_ptr: *const u8,
    input_len: usize,
) -> *mut TalkEvalResult {
    Boundary::handle(
        || {
            let input = RawBytes::new(input_ptr, input_len, "input").string()?;
            Ok(ReplPtr::new(repl).get_mut()?.session.type_of(&input))
        },
        TalkEvalResult::ok,
        TalkEvalResult::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_complete_utf8(
    repl: *mut TalkReplSession,
    input_ptr: *const u8,
    input_len: usize,
    byte_offset: usize,
) -> *mut TalkReplCompletions {
    Boundary::handle(
        || {
            let input = RawBytes::new(input_ptr, input_len, "input").string()?;
            Ok(ReplPtr::new(repl)
                .get_mut()?
                .session
                .complete_input(&input, byte_offset))
        },
        TalkReplCompletions::ok,
        TalkReplCompletions::err,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_needs_more_input_utf8(input_ptr: *const u8, input_len: usize) -> bool {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let input = RawBytes::new(input_ptr, input_len, "input").string()?;
        Ok::<bool, ApiError>(talk::repl::needs_more_input(&input))
    }));
    matches!(result, Ok(Ok(true)))
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_diagnostics_status(ptr: *const TalkDiagnostics) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_diagnostics_error(ptr: *const TalkDiagnostics) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_diagnostics_count(ptr: *const TalkDiagnostics) -> usize {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| handle.items.len())
            .unwrap_or(0)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_diagnostics_get(
    ptr: *const TalkDiagnostics,
    index: usize,
) -> TalkDiagnosticView {
    // SAFETY: The pointer is only read if non-null.
    unsafe { diagnostic_view(handle_ref(ptr).and_then(|handle| handle.items.get(index))) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_diagnostics_free(ptr: *mut TalkDiagnostics) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_hover_status(ptr: *const TalkHover) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_hover_error(ptr: *const TalkHover) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_hover_value(ptr: *const TalkHover) -> TalkHoverView {
    // SAFETY: The pointer is only read if non-null.
    let Some(handle) = (unsafe { handle_ref(ptr) }) else {
        return TalkHoverView {
            present: OPTIONAL_ABSENT,
            contents: TalkStringRef::empty(),
            range: TalkTextRange::empty(),
        };
    };
    match handle.value.as_ref() {
        Some(value) => TalkHoverView {
            present: OPTIONAL_PRESENT,
            contents: TalkStringRef::from_str(&value.contents),
            range: TalkTextRange::from_range(value.range),
        },
        None => TalkHoverView {
            present: OPTIONAL_ABSENT,
            contents: TalkStringRef::empty(),
            range: TalkTextRange::empty(),
        },
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_hover_free(ptr: *mut TalkHover) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_completions_status(ptr: *const TalkCompletions) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_completions_error(ptr: *const TalkCompletions) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_completions_count(ptr: *const TalkCompletions) -> usize {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| handle.items.len())
            .unwrap_or(0)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_completions_get(
    ptr: *const TalkCompletions,
    index: usize,
) -> TalkCompletionView {
    // SAFETY: The pointer is only read if non-null.
    let record = unsafe { handle_ref(ptr).and_then(|handle| handle.items.get(index)) };
    match record {
        Some(record) => TalkCompletionView {
            label: TalkStringRef::from_str(&record.label),
            kind: record.kind,
            detail: TalkOptionalStringRef::from_option(record.detail.as_deref()),
            insert_text: TalkOptionalStringRef::from_option(record.insert_text.as_deref()),
            insert_text_is_snippet: record.insert_text_is_snippet,
        },
        None => TalkCompletionView {
            label: TalkStringRef::empty(),
            kind: COMPLETION_NONE,
            detail: TalkOptionalStringRef::none(),
            insert_text: TalkOptionalStringRef::none(),
            insert_text_is_snippet: 0,
        },
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_completions_free(ptr: *mut TalkCompletions) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_inlay_hints_status(ptr: *const TalkInlayHints) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_inlay_hints_error(ptr: *const TalkInlayHints) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_inlay_hints_count(ptr: *const TalkInlayHints) -> usize {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| handle.items.len())
            .unwrap_or(0)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_inlay_hints_get(
    ptr: *const TalkInlayHints,
    index: usize,
) -> TalkInlayHintView {
    // SAFETY: The pointer is only read if non-null.
    let record = unsafe { handle_ref(ptr).and_then(|handle| handle.items.get(index)) };
    match record {
        Some(record) => TalkInlayHintView {
            position: record.position,
            label: TalkStringRef::from_str(&record.label),
            tooltip: TalkStringRef::from_str(&record.tooltip),
            kind: record.kind,
        },
        None => TalkInlayHintView {
            position: 0,
            label: TalkStringRef::empty(),
            tooltip: TalkStringRef::empty(),
            kind: 0,
        },
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_inlay_hints_free(ptr: *mut TalkInlayHints) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_highlight_tokens_status(ptr: *const TalkHighlightTokens) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_highlight_tokens_error(ptr: *const TalkHighlightTokens) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_highlight_tokens_count(ptr: *const TalkHighlightTokens) -> usize {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| handle.items.len())
            .unwrap_or(0)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_highlight_tokens_get(
    ptr: *const TalkHighlightTokens,
    index: usize,
) -> TalkHighlightTokenView {
    // SAFETY: The pointer is only read if non-null.
    let record = unsafe { handle_ref(ptr).and_then(|handle| handle.items.get(index)) };
    match record {
        Some(record) => TalkHighlightTokenView {
            kind: record.kind,
            start: record.start,
            end: record.end,
        },
        None => TalkHighlightTokenView {
            kind: 0,
            start: 0,
            end: 0,
        },
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_highlight_tokens_free(ptr: *mut TalkHighlightTokens) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_location_status(ptr: *const TalkLocationResult) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_location_error(ptr: *const TalkLocationResult) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_location_value(ptr: *const TalkLocationResult) -> TalkLocationView {
    // SAFETY: The pointer is only read if non-null.
    let Some(handle) = (unsafe { handle_ref(ptr) }) else {
        return TalkLocationView {
            present: OPTIONAL_ABSENT,
            document: TalkStringRef::empty(),
            range: TalkTextRange::empty(),
        };
    };
    match handle.value.as_ref() {
        Some(value) => TalkLocationView {
            present: OPTIONAL_PRESENT,
            document: TalkStringRef::from_str(&value.document),
            range: TalkTextRange::from_range(value.range),
        },
        None => TalkLocationView {
            present: OPTIONAL_ABSENT,
            document: TalkStringRef::empty(),
            range: TalkTextRange::empty(),
        },
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_location_free(ptr: *mut TalkLocationResult) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_edit_status(ptr: *const TalkWorkspaceEditResult) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_edit_error(ptr: *const TalkWorkspaceEditResult) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_edit_document_count(ptr: *const TalkWorkspaceEditResult) -> usize {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| handle.documents.len())
            .unwrap_or(0)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_edit_document(
    ptr: *const TalkWorkspaceEditResult,
    document_index: usize,
) -> TalkDocumentEditView {
    // SAFETY: The pointer is only read if non-null.
    let record = unsafe { handle_ref(ptr).and_then(|handle| handle.documents.get(document_index)) };
    match record {
        Some(record) => TalkDocumentEditView {
            document: TalkStringRef::from_str(&record.document),
            edit_count: record.edits.len(),
        },
        None => TalkDocumentEditView {
            document: TalkStringRef::empty(),
            edit_count: 0,
        },
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_edit_text_edit(
    ptr: *const TalkWorkspaceEditResult,
    document_index: usize,
    edit_index: usize,
) -> TalkTextEditView {
    // SAFETY: The pointer is only read if non-null.
    let record = unsafe {
        handle_ref(ptr)
            .and_then(|handle| handle.documents.get(document_index))
            .and_then(|document| document.edits.get(edit_index))
    };
    match record {
        Some(record) => TalkTextEditView {
            range: TalkTextRange::from_range(record.range),
            replacement: TalkStringRef::from_str(&record.replacement),
        },
        None => TalkTextEditView {
            range: TalkTextRange::empty(),
            replacement: TalkStringRef::empty(),
        },
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_workspace_edit_free(ptr: *mut TalkWorkspaceEditResult) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_status(ptr: *const TalkEvalResult) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_error(ptr: *const TalkEvalResult) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_kind(ptr: *const TalkEvalResult) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { handle_ref(ptr).map(|handle| handle.kind).unwrap_or(0) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_stdout(ptr: *const TalkEvalResult) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| TalkStringRef::from_str(&handle.stdout))
            .unwrap_or_else(TalkStringRef::empty)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_stderr(ptr: *const TalkEvalResult) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| TalkStringRef::from_str(&handle.stderr))
            .unwrap_or_else(TalkStringRef::empty)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_value(ptr: *const TalkEvalResult) -> TalkOptionalStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| TalkOptionalStringRef::from_option(handle.value.as_deref()))
            .unwrap_or_else(TalkOptionalStringRef::none)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_source(ptr: *const TalkEvalResult) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| TalkStringRef::from_str(&handle.source))
            .unwrap_or_else(TalkStringRef::empty)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_message(ptr: *const TalkEvalResult) -> TalkOptionalStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| TalkOptionalStringRef::from_option(handle.message.as_deref()))
            .unwrap_or_else(TalkOptionalStringRef::none)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_diagnostic_count(ptr: *const TalkEvalResult) -> usize {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| handle.diagnostics.len())
            .unwrap_or(0)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_diagnostic(
    ptr: *const TalkEvalResult,
    index: usize,
) -> TalkDiagnosticView {
    // SAFETY: The pointer is only read if non-null.
    unsafe { diagnostic_view(handle_ref(ptr).and_then(|handle| handle.diagnostics.get(index))) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_eval_result_free(ptr: *mut TalkEvalResult) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_test_result_status(ptr: *const TalkTestResult) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_test_result_error(ptr: *const TalkTestResult) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_test_result_kind(ptr: *const TalkTestResult) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { handle_ref(ptr).map(|handle| handle.kind).unwrap_or(0) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_test_result_output(ptr: *const TalkTestResult) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| TalkStringRef::from_str(&handle.output))
            .unwrap_or_else(TalkStringRef::empty)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_test_result_failures(ptr: *const TalkTestResult) -> i64 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { handle_ref(ptr).map(|handle| handle.failures).unwrap_or(0) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_test_result_free(ptr: *mut TalkTestResult) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_completions_status(ptr: *const TalkReplCompletions) -> i32 {
    // SAFETY: The pointer is only read if non-null.
    unsafe { status_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_completions_error(ptr: *const TalkReplCompletions) -> TalkStringRef {
    // SAFETY: The pointer is only read if non-null.
    unsafe { error_of(handle_ref(ptr).map(|handle| &handle.status)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_completions_start(ptr: *const TalkReplCompletions) -> usize {
    // SAFETY: The pointer is only read if non-null.
    unsafe { handle_ref(ptr).map(|handle| handle.start).unwrap_or(0) }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_completions_count(ptr: *const TalkReplCompletions) -> usize {
    // SAFETY: The pointer is only read if non-null.
    unsafe {
        handle_ref(ptr)
            .map(|handle| handle.items.len())
            .unwrap_or(0)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_completions_get(
    ptr: *const TalkReplCompletions,
    index: usize,
) -> TalkReplCompletionView {
    // SAFETY: The pointer is only read if non-null.
    let record = unsafe { handle_ref(ptr).and_then(|handle| handle.items.get(index)) };
    match record {
        Some(record) => TalkReplCompletionView {
            display: TalkStringRef::from_str(&record.display),
            replacement: TalkStringRef::from_str(&record.replacement),
        },
        None => TalkReplCompletionView {
            display: TalkStringRef::empty(),
            replacement: TalkStringRef::empty(),
        },
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn talk_repl_completions_free(ptr: *mut TalkReplCompletions) {
    // SAFETY: The pointer was allocated by this crate or is null.
    unsafe { free_box(ptr) };
}
