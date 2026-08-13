struct DocumentWorkWakeEvent {
    uri: async_lsp::lsp_types::Url,
    generation: u64,
}

use async_lsp::LanguageClient;
use async_lsp::lsp_types::{
    CodeActionProviderCapability, CompletionOptions, Diagnostic, DiagnosticSeverity, MessageType,
    NumberOrString, Position, Range, SemanticTokens, SemanticTokensResult, ShowMessageParams,
    TextDocumentSyncCapability, TextDocumentSyncKind, TextDocumentSyncOptions,
    TextDocumentSyncSaveOptions, TextEdit,
};
use async_lsp::{
    ClientSocket,
    client_monitor::ClientProcessMonitorLayer,
    concurrency::ConcurrencyLayer,
    lsp_types::{
        CompletionResponse, GotoDefinitionResponse, HoverContents, HoverProviderCapability,
        InitializeParams, InitializeResult, MarkupContent, MarkupKind, OneOf,
        PublishDiagnosticsParams, Range as LspRange, SemanticTokensFullOptions,
        SemanticTokensLegend, SemanticTokensOptions, SemanticTokensServerCapabilities,
        ServerCapabilities, TextDocumentItem, Url, WorkspaceFolder, notification, request,
    },
    panic::CatchUnwindLayer,
    router::Router,
    server::LifecycleLayer,
    tracing::TracingLayer,
};
use rustc_hash::FxHashMap;
use std::any::Any;
use std::fs::File;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::{
    ops::ControlFlow,
    path::PathBuf,
    time::{Duration, Instant},
};
use tokio::spawn;
use tower::ServiceBuilder;
use tracing::Level;

use crate::analysis::{
    Diagnostic as AnalysisDiagnostic, DiagnosticSeverity as AnalysisSeverity, DocumentId,
    DocumentInput, Workspace as AnalysisWorkspace, completion as analysis_completion,
};
use crate::lsp::code_actions::compute_code_actions;
#[cfg(test)]
use crate::lsp::code_actions::{code_action_diagnostic, separator_list_item_removal_range};
use crate::lsp::goto_definition::{LspGoto, goto_definition};
use crate::lsp::rename::rename_at;
use crate::lsp::semantic_tokens::collect;
use crate::lsp::{completion, document::Document, semantic_tokens::TOKEN_TYPES};

#[allow(deprecated)]
fn workspace_roots_from_initialize(params: &InitializeParams) -> Vec<PathBuf> {
    let mut roots: Vec<PathBuf> = vec![];

    if let Some(folders) = params.workspace_folders.as_ref() {
        for WorkspaceFolder { uri, .. } in folders {
            if let Ok(path) = uri.to_file_path() {
                roots.push(path);
            }
        }
    }

    if roots.is_empty() {
        if let Some(uri) = params.root_uri.as_ref() {
            if let Ok(path) = uri.to_file_path() {
                roots.push(path);
            }
        } else if let Some(path) = params.root_path.as_ref() {
            roots.push(PathBuf::from(path));
        }
    }

    roots
}

const DOCUMENT_QUIET_PERIOD: Duration = Duration::from_millis(200);

struct ServerState {
    client: ClientSocket,
    documents: FxHashMap<Url, Document>,
    next_work_generation: u64,
    pending_document_work: FxHashMap<Url, PendingDocumentWork>,
    roots: FxHashMap<PathBuf, RootState>,
    core: Option<Arc<AnalysisWorkspace>>,
    core_build_requested: bool,
    /// Stdlib module navigation workspaces (goto-definition targets),
    /// built off-loop and cached until a stdlib source changes.
    stdlib_modules: FxHashMap<crate::compiling::module::ModuleId, Arc<AnalysisWorkspace>>,
    stdlib_modules_requested: rustc_hash::FxHashSet<crate::compiling::module::ModuleId>,
    workspace_roots: Vec<PathBuf>,
    analysis: std::sync::mpsc::Sender<AnalysisJob>,
}

/// A rebuild request for one analysis root. Analysis is CPU-heavy
/// (native-frontend parses, name resolution, type checking), so it
/// never runs on the server's event loop: this job goes to the
/// analysis worker thread and the result returns as a loopback event.
/// Request handlers serve the latest completed snapshot, stale or not.
struct WorkspaceBuildJob {
    root: PathBuf,
    focus: Url,
    /// Open .tlk documents relevant to the root (those under it, plus
    /// the focus): everything else the worker reads from disk.
    open_docs: Vec<OpenDocument>,
    /// An open/close/watched-file event happened since the last build:
    /// the worker's cached file inventory is stale and re-walks once.
    inventory_changed: bool,
}

struct OpenDocument {
    uri: Url,
    version: i32,
    text: String,
}

enum AnalysisJob {
    Workspace(WorkspaceBuildJob),
    /// The name-resolved core workspace goto-definition navigates into,
    /// built once per session and cached.
    Core,
    /// A stdlib module's navigation workspace (goto-definition
    /// target), built on demand and cached until a stdlib source
    /// changes.
    StdlibModule(crate::compiling::module::ModuleId),
}

struct WorkspaceBuildEvent {
    root: PathBuf,
    focus: Url,
    /// Ok(None) means nothing analyzable remained (e.g. the last
    /// document closed); Err carries the panic payload message.
    result: Result<Option<Arc<AnalysisWorkspace>>, String>,
    /// Semantic tokens for the focus document, computed off-loop from
    /// the same text snapshot the build used.
    semantic_tokens: Option<SemanticTokensResult>,
}

struct CoreBuildEvent(Option<Arc<AnalysisWorkspace>>);

struct StdlibModuleBuildEvent {
    module_id: crate::compiling::module::ModuleId,
    workspace: Option<Arc<AnalysisWorkspace>>,
}

/// Per-root editor state (CLEAN-01). The workspace snapshot is whatever
/// the analysis worker last completed — served stale by request
/// handlers so typing never waits on a build. Freshness is
/// demand-driven: document events flag the root dirty and a background
/// build publishes diagnostics when it lands.
#[derive(Default)]
struct RootState {
    workspace: Option<Arc<AnalysisWorkspace>>,
    build_in_flight: bool,
    /// A rebuild was requested while one was running: the latest
    /// requester's focus wins, sent when the in-flight build
    /// completes. The focus matters — the document set (a stdlib
    /// session's module) and semantic tokens key on it.
    build_pending: Option<Url>,
    /// Bumped by every event that can affect the root's analysis; the
    /// failure backoff keys on it so a new edit retries immediately.
    revision: u64,
    /// The file list may have changed (open/close/watched): the next
    /// build re-walks instead of reusing the worker's inventory.
    /// Content edits to open documents do not set this: their versions
    /// travel with the build job, not the walk.
    inventory_dirty: bool,
    backoff: Option<WorkspaceAnalysisBackoff>,
}

struct CachedPackageContext {
    /// Stamps of `package.tlk` and `package.lock` when the context was
    /// built.
    stamp: (i32, i32),
    /// `None` when the root has no usable manifest/lock (or the locked
    /// graph failed to load): the session falls back to the inferred,
    /// dependency-free source root.
    context: Option<crate::compiling::package::PackageCompileContext>,
}

#[derive(Clone, Copy)]
struct PendingDocumentWork {
    generation: u64,
    ready_at: Instant,
}

impl ServerState {
    fn queue_document_work(&mut self, uri: Url, now: Instant) -> u64 {
        self.next_work_generation = self
            .next_work_generation
            .checked_add(1)
            .expect("document work generation exhausted");
        let generation = self.next_work_generation;
        self.pending_document_work.insert(
            uri,
            PendingDocumentWork {
                generation,
                ready_at: now + DOCUMENT_QUIET_PERIOD,
            },
        );
        generation
    }

    fn schedule_document_work(&mut self, uri: Url) {
        let generation = self.queue_document_work(uri.clone(), Instant::now());
        let client = self.client.clone();
        spawn(async move {
            tokio::time::sleep(DOCUMENT_QUIET_PERIOD).await;
            let _ = client.emit(DocumentWorkWakeEvent { uri, generation });
        });
    }

    fn take_document_work(&mut self, uri: &Url, generation: u64, now: Instant) -> bool {
        let is_ready = self
            .pending_document_work
            .get(uri)
            .is_some_and(|work| work.generation == generation && work.ready_at <= now);
        if is_ready {
            self.pending_document_work.remove(uri);
        }
        is_ready
    }

    /// Flag the root containing `uri` dirty (CLEAN-01): only that
    /// root's analysis is affected. `inventory_changed` additionally
    /// forces a one-time re-walk of the root's file list on the next
    /// build (opens, closes, and watched-file events; plain edits to
    /// open documents do not change the file list).
    fn invalidate_root(&mut self, uri: &Url, inventory_changed: bool) {
        let Some(root) = analysis_root_for_uri(self, uri) else {
            return;
        };
        let root_state = self.roots.entry(root).or_default();
        root_state.revision = root_state.revision.wrapping_add(1);
        if inventory_changed {
            root_state.inventory_dirty = true;
        }
    }
}

struct WorkspaceAnalysisBackoff {
    revision: u64,
    consecutive_failures: u32,
    retry_at: Instant,
}

impl WorkspaceAnalysisBackoff {
    const MAX_DELAY_SECS: u64 = 30;

    fn after_failure(revision: u64, previous: Option<&Self>, now: Instant) -> Self {
        let consecutive_failures = previous
            .filter(|failure| failure.revision == revision)
            .map_or(1, |failure| failure.consecutive_failures.saturating_add(1));
        let exponent = consecutive_failures.saturating_sub(1).min(5);
        let delay_secs = (1_u64 << exponent).min(Self::MAX_DELAY_SECS);

        Self {
            revision,
            consecutive_failures,
            retry_at: now + Duration::from_secs(delay_secs),
        }
    }

    fn blocks(&self, revision: u64, now: Instant) -> bool {
        self.revision == revision && now < self.retry_at
    }
}

fn panic_payload_message(payload: &(dyn Any + Send)) -> String {
    if let Some(message) = payload.downcast_ref::<&'static str>() {
        return (*message).to_string();
    }
    if let Some(message) = payload.downcast_ref::<String>() {
        return message.clone();
    }
    "unknown panic payload".to_string()
}

fn report_lsp_internal_error(
    state: &mut ServerState,
    uri: Option<&Url>,
    context: &str,
    detail: &str,
) {
    let message = format!(
        "Talk LSP internal error while {context}: {detail}. The server recovered; results may be incomplete until the next edit."
    );
    tracing::error!("{message}");

    let _ = state.client.show_message(ShowMessageParams {
        typ: MessageType::ERROR,
        message: message.clone(),
    });

    let Some(uri) = uri else {
        return;
    };

    let range = state
        .documents
        .get(uri)
        .and_then(|document| document.range_of_byte_span(0, 0))
        .unwrap_or_else(|| Range::new(Position::new(0, 0), Position::new(0, 0)));
    let version = state.documents.get(uri).map(|document| document.version);

    let diagnostic = Diagnostic {
        range,
        severity: Some(DiagnosticSeverity::ERROR),
        source: Some("talk-lsp".to_string()),
        message,
        ..Diagnostic::default()
    };
    let _ = state.client.publish_diagnostics(PublishDiagnosticsParams {
        uri: uri.clone(),
        diagnostics: vec![diagnostic],
        version,
    });
}

fn recover_lsp_result<T>(
    state: &mut ServerState,
    uri: Option<&Url>,
    context: &str,
    f: impl FnOnce() -> T,
) -> Result<T, ()> {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(value) => Ok(value),
        Err(payload) => {
            report_lsp_internal_error(
                state,
                uri,
                context,
                &panic_payload_message(payload.as_ref()),
            );
            Err(())
        }
    }
}

fn recover_lsp<T>(
    state: &mut ServerState,
    uri: Option<&Url>,
    context: &str,
    fallback: T,
    f: impl FnOnce() -> T,
) -> T {
    match recover_lsp_result(state, uri, context, f) {
        Ok(value) => value,
        Err(()) => fallback,
    }
}

pub async fn start() {
    let (server, _) = async_lsp::MainLoop::new_server(|client| {
        // The analysis worker: rebuilds are CPU-heavy and run off the
        // event loop. Jobs go over a std channel; results come back as
        // loopback events through the client socket (both thread-safe).
        let (analysis_tx, analysis_rx) = std::sync::mpsc::channel::<AnalysisJob>();
        let worker_client = client.clone();
        if let Err(err) = std::thread::Builder::new()
            .name("talk-analysis".to_string())
            .spawn(move || run_analysis_worker(worker_client, analysis_rx))
        {
            eprintln!("Talk LSP could not spawn the analysis worker: {err}");
        }

        let mut router = Router::new(ServerState {
            client: client.clone(),
            documents: Default::default(),
            next_work_generation: 0,
            pending_document_work: Default::default(),
            roots: Default::default(),
            core: None,
            core_build_requested: false,
            stdlib_modules: Default::default(),
            stdlib_modules_requested: Default::default(),
            workspace_roots: Default::default(),
            analysis: analysis_tx,
        });

        router
            .request::<request::Initialize, _>(|st, params| {
                tracing::trace!("Initialize with {params:?}");

                let roots = workspace_roots_from_initialize(&params);
                if !roots.is_empty() {
                    tracing::info!("workspace roots: {roots:?}");
                }
                st.workspace_roots = roots;
                st.roots.clear();

                async move {
                    Ok(InitializeResult {
                        capabilities: ServerCapabilities {
                            definition_provider: Some(OneOf::Left(true)),
                            hover_provider: Some(HoverProviderCapability::Simple(true)),
                            rename_provider: Some(OneOf::Left(true)),
                            completion_provider: Some(completion_options()),
                            document_formatting_provider: Some(OneOf::Left(true)),
                            code_action_provider: Some(CodeActionProviderCapability::Options(
                                async_lsp::lsp_types::CodeActionOptions {
                                    code_action_kinds: Some(vec![
                                        async_lsp::lsp_types::CodeActionKind::QUICKFIX,
                                        async_lsp::lsp_types::CodeActionKind::SOURCE_FIX_ALL,
                                    ]),
                                    ..Default::default()
                                },
                            )),
                            semantic_tokens_provider: Some(
                                SemanticTokensServerCapabilities::SemanticTokensOptions(
                                    SemanticTokensOptions {
                                        legend: SemanticTokensLegend {
                                            token_types: TOKEN_TYPES.to_vec(),
                                            token_modifiers: vec![],
                                        },
                                        full: Some(SemanticTokensFullOptions::Bool(true)),
                                        range: Some(false),
                                        ..Default::default()
                                    },
                                ),
                            ),
                            text_document_sync: Some(TextDocumentSyncCapability::Options(
                                TextDocumentSyncOptions {
                                    open_close: Some(true),
                                    change: Some(TextDocumentSyncKind::INCREMENTAL),
                                    will_save: None,
                                    will_save_wait_until: None,
                                    save: Some(TextDocumentSyncSaveOptions::Supported(true)),
                                },
                            )),
                            ..ServerCapabilities::default()
                        },
                        server_info: None,
                    })
                }
            })
            .notification::<notification::DidOpenTextDocument>(|state, params| {
                let TextDocumentItem {
                    uri: document_url,
                    version,
                    text,
                    ..
                } = params.text_document;

                tracing::info!("did open {document_url}");

                state
                    .documents
                    .insert(document_url.clone(), Document::new(version, text));
                state.schedule_document_work(document_url.clone());
                state.invalidate_root(&document_url, true);
                std::ops::ControlFlow::Continue(())
            })
            .notification::<notification::DidChangeTextDocument>(|state, params| {
                let uri = params.text_document.uri.clone();
                let version = params.text_document.version;

                tracing::info!("did change {uri}");

                let mut panic_payload = None;
                if let Some(document) = state.documents.get_mut(&uri) {
                    if let Err(payload) = catch_unwind(AssertUnwindSafe(|| {
                        document.apply_changes(&params.content_changes);
                    })) {
                        panic_payload = Some(payload);
                    }
                    document.version = version;
                    state.schedule_document_work(uri.clone());
                    state.invalidate_root(&uri, false);
                    invalidate_stdlib_module_workspaces(state, &uri);
                }
                if let Some(payload) = panic_payload {
                    report_lsp_internal_error(
                        state,
                        Some(&uri),
                        "applying document changes",
                        &panic_payload_message(payload.as_ref()),
                    );
                }

                std::ops::ControlFlow::Continue(())
            })
            .notification::<notification::DidCloseTextDocument>(|state, params| {
                let document_url = params.text_document.uri;
                tracing::info!("did close {document_url}");

                state.documents.remove(&document_url);
                state.pending_document_work.remove(&document_url);
                state.invalidate_root(&document_url, true);
                invalidate_stdlib_module_workspaces(state, &document_url);

                if is_tlk_uri(&document_url) {
                    // Rebuild from disk state off-loop; the completion
                    // event republishes (or clears) diagnostics.
                    request_workspace_build(state, &document_url);
                }

                std::ops::ControlFlow::Continue(())
            })
            .request::<request::Formatting, _>(|st, params| {
                let uri = params.text_document.uri;
                let text = st.documents.get(&uri).map(|document| document.text.clone());
                let result = if let Some(text) = text {
                    let formatted =
                        recover_lsp(st, Some(&uri), "formatting document", None, || {
                            Some(crate::compiling::frontend::format_string(&text))
                        });
                    if let Some(formatted) = formatted {
                        let newline_count = text.matches('\n').count();
                        let ends_with_newline = text.ends_with('\n');
                        let last_line = newline_count as u32;
                        let last_char = if ends_with_newline {
                            0
                        } else {
                            // LSP positions count UTF-16 code units, not bytes.
                            text.rsplit('\n')
                                .next()
                                .map(|s| s.encode_utf16().count())
                                .unwrap_or_default() as u32
                        };

                        Ok(Some(vec![TextEdit::new(
                            Range::new(Position::new(0, 0), Position::new(last_line, last_char)),
                            formatted,
                        )]))
                    } else {
                        Ok(None)
                    }
                } else {
                    Ok(None)
                };

                async move { result }
            })
            .request::<request::SemanticTokensFullRequest, _>(|st, params| {
                let uri = params.text_document.uri;
                let result = if let Some(result) = st.documents.get(&uri)
                    && let Some(doc) = result.semantic_tokens.clone()
                {
                    Ok(Some(doc))
                } else {
                    Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
                        result_id: None,
                        data: vec![],
                    })))
                };

                async move { result }
            })
            .request::<request::Rename, _>(|st, params| {
                let uri = params.text_document_position.text_document.uri.clone();
                let position = params.text_document_position.position;
                let new_name = params.new_name.clone();

                let byte_offset = st
                    .documents
                    .get(&uri)
                    .and_then(|document| document.byte_offset(position).map(|o| o as u32));

                let workspace = snapshot_workspace(st, &uri);
                let result = match (byte_offset, workspace) {
                    (Some(byte_offset), Some(workspace)) => {
                        recover_lsp(st, Some(&uri), "renaming symbol", None, || {
                            rename_at(&workspace, &uri, byte_offset, &new_name)
                        })
                    }
                    _ => None,
                };

                async move { Ok(result) }
            })
            .request::<request::HoverRequest, _>(|st, params| {
                let uri = params
                    .text_document_position_params
                    .text_document
                    .uri
                    .clone();
                let position = params.text_document_position_params.position;
                let byte_offset = st
                    .documents
                    .get(&uri)
                    .and_then(|document| document.byte_offset(position).map(|o| o as u32));
                let workspace = snapshot_workspace(st, &uri);
                let result = match (byte_offset, workspace) {
                    (Some(byte_offset), Some(workspace)) => {
                        recover_lsp(st, Some(&uri), "computing hover", None, || {
                            hover_at_lsp(&workspace, &uri, byte_offset)
                        })
                    }
                    _ => None,
                };
                async move { Ok(result) }
            })
            .request::<request::GotoDefinition, _>(|st, params| {
                let uri = params
                    .text_document_position_params
                    .text_document
                    .uri
                    .clone();
                let position = params.text_document_position_params.position;

                let byte_offset = st
                    .documents
                    .get(&uri)
                    .and_then(|document| document.byte_offset(position).map(|o| o as u32));

                let workspace = snapshot_workspace(st, &uri);
                let core = core_snapshot(st);
                let stdlib_modules = st.stdlib_modules.clone();
                let mut needed_module = None;
                let result = match (byte_offset, workspace) {
                    (Some(byte_offset), Some(workspace)) => {
                        recover_lsp(st, Some(&uri), "resolving definition", None, || {
                            match goto_definition(
                                &workspace,
                                core.as_deref(),
                                &stdlib_modules,
                                &uri,
                                byte_offset,
                            ) {
                                LspGoto::Found(location) => {
                                    Some(GotoDefinitionResponse::Scalar(location))
                                }
                                LspGoto::NeedsModule(module_id) => {
                                    needed_module = Some(module_id);
                                    None
                                }
                                LspGoto::NotFound => None,
                            }
                        })
                    }
                    _ => None,
                };
                if let Some(module_id) = needed_module {
                    // The target stdlib module's navigation workspace
                    // builds off-loop; the next goto finds it cached.
                    request_stdlib_module(st, module_id);
                }

                async move { Ok(result) }
            })
            .request::<request::Completion, _>(|st, params| {
                let uri = params.text_document_position.text_document.uri.clone();
                let position = params.text_document_position.position;

                let byte_offset = st
                    .documents
                    .get(&uri)
                    .and_then(|document| document.byte_offset(position).map(|o| o as u32));
                let workspace = snapshot_workspace(st, &uri);
                let result = match (byte_offset, workspace) {
                    (Some(byte_offset), Some(workspace)) => recover_lsp(
                        st,
                        Some(&uri),
                        "computing completions",
                        Some(CompletionResponse::Array(vec![])),
                        || {
                            let document_id = document_id_for_uri(&uri);
                            let items = analysis_completion::complete_in_workspace(
                                &workspace,
                                &document_id,
                                byte_offset,
                            );
                            let Some(document_index) = workspace.document_index(&document_id)
                            else {
                                return Some(CompletionResponse::Array(vec![]));
                            };
                            let Some(text) = workspace.texts.get(document_index) else {
                                return Some(CompletionResponse::Array(vec![]));
                            };
                            let Some(roots) = workspace
                                .asts
                                .get(document_index)
                                .and_then(|ast| ast.as_ref())
                                .map(|ast| ast.roots.as_slice())
                            else {
                                return Some(CompletionResponse::Array(vec![]));
                            };
                            let items = completion::to_lsp_items(items, text.text(), roots);
                            Some(CompletionResponse::Array(items))
                        },
                    ),
                    (Some(_), None) => Some(CompletionResponse::Array(vec![])),
                    _ => None,
                };

                async move { Ok(result) }
            })
            .request::<request::Shutdown, _>(|_, _| async move { Ok(()) })
            .notification::<notification::Exit>(|_, _| ControlFlow::Break(Ok(())))
            .notification::<notification::Initialized>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::DidChangeConfiguration>(|_, _| ControlFlow::Continue(()))
            .request::<request::CodeActionRequest, _>(|state, params| {
                let uri = params.text_document.uri.clone();
                let range = params.range;
                let workspace = snapshot_workspace(state, &uri);
                let actions = if let Some(workspace) = workspace {
                    recover_lsp(
                        state,
                        Some(&uri),
                        "computing code actions",
                        Vec::new(),
                        || {
                            let document_id = document_id_for_uri(&uri);
                            compute_code_actions(&workspace, &document_id, &uri, range)
                        },
                    )
                } else {
                    Vec::new()
                };
                let result = if actions.is_empty() {
                    None
                } else {
                    Some(actions)
                };

                async move { Ok(result) }
            })
            .notification::<notification::DidSaveTextDocument>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::DidChangeWatchedFiles>(|state, params| {
                let mut diagnostics_workspaces: FxHashMap<PathBuf, Url> = FxHashMap::default();

                for change in params.changes {
                    let uri = change.uri;
                    if !is_tlk_uri(&uri) {
                        continue;
                    }

                    if let Some(root) = analysis_root_for_uri(state, &uri) {
                        diagnostics_workspaces
                            .entry(root)
                            .or_insert_with(|| uri.clone());
                    }
                    if state.documents.contains_key(&uri) {
                        state.schedule_document_work(uri.clone());
                    }
                    // The file list or a disk stamp may have changed:
                    // invalidate only the containing root (CLEAN-01).
                    state.invalidate_root(&uri, true);
                    invalidate_stdlib_module_workspaces(state, &uri);
                }

                for focus_uri in diagnostics_workspaces.values() {
                    // Rebuild off-loop; completion events publish.
                    request_workspace_build(state, focus_uri);
                }

                ControlFlow::Continue(())
            })
            .event::<DocumentWorkWakeEvent>(|state, event| {
                if !state.take_document_work(&event.uri, event.generation, Instant::now()) {
                    return std::ops::ControlFlow::Continue(());
                }

                let document_url = event.uri;
                if is_tlk_uri(&document_url) {
                    // The debounced rebuild runs on the analysis worker;
                    // diagnostics and semantic tokens ride back on the
                    // completion event.
                    request_workspace_build(state, &document_url);
                    return std::ops::ControlFlow::Continue(());
                }

                // Non-talk documents never build a workspace; their
                // tokens are cheap enough to collect inline.
                let semantic_tokens = if let Some(text) = state
                    .documents
                    .get(&document_url)
                    .map(|document| document.text.clone())
                {
                    recover_lsp(
                        state,
                        Some(&document_url),
                        "collecting semantic tokens",
                        None,
                        || {
                            Some(SemanticTokensResult::Tokens(SemanticTokens {
                                result_id: None,
                                data: collect(text),
                            }))
                        },
                    )
                } else {
                    None
                };
                let needs_refresh = if let Some(document) = state.documents.get_mut(&document_url) {
                    document.semantic_tokens = semantic_tokens;
                    true
                } else {
                    false
                };

                if needs_refresh {
                    let client = state.client.clone();
                    spawn(async move {
                        client
                            .request::<request::SemanticTokensRefresh>(())
                            .await
                            .ok();
                    });
                }

                std::ops::ControlFlow::Continue(())
            })
            .event::<WorkspaceBuildEvent>(|state, event| {
                let WorkspaceBuildEvent {
                    root,
                    focus,
                    result,
                    semantic_tokens,
                } = event;

                let mut root_state = state.roots.remove(&root).unwrap_or_default();
                root_state.build_in_flight = false;

                match result {
                    Ok(Some(workspace)) => {
                        root_state.backoff = None;
                        root_state.workspace = Some(workspace.clone());
                        publish_workspace_diagnostics(state, &workspace);
                    }
                    Ok(None) => {
                        // Nothing analyzable remained (e.g. the last
                        // document closed): clear the focus.
                        root_state.backoff = None;
                        let _ = state.client.publish_diagnostics(PublishDiagnosticsParams {
                            uri: focus.clone(),
                            diagnostics: vec![],
                            version: None,
                        });
                    }
                    Err(detail) => {
                        let revision = root_state.revision;
                        root_state.backoff = Some(WorkspaceAnalysisBackoff::after_failure(
                            revision,
                            root_state.backoff.as_ref(),
                            Instant::now(),
                        ));
                        report_lsp_internal_error(
                            state,
                            Some(&focus),
                            "analyzing workspace",
                            &detail,
                        );
                    }
                }

                let build_pending = root_state.build_pending.take();
                state.roots.insert(root, root_state);

                let mut needs_refresh = false;
                if let Some(tokens) = semantic_tokens
                    && let Some(document) = state.documents.get_mut(&focus)
                {
                    document.semantic_tokens = Some(tokens);
                    needs_refresh = true;
                }

                if let Some(pending_focus) = build_pending {
                    // Edits landed while the build ran: rebuild with the
                    // latest requester's inputs.
                    request_workspace_build(state, &pending_focus);
                }

                if needs_refresh {
                    let client = state.client.clone();
                    spawn(async move {
                        client
                            .request::<request::SemanticTokensRefresh>(())
                            .await
                            .ok();
                    });
                }

                std::ops::ControlFlow::Continue(())
            })
            .event::<CoreBuildEvent>(|state, event| {
                state.core_build_requested = false;
                if let Some(core) = event.0 {
                    state.core = Some(core);
                } else {
                    tracing::warn!("core workspace build failed; goto-definition into core degraded");
                }
                std::ops::ControlFlow::Continue(())
            })
            .event::<StdlibModuleBuildEvent>(|state, event| {
                state.stdlib_modules_requested.remove(&event.module_id);
                if let Some(workspace) = event.workspace {
                    state.stdlib_modules.insert(event.module_id, workspace);
                } else {
                    tracing::warn!(
                        "stdlib module workspace build failed for {:?}",
                        event.module_id
                    );
                }
                std::ops::ControlFlow::Continue(())
            });

        ServiceBuilder::new()
            .layer(TracingLayer::default())
            .layer(LifecycleLayer::default())
            .layer(CatchUnwindLayer::default())
            .layer(ConcurrencyLayer::default())
            .layer(ClientProcessMonitorLayer::new(client))
            .service(router)
    });
    init_tracing();

    // Prefer truly asynchronous piped stdin/stdout without blocking tasks.
    #[cfg(unix)]
    let (stdin, stdout) = {
        let stdin = match async_lsp::stdio::PipeStdin::lock_tokio() {
            Ok(stdin) => stdin,
            Err(err) => {
                eprintln!("Talk LSP could not lock stdin: {err}");
                return;
            }
        };
        let stdout = match async_lsp::stdio::PipeStdout::lock_tokio() {
            Ok(stdout) => stdout,
            Err(err) => {
                eprintln!("Talk LSP could not lock stdout: {err}");
                return;
            }
        };
        (stdin, stdout)
    };
    // Fallback to spawn blocking read/write otherwise.
    #[cfg(not(unix))]
    let (stdin, stdout) = (
        tokio_util::compat::TokioAsyncReadCompatExt::compat(tokio::io::stdin()),
        tokio_util::compat::TokioAsyncWriteCompatExt::compat_write(tokio::io::stdout()),
    );

    if let Err(err) = server.run_buffered(stdin, stdout).await {
        eprintln!("Talk LSP server stopped with error: {err}");
    }
}

fn init_tracing() {
    let log_file = File::options()
        .create(true)
        .write(true)
        .truncate(true)
        .open("server.log");

    match log_file {
        Ok(file) => {
            if let Err(err) = tracing_subscriber::fmt()
                .with_max_level(Level::WARN)
                .with_ansi(false)
                .with_writer(file)
                .with_target(false)
                .with_file(false)
                .with_line_number(false)
                .try_init()
            {
                eprintln!("Talk LSP could not initialize file logging: {err}");
            }
        }
        Err(err) => {
            eprintln!("Talk LSP could not create server.log: {err}");
            if let Err(err) = tracing_subscriber::fmt()
                .with_max_level(Level::WARN)
                .with_ansi(false)
                .with_target(false)
                .with_file(false)
                .with_line_number(false)
                .try_init()
            {
                eprintln!("Talk LSP could not initialize stderr logging: {err}");
            }
        }
    }
}

fn is_tlk_uri(uri: &Url) -> bool {
    uri.path().ends_with(".tlk")
}

fn uri_is_under_root(uri: &Url, root: &PathBuf) -> bool {
    let Ok(path) = uri.to_file_path() else {
        return false;
    };
    path.starts_with(root)
}

fn file_stamp_version(path: &PathBuf) -> i32 {
    use std::hash::{Hash, Hasher};
    use std::time::UNIX_EPOCH;

    let meta = std::fs::metadata(path);
    let Ok(meta) = meta else {
        return 0;
    };
    let modified_nanos: u128 = meta
        .modified()
        .ok()
        .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
        .map(|d| d.as_nanos())
        .unwrap_or(0);

    let mut hasher = rustc_hash::FxHasher::default();
    modified_nanos.hash(&mut hasher);
    meta.len().hash(&mut hasher);
    let hash = hasher.finish();
    hash as u32 as i32
}

fn analysis_root_for_uri(state: &ServerState, uri: &Url) -> Option<PathBuf> {
    let path = uri.to_file_path().ok();

    // A package is the analysis boundary even when the client advertises
    // one of its subdirectories or a broader multi-project workspace.
    // In particular, tests/ must retain the manifest's src/ anchor.
    if let Some(package_root) = path
        .as_ref()
        .and_then(crate::compiling::package::PackageProject::enclosing_root)
    {
        return Some(package_root);
    }

    if state.workspace_roots.is_empty()
        && let Some(path) = path.as_ref()
    {
        return path
            .parent()
            .map(|p| p.to_path_buf())
            .or_else(|| Some(path.clone()));
    }

    if let Some(path) = path.as_ref() {
        if !state.workspace_roots.is_empty() {
            let root = state
                .workspace_roots
                .iter()
                .filter(|r| path.starts_with(r))
                .max_by_key(|r| r.components().count())
                .cloned();

            if let Some(root) = root {
                if let Ok(rel) = path.strip_prefix(&root) {
                    let mut comps = rel.components();
                    if let Some(std::path::Component::Normal(first)) = comps.next() {
                        let candidate = root.join(first);
                        if std::fs::metadata(&candidate)
                            .map(|m| m.is_dir())
                            .unwrap_or(false)
                        {
                            return Some(candidate);
                        }
                    }
                }
                return Some(root);
            }
        }

        return path
            .parent()
            .map(|p| p.to_path_buf())
            .or_else(|| Some(path.clone()));
    }

    state
        .workspace_roots
        .first()
        .cloned()
        .or_else(|| std::env::current_dir().ok())
}

/// Stamps of the files the package compile context is built from, so
/// the cached context reloads exactly when one of them changes.
fn package_context_stamp(root: &PathBuf) -> (i32, i32) {
    (
        file_stamp_version(&root.join("package.tlk")),
        file_stamp_version(&root.join("package.lock")),
    )
}

/// The package's compile context for editor sessions: the same inputs
/// `talk check` compiles against, so `package::` anchors at the
/// manifest's source root and dependency imports resolve. Offline: a
/// dependency that is not installed yet degrades to the
/// dependency-free session rather than fetching mid-keystroke.
fn load_package_context(
    root: &PathBuf,
) -> Option<crate::compiling::package::PackageCompileContext> {
    if !crate::compiling::package::PackageProject::exists_at(root) {
        return None;
    }
    match crate::compiling::package::PackageProject::open_at(root, true)
        .and_then(|project| project.package_compile_context())
    {
        Ok(context) => Some(context),
        Err(err) => {
            tracing::warn!(
                "package context unavailable for {}: {err}; using dependency-free session",
                root.display()
            );
            None
        }
    }
}

fn tlk_files_under_root(root: &PathBuf) -> Vec<PathBuf> {
    // A package manifest scopes the workspace to its targets and tests.
    // Stray .tlk files elsewhere stay out of diagnostics.
    crate::cli::package::workspace_source_files(root)
}

/// The document set for a session focused inside the stdlib tree, or
/// None when the focus is not a stdlib path. Module sources compile as
/// their own module (the `Stdlib` workspace context, matching
/// `talk check`): the set is the module's source files, with open
/// documents overriding disk by canonical path. Open documents from
/// OTHER stdlib modules stay out — their `use module::` imports would
/// collide with the module compiling here.
///
/// Test files and harness internals (which no module owns) get an
/// open-documents-only session: their `use fs::`-style imports resolve
/// against the compiled stdlib artifacts, exactly like `talk test`.
/// Open documents that ARE module sources stay out of it — the
/// artifact already provides those definitions, and compiling the
/// source again in this Normal context both duplicates them and
/// drags the module through checks meant for user programs.
fn stdlib_session_documents(
    open_docs: &[OpenDocument],
    focus_uri: &Url,
) -> Option<FxHashMap<Url, i32>> {
    let focus_path = focus_uri.to_file_path().ok()?;
    let stdlib_dir = crate::compiling::stdlib::active_stdlib_dir();
    let canonical_focus = focus_path.canonicalize().unwrap_or(focus_path);
    if !canonical_focus.starts_with(&stdlib_dir) {
        return None;
    }

    let is_test = canonical_focus
        .file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.ends_with(".test.tlk"));

    // Open documents by canonical path, for override matching.
    let open_by_path: FxHashMap<PathBuf, (&Url, i32)> = open_docs
        .iter()
        .filter_map(|doc| {
            let path = doc.uri.to_file_path().ok()?;
            let canonical = path.canonicalize().unwrap_or(path);
            Some((canonical, (&doc.uri, doc.version)))
        })
        .collect();

    if !is_test
        && let Some(module) = crate::compiling::stdlib::module_name_for_path(&canonical_focus)
    {
        let mut set: FxHashMap<Url, i32> = FxHashMap::default();
        for (path, _) in crate::compiling::stdlib::source_documents(module)? {
            if let Some((uri, version)) = open_by_path.get(&path) {
                set.insert((*uri).clone(), *version);
            } else {
                let stamp = file_stamp_version(&path);
                set.insert(Url::from_file_path(&path).ok()?, stamp);
            }
        }
        // A module file the fixed source list does not know yet (new
        // file under syntax/) still joins its own session.
        if let Some((uri, version)) = open_by_path.get(&canonical_focus) {
            set.entry((*uri).clone()).or_insert(*version);
        }
        return Some(set);
    }

    let mut set: FxHashMap<Url, i32> = FxHashMap::default();
    for (path, (uri, version)) in &open_by_path {
        if !path.starts_with(&stdlib_dir) {
            continue;
        }
        let is_module_source = !path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.ends_with(".test.tlk"))
            && crate::compiling::stdlib::module_name_for_path(path).is_some();
        if is_module_source {
            // A module source: its own module session covers it, and
            // the compiled artifact already defines it here.
            continue;
        }
        set.insert((*uri).clone(), *version);
    }
    if set.is_empty() {
        // The focus is closed and nothing else is open: a one-document
        // session from disk, so close-time diagnostics still publish.
        set.insert(focus_uri.clone(), file_stamp_version(&canonical_focus));
    }
    Some(set)
}

/// Kick an off-loop rebuild of the root containing `focus_uri`. At
/// most one build per root is in flight; requests made during a build
/// mark the root pending and the latest inputs win on completion.
fn request_workspace_build(state: &mut ServerState, focus_uri: &Url) {
    let Some(root) = analysis_root_for_uri(state, focus_uri) else {
        return;
    };
    let root_state = state.roots.entry(root.clone()).or_default();
    if root_state.build_in_flight {
        root_state.build_pending = Some(focus_uri.clone());
        return;
    }
    if root_state
        .backoff
        .as_ref()
        .is_some_and(|backoff| backoff.blocks(root_state.revision, Instant::now()))
    {
        return;
    }

    let open_docs = state
        .documents
        .iter()
        .filter(|(uri, _)| is_tlk_uri(uri))
        .filter(|(uri, _)| *uri == focus_uri || uri_is_under_root(uri, &root))
        .map(|(uri, doc)| OpenDocument {
            uri: uri.clone(),
            version: doc.version,
            text: doc.text.clone(),
        })
        .collect();

    let inventory_changed = std::mem::take(&mut root_state.inventory_dirty);
    root_state.build_in_flight = true;
    let job = WorkspaceBuildJob {
        root,
        focus: focus_uri.clone(),
        open_docs,
        inventory_changed,
    };
    if state.analysis.send(AnalysisJob::Workspace(job)).is_err() {
        root_state.build_in_flight = false;
    }
}

/// The latest completed analysis for the focus root, possibly stale.
/// Handlers never build on the event loop: a cold root kicks the
/// worker and answers empty this once.
fn snapshot_workspace(state: &mut ServerState, focus_uri: &Url) -> Option<Arc<AnalysisWorkspace>> {
    let root = analysis_root_for_uri(state, focus_uri)?;
    let snapshot = state
        .roots
        .get(&root)
        .and_then(|root_state| root_state.workspace.clone());
    if snapshot.is_none() {
        request_workspace_build(state, focus_uri);
    }
    snapshot
}

/// The name-resolved core workspace goto-definition navigates into,
/// built once per session on the worker.
fn core_snapshot(state: &mut ServerState) -> Option<Arc<AnalysisWorkspace>> {
    if state.core.is_none() && !state.core_build_requested {
        state.core_build_requested = true;
        let _ = state.analysis.send(AnalysisJob::Core);
    }
    state.core.clone()
}

/// Kick an off-loop build of a stdlib module's navigation workspace
/// (a goto-definition target), deduplicated against in-flight builds.
fn request_stdlib_module(state: &mut ServerState, module_id: crate::compiling::module::ModuleId) {
    if state.stdlib_modules.contains_key(&module_id)
        || !state.stdlib_modules_requested.insert(module_id)
    {
        return;
    }
    if state
        .analysis
        .send(AnalysisJob::StdlibModule(module_id))
        .is_err()
    {
        state.stdlib_modules_requested.remove(&module_id);
    }
}

/// Stdlib module navigation workspaces mirror stdlib sources; an edit
/// under the stdlib tree invalidates them all.
fn invalidate_stdlib_module_workspaces(state: &mut ServerState, uri: &Url) {
    let Ok(path) = uri.to_file_path() else {
        return;
    };
    let stdlib_dir = crate::compiling::stdlib::active_stdlib_dir();
    let canonical = path.canonicalize().unwrap_or(path);
    if canonical.starts_with(&stdlib_dir) {
        state.stdlib_modules.clear();
        state.stdlib_modules_requested.clear();
    }
}

fn run_analysis_worker(client: ClientSocket, receiver: std::sync::mpsc::Receiver<AnalysisJob>) {
    let mut build = AnalysisBuild::default();
    while let Ok(job) = receiver.recv() {
        match job {
            AnalysisJob::Workspace(job) => {
                let root = job.root.clone();
                let focus = job.focus.clone();
                let focus_text = job
                    .open_docs
                    .iter()
                    .find(|doc| doc.uri == focus)
                    .map(|doc| doc.text.clone());
                let result = build.workspace(job);
                // Tokens ride the build: same debounce, same text
                // snapshot, and the focus document's parse reused from
                // the build's parse cache instead of a re-parse.
                let semantic_tokens = focus_text.and_then(|text| {
                    let ast = result
                        .as_ref()
                        .ok()
                        .and_then(|workspace| workspace.as_ref())
                        .and_then(|workspace| {
                            let document_id = document_id_for_uri(&focus);
                            let file_id = *workspace.document_to_file_id.get(&document_id)?;
                            build.parse_cache.borrow().get_ast(
                                file_id,
                                &document_path_for_uri(&focus),
                                crate::compiling::driver::ParseMode::Lenient,
                                &text,
                            )
                        });
                    catch_unwind(AssertUnwindSafe(|| {
                        SemanticTokensResult::Tokens(SemanticTokens {
                            result_id: None,
                            data: crate::lsp::semantic_tokens::collect_with_ast(
                                &text,
                                ast.as_ref(),
                            ),
                        })
                    }))
                    .ok()
                });
                if client
                    .emit(WorkspaceBuildEvent {
                        root,
                        focus,
                        result,
                        semantic_tokens,
                    })
                    .is_err()
                {
                    return;
                }
            }
            AnalysisJob::Core => {
                let core = catch_unwind(AssertUnwindSafe(AnalysisWorkspace::core))
                    .ok()
                    .flatten()
                    .map(Arc::new);
                if client.emit(CoreBuildEvent(core)).is_err() {
                    return;
                }
            }
            AnalysisJob::StdlibModule(module_id) => {
                let parse_cache = build.parse_cache.clone();
                let workspace = catch_unwind(AssertUnwindSafe(|| {
                    AnalysisWorkspace::stdlib_module_workspace(module_id, Some(parse_cache))
                }))
                .ok()
                .flatten()
                .map(Arc::new);
                if client
                    .emit(StdlibModuleBuildEvent {
                        module_id,
                        workspace,
                    })
                    .is_err()
                {
                    return;
                }
            }
        }
    }
}

/// The worker-side build pipeline. Owns the caches the synchronous
/// path kept in RootState (inventories, per-root last-build dedup)
/// plus the package compile contexts, which are not Send and so never
/// leave this thread.
#[derive(Default)]
struct AnalysisBuild {
    package_contexts: FxHashMap<PathBuf, CachedPackageContext>,
    /// Walked file inventories per root (path uri, disk stamp),
    /// refreshed when a job arrives with `inventory_changed`.
    inventories: FxHashMap<PathBuf, Vec<(Url, i32)>>,
    last_builds: FxHashMap<PathBuf, LastBuild>,
    /// Per-file parse results shared across every root's rebuilds:
    /// unchanged files skip the native frontend entirely (parse is the
    /// bulk of a rebuild's cost).
    parse_cache: std::rc::Rc<std::cell::RefCell<crate::compiling::driver::ParseCache>>,
}

struct LastBuild {
    versions: FxHashMap<DocumentId, i32>,
    /// The manifest/lock stamps the workspace was built with: a lock
    /// change alone does not alter any document version, so the dedup
    /// must compare it explicitly.
    package_stamp: (i32, i32),
    workspace: Option<Arc<AnalysisWorkspace>>,
}

impl AnalysisBuild {
    fn workspace(
        &mut self,
        job: WorkspaceBuildJob,
    ) -> Result<Option<Arc<AnalysisWorkspace>>, String> {
        let WorkspaceBuildJob {
            root,
            focus,
            open_docs,
            inventory_changed,
        } = job;

        // The package context anchors `package::` at the manifest's
        // source root and resolves dependency imports, matching what
        // `talk check` accepts. It reloads only when the manifest or
        // lock changes.
        let package_stamp = package_context_stamp(&root);
        let package = match self.package_contexts.get(&root) {
            Some(cached) if cached.stamp == package_stamp => cached.context.clone(),
            _ => {
                let context = load_package_context(&root);
                self.package_contexts.insert(
                    root.clone(),
                    CachedPackageContext {
                        stamp: package_stamp,
                        context: context.clone(),
                    },
                );
                context
            }
        };

        // stdlib sources compile one module at a time, the way
        // `talk check` sees them: a mixed walk of the whole stdlib tree
        // forces the dependency-free Normal context, where intra-module
        // `package::` imports cannot resolve and every edit recompiles
        // modules it did not touch. A stdlib session's document set is
        // the focus module's sources, with open documents overriding
        // disk.
        let docs_by_uri: FxHashMap<Url, i32> = if let Some(session) =
            stdlib_session_documents(&open_docs, &focus)
        {
            session
        } else {
            // The file inventory refreshes only after inventory-affecting
            // events; a burst of edits reuses the last walk.
            if inventory_changed || !self.inventories.contains_key(&root) {
                let walked: Vec<(Url, i32)> = tlk_files_under_root(&root)
                    .into_iter()
                    .filter_map(|path| {
                        let stamp = file_stamp_version(&path);
                        Url::from_file_path(&path).ok().map(|uri| (uri, stamp))
                    })
                    .collect();
                self.inventories.insert(root.clone(), walked);
            }
            let mut docs_by_uri: FxHashMap<Url, i32> = self
                .inventories
                .get(&root)
                .into_iter()
                .flatten()
                .cloned()
                .collect();
            for doc in &open_docs {
                docs_by_uri.insert(doc.uri.clone(), doc.version);
            }
            docs_by_uri
        };

        if docs_by_uri.is_empty() {
            self.last_builds.insert(
                root,
                LastBuild {
                    versions: FxHashMap::default(),
                    package_stamp,
                    workspace: None,
                },
            );
            return Ok(None);
        }

        let versions: FxHashMap<DocumentId, i32> = docs_by_uri
            .iter()
            .map(|(uri, version)| (document_id_for_uri(uri), *version))
            .collect();

        // Inputs identical to the last build (an open/close round trip,
        // a watched-file event that touched nothing relevant, a burst
        // of kicks while one build ran): reuse rather than rebuild.
        if let Some(last) = self.last_builds.get(&root)
            && last.versions == versions
            && last.package_stamp == package_stamp
        {
            return Ok(last.workspace.clone());
        }

        let open_texts: FxHashMap<&Url, &str> = open_docs
            .iter()
            .map(|doc| (&doc.uri, doc.text.as_str()))
            .collect();

        let mut uris: Vec<Url> = docs_by_uri.keys().cloned().collect();
        uris.sort_by(|a, b| a.as_str().cmp(b.as_str()));

        let mut docs: Vec<DocumentInput> = vec![];
        for uri in uris {
            let Some(version) = docs_by_uri.get(&uri) else {
                continue;
            };
            let text = if let Some(text) = open_texts.get(&uri) {
                (*text).to_string()
            } else if let Ok(path) = uri.to_file_path() {
                match std::fs::read_to_string(&path) {
                    Ok(text) => text,
                    Err(err) => {
                        tracing::warn!("skipping unreadable file {path:?}: {err}");
                        continue;
                    }
                }
            } else {
                continue;
            };

            docs.push(DocumentInput {
                id: document_id_for_uri(&uri),
                path: document_path_for_uri(&uri),
                version: *version,
                text: text.into(),
            });
        }

        if docs.is_empty() {
            self.last_builds.insert(
                root,
                LastBuild {
                    versions,
                    package_stamp,
                    workspace: None,
                },
            );
            return Ok(None);
        }

        let build = catch_unwind(AssertUnwindSafe(|| {
            AnalysisWorkspace::new_with_parse_cache(docs, package, self.parse_cache.clone())
        }));
        match build {
            Ok(workspace) => {
                let workspace = workspace.map(Arc::new);
                self.last_builds.insert(
                    root,
                    LastBuild {
                        versions,
                        package_stamp,
                        workspace: workspace.clone(),
                    },
                );
                Ok(workspace)
            }
            Err(payload) => Err(panic_payload_message(payload.as_ref())),
        }
    }
}

fn publish_workspace_diagnostics(state: &mut ServerState, workspace: &AnalysisWorkspace) {
    for (idx, doc_id) in workspace.file_id_to_document.iter().enumerate() {
        let Some(uri) = url_from_document_id(doc_id) else {
            continue;
        };
        if uri
            .to_file_path()
            .is_ok_and(|path| crate::testing::Harness::is_source_path(&path))
        {
            continue;
        }
        let Some(snapshot) = workspace.texts.get(idx) else {
            continue;
        };
        let diagnostics = workspace
            .diagnostics
            .get(doc_id)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter_map(|diagnostic| {
                lsp_diagnostic_for_analysis(snapshot.line_index(), snapshot.text(), &diagnostic)
            })
            .collect();
        // The version the analysis was built from, not the document's
        // current one: the positions belong to that text.
        let version = workspace
            .versions
            .get(doc_id)
            .copied()
            .or_else(|| state.documents.get(&uri).map(|d| d.version));

        let _ = state.client.publish_diagnostics(PublishDiagnosticsParams {
            uri,
            diagnostics,
            version,
        });
    }
}

pub(crate) fn document_id_for_uri(uri: &Url) -> DocumentId {
    uri.as_str().to_string()
}

/// The analysis hover as an LSP hover: markdown contents plus the
/// source range as UTF-16 positions.
pub(crate) fn hover_at_lsp(
    workspace: &AnalysisWorkspace,
    uri: &Url,
    byte_offset: u32,
) -> Option<async_lsp::lsp_types::Hover> {
    let document_id = document_id_for_uri(uri);
    let hover = crate::analysis::hover_at(workspace, &document_id, byte_offset)?;
    let range = workspace.text_for(&document_id).map(|text| {
        let index = crate::common::line_index::LineIndex::new(text);
        let (start_line, start_col, _, _) = index.line_info_utf16(text, hover.range.start);
        let (end_line, end_col, _, _) = index.line_info_utf16(text, hover.range.end);
        LspRange {
            start: Position {
                line: start_line - 1,
                character: start_col - 1,
            },
            end: Position {
                line: end_line - 1,
                character: end_col - 1,
            },
        }
    });
    Some(async_lsp::lsp_types::Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```talk\n{}\n```", hover.contents),
        }),
        range,
    })
}

fn completion_options() -> CompletionOptions {
    CompletionOptions {
        trigger_characters: Some(vec![".".to_string()]),
        ..Default::default()
    }
}

fn document_path_for_uri(uri: &Url) -> String {
    uri.to_file_path()
        .map(|p| p.display().to_string())
        .unwrap_or_else(|_| uri.as_str().to_string())
}

pub(crate) fn url_from_document_id(id: &DocumentId) -> Option<Url> {
    Url::parse(id).ok().or_else(|| Url::from_file_path(id).ok())
}

fn lsp_diagnostic_for_analysis(
    index: &crate::common::line_index::LineIndex,
    text: &str,
    diagnostic: &AnalysisDiagnostic,
) -> Option<Diagnostic> {
    let range =
        byte_span_to_range_utf16_in(index, text, diagnostic.range.start, diagnostic.range.end)?;
    let severity = match diagnostic.severity {
        AnalysisSeverity::Error => DiagnosticSeverity::ERROR,
        AnalysisSeverity::Warning => DiagnosticSeverity::WARNING,
        AnalysisSeverity::Info => DiagnosticSeverity::INFORMATION,
    };

    Some(Diagnostic {
        range,
        severity: Some(severity),
        code: diagnostic
            .kind
            .as_ref()
            .map(|kind| NumberOrString::String(kind.code().to_string())),
        source: Some("talk".to_string()),
        message: diagnostic.message.clone(),
        ..Diagnostic::default()
    })
}

pub(crate) fn byte_span_to_range_utf16(text: &str, start: u32, end: u32) -> Option<Range> {
    byte_span_to_range_utf16_in(
        &crate::common::line_index::LineIndex::new(text),
        text,
        start,
        end,
    )
}

/// The cached-index form: flows converting several spans into one text
/// (diagnostics publish, hover) build the index once.
pub(crate) fn byte_span_to_range_utf16_in(
    index: &crate::common::line_index::LineIndex,
    text: &str,
    start: u32,
    end: u32,
) -> Option<Range> {
    let start = byte_offset_to_utf16_position_in(index, text, start)?;
    let end = byte_offset_to_utf16_position_in(index, text, end)?;
    Some(Range::new(start, end))
}

fn byte_offset_to_utf16_position_in(
    index: &crate::common::line_index::LineIndex,
    text: &str,
    byte_offset: u32,
) -> Option<Position> {
    let (line, character) = index.utf16_position_of_byte_offset(text, byte_offset as usize)?;
    Some(Position::new(line, character))
}

#[cfg(test)]
mod tests {
    use super::{AnalysisWorkspace, DocumentInput, WorkspaceAnalysisBackoff};

    #[test]
    fn manifest_scopes_workspace_files() {
        // A package manifest defines the program: stray .tlk files
        // outside the build targets' source directories (scratch, stale
        // copies) stay out of the compile set, so their frontend errors
        // cannot gate the real program's MIR diagnostics.
        let root = std::env::temp_dir().join(format!("talk-lsp-scope-{}", std::process::id()));
        let src = root.join("src");
        let tests = root.join("tests");
        std::fs::create_dir_all(&src).expect("temp source dir");
        std::fs::create_dir_all(&tests).expect("temp tests dir");
        std::fs::write(
            root.join("package.tlk"),
            "Package(\n\tname: \"p\",\n\tversion: \"0.1.0\",\n\tbuilds: [.lib(from: \"src/lib.tlk\")],\n\tdependencies: []\n)\n",
        )
        .expect("manifest");
        std::fs::write(src.join("lib.tlk"), "let x = 1\n").expect("lib");
        std::fs::write(
            tests.join("lib.test.tlk"),
            "test(\"lib\") { assert(true) }\n",
        )
        .expect("test");
        std::fs::write(root.join("stale.tlk"), "use package::nope::{ Gone }\n").expect("stale");
        let files = super::tlk_files_under_root(&root);
        let names: Vec<&str> = files
            .iter()
            .filter_map(|p| p.file_name().and_then(|n| n.to_str()))
            .collect();
        assert!(names.contains(&"lib.tlk"), "{names:?}");
        assert!(names.contains(&"lib.test.tlk"), "{names:?}");
        assert!(names.contains(&"package.tlk"), "{names:?}");
        assert!(!names.contains(&"stale.tlk"), "{names:?}");
        std::fs::remove_dir_all(&root).ok();
    }
    use crate::lsp::document::Document;
    use async_lsp::ClientSocket;
    use async_lsp::lsp_types::HoverContents;
    use async_lsp::lsp_types::Range;
    use async_lsp::lsp_types::Url;
    use async_lsp::lsp_types::WorkspaceEdit;
    use std::time::{Duration, Instant};

    #[test]
    fn workspace_analysis_failures_back_off_until_the_input_changes() {
        let now = Instant::now();
        let first = WorkspaceAnalysisBackoff::after_failure(1, None, now);
        assert!(first.blocks(1, now + Duration::from_millis(999)));
        assert!(!first.blocks(1, now + Duration::from_secs(1)));

        let second = WorkspaceAnalysisBackoff::after_failure(1, Some(&first), now);
        assert_eq!(second.retry_at, now + Duration::from_secs(2));

        // A new revision (an edit landed) retries immediately.
        assert!(!second.blocks(2, now));
        let changed = WorkspaceAnalysisBackoff::after_failure(2, Some(&second), now);
        assert_eq!(changed.retry_at, now + Duration::from_secs(1));
    }

    #[test]
    fn workspace_analysis_backoff_is_capped() {
        let now = Instant::now();
        let mut backoff = WorkspaceAnalysisBackoff::after_failure(1, None, now);
        for _ in 0..10 {
            backoff = WorkspaceAnalysisBackoff::after_failure(1, Some(&backoff), now);
        }
        assert_eq!(backoff.retry_at, now + Duration::from_secs(30));
    }

    fn workspace_for_docs(docs: Vec<(Url, &str)>) -> AnalysisWorkspace {
        let inputs = docs
            .into_iter()
            .map(|(uri, text)| DocumentInput {
                id: super::document_id_for_uri(&uri),
                path: super::document_path_for_uri(&uri),
                version: 0,
                text: text.into(),
            })
            .collect();
        AnalysisWorkspace::new(inputs).expect("workspace")
    }

    fn parser_workspace(uri: &Url, text: &str) -> AnalysisWorkspace {
        use crate::analysis::workspace::diagnostic_for_any;
        use crate::ast::{AST, NameResolved};
        use crate::compiling::module::ModuleId;
        use crate::node_id::FileID;
        use rustc_hash::FxHashMap;

        // The frontend artifact parses (ADR 0043 Stage 4); a hard
        // failure degrades to the empty AST plus its diagnostic, and
        // quick fixes read the structured payloads on the bridged
        // diagnostics.
        let file_id = FileID(0);
        let (ast, diagnostics) =
            crate::compiling::frontend::parse_ast_lenient(text, file_id, uri.path());
        let ast = AST::<NameResolved>::from(ast);
        let document_id = super::document_id_for_uri(uri);
        let file_id_to_document = vec![document_id.clone()];
        let texts = vec![crate::common::source_snapshot::SourceSnapshot::new(text)];
        let asts = vec![Some(ast)];
        let analysis_diagnostics = diagnostics
            .iter()
            .filter_map(|diagnostic| {
                diagnostic_for_any(&file_id_to_document, &texts, &asts, diagnostic)
            })
            .map(|(_, diagnostic)| diagnostic)
            .collect();
        let mut diagnostics_by_document = FxHashMap::default();
        diagnostics_by_document.insert(document_id.clone(), analysis_diagnostics);

        AnalysisWorkspace {
            local_module_id: ModuleId::Main,
            facts: Default::default(),
            source_root: uri
                .to_file_path()
                .ok()
                .and_then(|path| path.parent().map(std::path::Path::to_path_buf))
                .unwrap_or_default(),
            versions: [(document_id.clone(), 0)].into_iter().collect(),
            file_id_to_document,
            document_to_file_id: [(document_id, file_id)].into_iter().collect(),
            texts,
            asts,
            resolved_names: Default::default(),
            types: Default::default(),
            diagnostics: diagnostics_by_document,
            stdlib_module_ids: Default::default(),
            importable_modules: Default::default(),
        }
    }

    fn bare_workspace(uri: &Url, text: &str) -> AnalysisWorkspace {
        use crate::analysis::workspace::diagnostic_for_any;
        use crate::compiling::driver::{Driver, DriverConfig, Source};
        use crate::name_resolution::symbol::set_symbol_names;
        use rustc_hash::FxHashMap;

        let path = uri.to_file_path().expect("file path");
        let config = DriverConfig::new("CodeActionTest");
        let local_module_id = config.module_id;
        let driver = Driver::new_bare(
            vec![Source::in_memory(path.clone(), text.to_string())],
            config,
        );
        let parsed = driver.parse().expect("parse");
        let resolved = parsed.resolve_names().expect("resolve");
        let asts_by_source = resolved.phase.asts.clone();
        let typed = resolved.type_check();
        let Driver { phase, .. } = typed;
        let (resolved_names, types, facts) = phase.program.into_semantic_parts();
        let diagnostics_any = phase.diagnostics;
        let document_id = super::document_id_for_uri(uri);
        let file_id_to_document = vec![document_id.clone()];
        let document_to_file_id = [(document_id.clone(), crate::node_id::FileID(0))]
            .into_iter()
            .collect();
        let texts = vec![crate::common::source_snapshot::SourceSnapshot::new(text)];
        let mut asts = vec![None];
        for ast in asts_by_source.values() {
            asts[ast.file_id.0 as usize] = Some(ast.clone());
        }
        let _names = set_symbol_names(resolved_names.symbol_names.clone());
        let mut diagnostics: FxHashMap<String, Vec<crate::analysis::Diagnostic>> =
            FxHashMap::default();
        for diagnostic in &diagnostics_any {
            if let Some((document_id, diagnostic)) =
                diagnostic_for_any(&file_id_to_document, &texts, &asts, diagnostic)
            {
                diagnostics.entry(document_id).or_default().push(diagnostic);
            }
        }

        AnalysisWorkspace {
            local_module_id,
            source_root: path
                .parent()
                .map(std::path::Path::to_path_buf)
                .unwrap_or_default(),
            versions: [(document_id.clone(), 0)].into_iter().collect(),
            file_id_to_document,
            document_to_file_id,
            texts,
            asts,
            resolved_names,
            types,
            facts,
            diagnostics,
            stdlib_module_ids: Default::default(),
            importable_modules: Default::default(),
        }
    }

    fn action_rewrite(
        code: &str,
        title: &str,
        workspace: impl FnOnce(&Url, &str) -> AnalysisWorkspace,
    ) -> String {
        let uri =
            Url::from_file_path(std::env::temp_dir().join("code_action.tlk")).expect("file uri");
        let workspace = workspace(&uri, code);
        let document_id = super::document_id_for_uri(&uri);
        let everywhere = Range::new(
            async_lsp::lsp_types::Position::new(0, 0),
            async_lsp::lsp_types::Position::new(999, 0),
        );
        let actions = super::compute_code_actions(&workspace, &document_id, &uri, everywhere);
        let action = actions
            .iter()
            .find_map(|action| match action {
                async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action)
                    if action.title == title =>
                {
                    Some(action)
                }
                _ => None,
            })
            .unwrap_or_else(|| {
                panic!(
                    "missing action '{title}': {actions:?}; diagnostics: {:?}",
                    workspace.diagnostics
                )
            });
        apply_edits(code, action.edit.as_ref().expect("edit"), &uri)
    }

    fn parser_action_rewrite(code: &str, title: &str) -> String {
        action_rewrite(code, title, parser_workspace)
    }

    fn type_action_rewrite(code: &str, title: &str) -> String {
        action_rewrite(code, title, bare_workspace)
    }

    fn action_titles(
        code: &str,
        workspace: impl FnOnce(&Url, &str) -> AnalysisWorkspace,
    ) -> Vec<String> {
        let uri = Url::from_file_path(std::env::temp_dir().join("code_action_titles.tlk"))
            .expect("file uri");
        let workspace = workspace(&uri, code);
        let document_id = super::document_id_for_uri(&uri);
        super::compute_code_actions(
            &workspace,
            &document_id,
            &uri,
            Range::new(
                async_lsp::lsp_types::Position::new(0, 0),
                async_lsp::lsp_types::Position::new(999, 0),
            ),
        )
        .into_iter()
        .filter_map(|action| match action {
            async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) => Some(action.title),
            _ => None,
        })
        .collect()
    }

    fn edit_ranges_for_uri(edit: &WorkspaceEdit, uri: &Url) -> Vec<Range> {
        let mut ranges: Vec<Range> = edit
            .changes
            .as_ref()
            .and_then(|c| c.get(uri))
            .expect("missing edits for uri")
            .iter()
            .map(|e| e.range)
            .collect();
        ranges.sort_by_key(|r| (r.start.line, r.start.character, r.end.line, r.end.character));
        ranges
    }

    #[test]
    fn parser_code_actions_insert_recovered_delimiters() {
        assert_eq!(
            parser_action_rewrite("let xs = [1, 2", "Insert ']'"),
            "let xs = [1, 2]"
        );
        assert_eq!(
            parser_action_rewrite("let pair = (1, 2", "Insert ')'"),
            "let pair = (1, 2)"
        );
        assert_eq!(
            parser_action_rewrite("func f() { 1", "Insert '}'"),
            "func f() { 1}"
        );
        assert_eq!(
            parser_action_rewrite("let xs = [\"😀\"", "Insert ']'"),
            "let xs = [\"😀\"]"
        );
    }

    #[test]
    fn parser_code_action_adds_required_else_branch() {
        assert_eq!(
            parser_action_rewrite("let x = if true { 1 }", "Add required else branch"),
            "let x = if true { 1 } else {}"
        );
    }

    #[test]
    fn parser_code_action_removes_explicit_self_parameter() {
        assert_eq!(
            parser_action_rewrite(
                "struct Foo { func f(self: Foo, value: Int) { value } }",
                "Remove explicit self parameter",
            ),
            "struct Foo { func f(value: Int) { value } }"
        );
    }

    #[test]
    fn parser_code_action_migrates_legacy_public_modifier() {
        assert_eq!(
            parser_action_rewrite("public func greet() {}", "Replace `public` with `pub`"),
            "pub func greet() {}"
        );
    }

    #[test]
    fn existing_type_code_actions_use_structured_diagnostics() {
        let ambiguous = "protocol A { func m() -> Int }\nprotocol B { func m() -> Int }\nextend Int: A { func m() -> Int { 1 } }\nextend Int: B { func m() -> Int { 2 } }\nlet n = 1\nlet x = n.m()\n";
        assert!(type_action_rewrite(ambiguous, "Use 'A.m(n...)'").contains("let x = A.m(n)"),);

        let missing_witness =
            "protocol P { func required() -> Int }\nstruct S {}\nextend S: P {}\n";
        assert!(
            type_action_rewrite(missing_witness, "Add requirement 'required'")
                .contains("func required() -> Int"),
        );

        let non_exhaustive = "enum Choice { case yes, no }\nlet choice = Choice.yes\nlet n = match choice { .yes -> 1 }\n";
        assert!(
            type_action_rewrite(non_exhaustive, "Add missing match arm '.no'")
                .contains(".no -> {}"),
        );
    }

    #[test]
    fn add_missing_match_arms_adds_every_unhandled_case() {
        let source = "enum Direction { case north, east, south, west, center }\nlet direction = Direction.north\nlet n = match direction { .north -> 1 }\n";
        let rewritten = type_action_rewrite(source, "Add missing match arms");

        for pattern in [".east", ".south", ".west", ".center"] {
            assert!(
                rewritten.contains(&format!("{pattern} -> {{}}")),
                "missing generated arm {pattern}: {rewritten}"
            );
        }
        assert!(
            action_titles(&rewritten, bare_workspace)
                .iter()
                .all(|title| !title.starts_with("Add missing match arm")),
            "generated arms did not make the match exhaustive: {rewritten}"
        );
    }

    #[test]
    fn arity_code_actions_add_and_remove_value_arguments() {
        let missing = "func add(a: Int, b: Int) -> Int { a }\nlet n = add(1)\n";
        assert_eq!(
            type_action_rewrite(missing, "Add missing argument"),
            "func add(a: Int, b: Int) -> Int { a }\nlet n = add(1, b: {})\n"
        );

        let multiple_missing = "func add(a: Int, b: Int) -> Int { a }\nlet n = add()\n";
        assert_eq!(
            type_action_rewrite(multiple_missing, "Add 2 missing arguments"),
            "func add(a: Int, b: Int) -> Int { a }\nlet n = add(a: {}, b: {})\n"
        );

        let effect_call = "effect 'ask(a: Int, b: Int) -> Int\nlet n = 'ask(1)\n";
        assert_eq!(
            type_action_rewrite(effect_call, "Add missing argument"),
            "effect 'ask(a: Int, b: Int) -> Int\nlet n = 'ask(1, b: {})\n"
        );

        let too_many = "func add(a: Int, b: Int) -> Int { a }\nlet n = add(1, 2, 3, 4)\n";
        assert_eq!(
            type_action_rewrite(too_many, "Remove 2 extra arguments"),
            "func add(a: Int, b: Int) -> Int { a }\nlet n = add(1, 2)\n"
        );

        let labeled_constructor = "struct Pair { let x: Int let y: Int }\nlet pair = Pair(x: 1)\n";
        assert_eq!(
            type_action_rewrite(labeled_constructor, "Add missing argument"),
            "struct Pair { let x: Int let y: Int }\nlet pair = Pair(x: 1, y: {})\n"
        );

        let missing_before_block =
            "func apply(value: Int, fn: () -> Int) -> Int { value }\nlet n = apply() { 1 }\n";
        assert_eq!(
            type_action_rewrite(missing_before_block, "Add missing argument"),
            "func apply(value: Int, fn: () -> Int) -> Int { value }\nlet n = apply(value: {}) { 1 }\n"
        );

        let extra_block = "func identity(value: Int) -> Int { value }\nlet n = identity(1) { 2 }\n";
        assert_eq!(
            type_action_rewrite(extra_block, "Remove extra argument"),
            "func identity(value: Int) -> Int { value }\nlet n = identity(1)\n"
        );

        let omitted_parentheses = "func combine(value: String, n: Int) -> String { value }\nlet missing = combine \"x\"\nfunc no_args() -> Int { 1 }\nlet extra = no_args \"x\"\n";
        assert_eq!(
            type_action_rewrite(omitted_parentheses, "Add missing argument"),
            "func combine(value: String, n: Int) -> String { value }\nlet missing = combine(\"x\", n: {})\nfunc no_args() -> Int { 1 }\nlet extra = no_args \"x\"\n"
        );
        assert_eq!(
            type_action_rewrite(omitted_parentheses, "Remove extra argument"),
            "func combine(value: String, n: Int) -> String { value }\nlet missing = combine \"x\"\nfunc no_args() -> Int { 1 }\nlet extra = no_args()\n"
        );

        let parenthesized_blocks = "func apply(value: Int, fn: () -> Int) -> Int { value }\nlet missing = apply({ 1 })\nfunc identity(value: Int) -> Int { value }\nlet extra = identity(1, { 2 })\n";
        assert_eq!(
            type_action_rewrite(parenthesized_blocks, "Add missing argument"),
            "func apply(value: Int, fn: () -> Int) -> Int { value }\nlet missing = apply(value: {}, { 1 })\nfunc identity(value: Int) -> Int { value }\nlet extra = identity(1, { 2 })\n"
        );
        assert_eq!(
            type_action_rewrite(parenthesized_blocks, "Remove extra argument"),
            "func apply(value: Int, fn: () -> Int) -> Int { value }\nlet missing = apply({ 1 })\nfunc identity(value: Int) -> Int { value }\nlet extra = identity(1)\n"
        );
    }

    #[test]
    fn fix_all_source_action_repairs_every_preferred_fix() {
        // One `source.fixAll` edit covers the whole document, not just the
        // requested range, and unions only the unambiguous quick fixes.
        let code = "func id(x: Int) -> Int {\n\tx\n}\nid(1)\nid(other: 2)\n";
        assert_eq!(
            type_action_rewrite(code, "Fix all"),
            "func id(x: Int) -> Int {\n\tx\n}\nid(x: 1)\nid(x: 2)\n"
        );

        let uri =
            Url::from_file_path(std::env::temp_dir().join("fix_all_kind.tlk")).expect("file uri");
        let workspace = bare_workspace(&uri, code);
        let document_id = super::document_id_for_uri(&uri);
        let actions = super::compute_code_actions(
            &workspace,
            &document_id,
            &uri,
            Range::new(
                async_lsp::lsp_types::Position::new(0, 0),
                async_lsp::lsp_types::Position::new(999, 0),
            ),
        );
        let fix_all = actions
            .iter()
            .find_map(|action| match action {
                async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action)
                    if action.title == "Fix all" =>
                {
                    Some(action)
                }
                _ => None,
            })
            .expect("a fix-all action");
        assert_eq!(
            fix_all.kind,
            Some(async_lsp::lsp_types::CodeActionKind::SOURCE_FIX_ALL)
        );
    }

    #[test]
    fn argument_label_code_actions_insert_replace_and_remove() {
        // ADR 0041: one atomic quick fix per call, edits derived from the
        // structured diagnostic's spans.
        let missing = "func id(x: Int) -> Int { x }\nid(x: 1)\nid(1)\n";
        assert_eq!(
            type_action_rewrite(missing, "Fix argument label"),
            "func id(x: Int) -> Int { x }\nid(x: 1)\nid(x: 1)\n"
        );

        let incorrect = "func id(foo: Int) -> Int { foo }\nid(fizz: 1)\n";
        assert_eq!(
            type_action_rewrite(incorrect, "Fix argument label"),
            "func id(foo: Int) -> Int { foo }\nid(foo: 1)\n"
        );

        let unexpected = "func id(_ x: Int) -> Int { x }\nid(x: 1)\n";
        assert_eq!(
            type_action_rewrite(unexpected, "Fix argument label"),
            "func id(_ x: Int) -> Int { x }\nid(1)\n"
        );

        let written_underscore = "func id(_ x: Int) -> Int { x }\nid(_: 1)\n";
        assert_eq!(
            type_action_rewrite(written_underscore, "Fix argument label"),
            "func id(_ x: Int) -> Int { x }\nid(1)\n"
        );

        // Multi-argument mismatches repair in one workspace edit.
        let multiple = "func f(a: Int, b: Int) -> Int { a }\nf(1, 2)\n";
        assert_eq!(
            type_action_rewrite(multiple, "Fix 2 argument labels"),
            "func f(a: Int, b: Int) -> Int { a }\nf(a: 1, b: 2)\n"
        );

        // Ownership markers belong to the value: the label inserts before
        // the marker and removal stops at it.
        let marker = "func store(value item: Int) -> Int { item }\nlet n = 1\nstore(consume n)\n";
        assert_eq!(
            type_action_rewrite(marker, "Fix argument label"),
            "func store(value item: Int) -> Int { item }\nlet n = 1\nstore(value: consume n)\n"
        );

        // Indirect function values are positional: the fix removes labels.
        let indirect = "func id(value: Int) -> Int { value }\nlet fn = id\nfn(value: 1)\n";
        assert_eq!(
            type_action_rewrite(indirect, "Fix argument label"),
            "func id(value: Int) -> Int { value }\nlet fn = id\nfn(1)\n"
        );

        // UTF-16 conversion holds after non-ASCII text on the same line.
        let unicode = "func id(x: Int) -> Int { x }\nlet s = \"héllo\"; id(1)\n";
        assert_eq!(
            type_action_rewrite(unicode, "Fix argument label"),
            "func id(x: Int) -> Int { x }\nlet s = \"héllo\"; id(x: 1)\n"
        );
    }

    #[test]
    fn type_code_actions_remove_duplicate_and_redundant_syntax() {
        let duplicate_predicate = "protocol P {}\nfunc f<T>(x: T) -> T where T: P && T: P { x }\n";
        assert_eq!(
            type_action_rewrite(duplicate_predicate, "Remove duplicate where predicate"),
            "protocol P {}\nfunc f<T>(x: T) -> T where T: P { x }\n"
        );

        let redundant_result = "enum Box<T> {\n\tcase value(T) -> Box<T>\n}\n";
        assert_eq!(
            type_action_rewrite(redundant_result, "Remove redundant variant result type",),
            "enum Box<T> {\n\tcase value(T)\n}\n"
        );

        let duplicate_binding =
            "protocol P { associated Item }\nlet x: any P<Item = Int, Item = Int>\n";
        assert_eq!(
            type_action_rewrite(
                duplicate_binding,
                "Remove duplicate associated type binding",
            ),
            "protocol P { associated Item }\nlet x: any P<Item = Int>\n"
        );
    }

    #[test]
    fn type_code_actions_use_catalog_candidates() {
        let unknown_member =
            "struct Counter { let count: Int }\nlet counter = Counter(count: 1)\ncounter.cout\n";
        assert_eq!(
            type_action_rewrite(unknown_member, "Change member to 'count'"),
            "struct Counter { let count: Int }\nlet counter = Counter(count: 1)\ncounter.count\n"
        );

        let unresolved_variant = "enum Choice { case yes }\nlet choice = .yes\n";
        assert_eq!(
            type_action_rewrite(unresolved_variant, "Qualify as 'Choice.yes'"),
            "enum Choice { case yes }\nlet choice = Choice.yes\n"
        );

        let ambiguous_variant = "enum A { case yes }\nenum B { case yes }\nlet value = .yes\n";
        let titles = action_titles(ambiguous_variant, bare_workspace);
        assert!(
            titles.contains(&"Qualify as 'A.yes'".to_string()),
            "{titles:?}"
        );
        assert!(
            titles.contains(&"Qualify as 'B.yes'".to_string()),
            "{titles:?}"
        );

        let unknown_binding = "protocol P { associated Item }\nlet x: any P<Ietm = Int>\n";
        assert_eq!(
            type_action_rewrite(unknown_binding, "Change associated type binding to 'Item'",),
            "protocol P { associated Item }\nlet x: any P<Item = Int>\n"
        );
    }

    #[test]
    fn type_code_actions_repair_effects_variants_and_generics() {
        let undeclared_effect =
            "effect 'io() -> Int\neffect 'net() -> Int\nfunc f() 'net -> Int { 'io() }\n";
        assert_eq!(
            type_action_rewrite(undeclared_effect, "Add 'io to effect annotation"),
            "effect 'io() -> Int\neffect 'net() -> Int\nfunc f() '[net, io] -> Int { 'io() }\n"
        );

        let invalid_result = "struct Other<T> {}\nenum Box<T> { case value(T) -> Other<T> }\n";
        assert_eq!(
            type_action_rewrite(invalid_result, "Change variant result to 'Box'"),
            "struct Other<T> {}\nenum Box<T> { case value(T) -> Box<T> }\n"
        );

        let invalid_labels = "enum Box { case value(item: Int) }\nlet box: Box = .value(itme: 1)\n";
        assert_eq!(
            type_action_rewrite(invalid_labels, "Use declared variant payload labels"),
            "enum Box { case value(item: Int) }\nlet box: Box = .value(item: 1)\n"
        );

        let shadowed_generic = "enum Box<T> { case value<T>(T) -> Box<T> }\n";
        let rewritten = type_action_rewrite(shadowed_generic, "Rename inner generic to 'T1'");
        assert!(rewritten.contains("case value<T1>(T1)"), "{rewritten}");
    }

    #[test]
    fn type_code_actions_split_patterns_and_remove_unreachable_source() {
        let incompatible_or = "enum G<T> {\n\tcase int(Int) -> G<Int>\n\tcase bool(Bool) -> G<Bool>\n}\nfunc f<T>(g: G<T>) -> Int {\n\tmatch g {\n\t\t.int(x) | .bool(x) -> 0\n\t}\n}\n";
        let split =
            type_action_rewrite(incompatible_or, "Split or-pattern into separate match arms");
        assert!(
            split.contains(".int(x) -> 0,\n\t\t.bool(x) -> 0"),
            "{split}"
        );

        let unreachable_arm = "enum Choice { case yes, no }\nlet choice = Choice.yes\nlet n = match choice {\n\t_ -> 1,\n\t.yes -> 2\n}\n";
        let removed = type_action_rewrite(unreachable_arm, "Remove unreachable match arm");
        assert!(!removed.contains(".yes -> 2"), "{removed}");

        let unreachable_code = "func f() -> Int {\n\tloop {}\n\t2\n\t3\n}\n";
        assert_eq!(
            type_action_rewrite(unreachable_code, "Remove unreachable code"),
            "func f() -> Int {\n\tloop {}\n}\n"
        );
    }

    #[test]
    fn separator_removal_handles_first_middle_and_last_items() {
        let text = "a && b && c";
        let remove = |start: usize, end: usize| {
            let (start, end) = super::separator_list_item_removal_range(text, start, end, "&&")
                .expect("removal range");
            format!("{}{}", &text[..start], &text[end..])
        };
        assert_eq!(remove(0, 1), "b && c");
        assert_eq!(remove(5, 6), "a && c");
        assert_eq!(remove(10, 11), "a && b");
    }

    #[test]
    fn code_actions_do_not_guess_for_underdetermined_diagnostics() {
        assert!(action_titles("let x: Int = true\n", bare_workspace).is_empty());
        assert!(
            action_titles("struct Box<T> {}\nlet x: Box<Int, Bool>\n", bare_workspace,).is_empty()
        );
        assert!(
            action_titles(
                "protocol P { associated Item }\nlet x: any P\n",
                bare_workspace,
            )
            .is_empty()
        );
        assert!(action_titles("func f(", parser_workspace).is_empty());
    }

    #[test]
    fn code_action_diagnostic_preserves_warning_identity() {
        let diagnostic = crate::analysis::Diagnostic {
            node_id: None,
            kind: Some(crate::analysis::DiagnosticKind::Types(
                crate::types::TypeError::UnreachableMatchArm,
            )),
            range: crate::analysis::TextRange::new(0, 1),
            severity: crate::analysis::DiagnosticSeverity::Warning,
            message: "unreachable".to_string(),
        };
        let lsp = super::code_action_diagnostic(
            &diagnostic,
            Range::new(
                async_lsp::lsp_types::Position::new(0, 0),
                async_lsp::lsp_types::Position::new(0, 1),
            ),
        );
        assert_eq!(
            lsp.severity,
            Some(async_lsp::lsp_types::DiagnosticSeverity::WARNING)
        );
        let expected_code = Some(async_lsp::lsp_types::NumberOrString::String(
            "type.unreachable-match-arm".to_string(),
        ));
        assert_eq!(lsp.code, expected_code);
        let published = super::lsp_diagnostic_for_analysis(
            &crate::common::line_index::LineIndex::new("x"),
            "x",
            &diagnostic,
        )
        .expect("published diagnostic");
        assert_eq!(published.code, expected_code);
        assert_eq!(
            published.severity,
            Some(async_lsp::lsp_types::DiagnosticSeverity::WARNING)
        );
    }

    #[test]
    fn completion_options_trigger_on_dot() {
        assert_eq!(
            super::completion_options().trigger_characters,
            Some(vec![".".to_string()])
        );
    }

    // ADR 0042: member completion excludes members the access site
    // cannot use.
    #[test]
    fn member_completion_hides_other_files_private_members() {
        let lib_code = "pub struct Widget {\n\tpub let visible: Int\n\tlet hidden: Int\n\tpub func shown() -> Int { 1 }\n\tfunc concealed() -> Int { 2 }\n}\n";
        let main_code = "use package::member_completion_lib::{ Widget }\nlet w = Widget(visible: 1, hidden: 2)\nlet v = w.\n";
        let uri_main = Url::from_file_path(std::env::temp_dir().join("member_completion_main.tlk"))
            .expect("main uri");
        let uri_lib = Url::from_file_path(std::env::temp_dir().join("member_completion_lib.tlk"))
            .expect("lib uri");
        let workspace =
            workspace_for_docs(vec![(uri_main.clone(), main_code), (uri_lib, lib_code)]);
        let document_id = super::document_id_for_uri(&uri_main);
        let items = crate::analysis::completion::complete_in_workspace(
            &workspace,
            &document_id,
            main_code.find("w.").expect("dot") as u32 + 2,
        );
        let labels: Vec<&str> = items.iter().map(|item| item.label.as_str()).collect();
        assert!(
            labels.contains(&"visible"),
            "expected visible in {labels:?}"
        );
        assert!(labels.contains(&"shown"), "expected shown in {labels:?}");
        assert!(
            !labels.contains(&"hidden"),
            "private field leaked into completion: {labels:?}"
        );
        assert!(
            !labels.contains(&"concealed"),
            "private method leaked into completion: {labels:?}"
        );
    }

    #[test]
    fn completion_acceptance_adds_import_from_defining_module() {
        let main_code = "let value = Fo\n";
        let lib_code = "pub struct Foo {}\n";
        // Stdlib modules serve auto-import candidates once any document
        // in the session imports them; nothing is indexed eagerly.
        let consumer_code = "use package::completion_auto_import_lib::{ Foo }\nuse fs::{ Directory }\nlet used = Foo()\n";
        let uri_main =
            Url::from_file_path(std::env::temp_dir().join("completion_auto_import_main.tlk"))
                .expect("main uri");
        let uri_lib =
            Url::from_file_path(std::env::temp_dir().join("completion_auto_import_lib.tlk"))
                .expect("lib uri");
        let uri_consumer =
            Url::from_file_path(std::env::temp_dir().join("completion_auto_import_consumer.tlk"))
                .expect("consumer uri");
        let workspace = workspace_for_docs(vec![
            (uri_main.clone(), main_code),
            (uri_lib, lib_code),
            (uri_consumer, consumer_code),
        ]);
        let document_id = super::document_id_for_uri(&uri_main);
        let candidates = workspace.import_candidates(&document_id);
        assert!(
            candidates
                .iter()
                .any(|candidate| candidate.name == "Directory" && candidate.module_path == "fs"),
            "configured module exports should be importable: {candidates:?}"
        );
        assert!(
            !candidates.iter().any(|candidate| candidate.name == "init"),
            "only top-level exports should be importable: {candidates:?}"
        );
        let items = crate::analysis::completion::complete_in_workspace(
            &workspace,
            &document_id,
            main_code.find("Fo").expect("completion prefix") as u32 + 2,
        );
        assert!(
            items
                .iter()
                .any(|item| item.label == "Directory" && item.import_from.as_deref() == Some("fs")),
            "configured module exports should appear in completion: {items:?}"
        );
        let auto_imports: Vec<_> = items
            .into_iter()
            .filter(|item| item.label == "Foo" && item.import_from.is_some())
            .collect();
        assert_eq!(
            auto_imports.len(),
            1,
            "only the defining module should be offered: {auto_imports:?}; candidates: {candidates:?}"
        );
        assert_eq!(
            auto_imports[0].import_from.as_deref(),
            Some("package::completion_auto_import_lib")
        );

        let ast = workspace.asts[workspace
            .document_index(&document_id)
            .expect("document index")]
        .as_ref()
        .expect("main ast");
        let lsp_items =
            crate::lsp::completion::to_lsp_items(auto_imports, main_code, ast.roots.as_slice());
        let edits = lsp_items[0]
            .additional_text_edits
            .as_ref()
            .expect("additional import edit");
        assert_eq!(edits.len(), 1);
        assert_eq!(
            edits[0].new_text,
            "use package::completion_auto_import_lib::{ Foo }\n\n"
        );
    }

    #[test]
    fn undefined_name_quick_fix_inserts_separated_import() {
        let main_code = "foo\n";
        let lib_code = "pub let foo = 1\n";
        let consumer_code = "use package::auto_import_path_only_lib::{ foo }\nlet consumed = foo\n";
        let uri_main =
            Url::from_file_path(std::env::temp_dir().join("auto_import_path_only_main.tlk"))
                .expect("main uri");
        let uri_lib =
            Url::from_file_path(std::env::temp_dir().join("auto_import_path_only_lib.tlk"))
                .expect("lib uri");
        let uri_consumer =
            Url::from_file_path(std::env::temp_dir().join("auto_import_path_only_consumer.tlk"))
                .expect("consumer uri");
        let module = workspace_for_docs(vec![
            (uri_main.clone(), main_code),
            (uri_lib, lib_code),
            (uri_consumer, consumer_code),
        ]);
        let document_id = super::document_id_for_uri(&uri_main);
        let everywhere = Range::new(
            async_lsp::lsp_types::Position::new(0, 0),
            async_lsp::lsp_types::Position::new(999, 0),
        );
        let actions = super::compute_code_actions(&module, &document_id, &uri_main, everywhere);
        let import_actions: Vec<_> = actions
            .iter()
            .filter(|action| match action {
                async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) => {
                    action.title.contains("Import 'foo'")
                }
                _ => false,
            })
            .collect();
        assert_eq!(
            import_actions.len(),
            1,
            "only the defining export should be offered: {import_actions:?}"
        );
        let async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) = import_actions[0]
        else {
            panic!("not a code action");
        };
        let rewritten = apply_edits(main_code, action.edit.as_ref().expect("edit"), &uri_main);
        assert_eq!(
            rewritten,
            "use package::auto_import_path_only_lib::{ foo }\n\nfoo\n"
        );
    }

    #[test]
    fn undefined_name_quick_fix_follows_no_core_comment() {
        let main_code = "// no-core\nfoo\n";
        let lib_code = "pub let foo = 1\n";
        let uri_main =
            Url::from_file_path(std::env::temp_dir().join("auto_import_no_core_main.tlk"))
                .expect("main uri");
        let uri_lib = Url::from_file_path(std::env::temp_dir().join("auto_import_no_core_lib.tlk"))
            .expect("lib uri");
        let module = workspace_for_docs(vec![(uri_main.clone(), main_code), (uri_lib, lib_code)]);
        let document_id = super::document_id_for_uri(&uri_main);
        let everywhere = Range::new(
            async_lsp::lsp_types::Position::new(0, 0),
            async_lsp::lsp_types::Position::new(999, 0),
        );
        let actions = super::compute_code_actions(&module, &document_id, &uri_main, everywhere);
        let async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) = actions
            .iter()
            .find(|action| match action {
                async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) => {
                    action.title.contains("Import 'foo'")
                }
                _ => false,
            })
            .expect("import quick-fix")
        else {
            panic!("not a code action");
        };

        let rewritten = apply_edits(main_code, action.edit.as_ref().expect("edit"), &uri_main);
        assert_eq!(
            rewritten,
            "// no-core\nuse package::auto_import_no_core_lib::{ foo }\n\nfoo\n"
        );
    }

    #[test]
    fn undefined_name_quick_fix_appends_to_import_block() {
        let main_code = "use package::auto_import_existing::{ existing }\n\nfoo\n";
        let existing_code = "pub let existing = 1\n";
        let foo_code = "pub let foo = 2\n";
        let uri_main =
            Url::from_file_path(std::env::temp_dir().join("auto_import_existing_main.tlk"))
                .expect("main uri");
        let uri_existing =
            Url::from_file_path(std::env::temp_dir().join("auto_import_existing.tlk"))
                .expect("existing uri");
        let uri_foo = Url::from_file_path(std::env::temp_dir().join("auto_import_appended.tlk"))
            .expect("foo uri");
        let module = workspace_for_docs(vec![
            (uri_main.clone(), main_code),
            (uri_existing, existing_code),
            (uri_foo, foo_code),
        ]);
        let document_id = super::document_id_for_uri(&uri_main);
        let everywhere = Range::new(
            async_lsp::lsp_types::Position::new(0, 0),
            async_lsp::lsp_types::Position::new(999, 0),
        );
        let actions = super::compute_code_actions(&module, &document_id, &uri_main, everywhere);
        let async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) = actions
            .iter()
            .find(|action| match action {
                async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) => {
                    action.title.contains("Import 'foo'")
                }
                _ => false,
            })
            .expect("import quick-fix")
        else {
            panic!("not a code action");
        };

        let rewritten = apply_edits(main_code, action.edit.as_ref().expect("edit"), &uri_main);
        assert_eq!(
            rewritten,
            "use package::auto_import_existing::{ existing }\nuse package::auto_import_appended::{ foo }\n\nfoo\n"
        );
    }

    #[test]
    fn ambiguous_member_quick_fix_offers_each_protocol() {
        let code = "protocol Aa {\n\tfunc m() -> Int\n}\nprotocol Bb {\n\tfunc m() -> Int\n}\nextend Int: Aa {\n\tfunc m() -> Int { 1 }\n}\nextend Int: Bb {\n\tfunc m() -> Int { 2 }\n}\nlet n = 5\nlet x = n.m()\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("ambiguous_member_quick_fix.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let document_id = super::document_id_for_uri(&uri);
        let everywhere = Range::new(
            async_lsp::lsp_types::Position::new(0, 0),
            async_lsp::lsp_types::Position::new(999, 0),
        );
        let actions = super::compute_code_actions(&module, &document_id, &uri, everywhere);
        let titles: Vec<String> = actions
            .iter()
            .map(|a| match a {
                async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) => {
                    action.title.clone()
                }
                other => panic!("unexpected action: {other:?}"),
            })
            .collect();
        assert!(
            titles.iter().any(|t| t.contains("Aa.m")) && titles.iter().any(|t| t.contains("Bb.m")),
            "one quick-fix per candidate protocol: {titles:?}"
        );
        // Applying the Aa fix rewrites `n.m()` into `Aa.m(n)`.
        let async_lsp::lsp_types::CodeActionOrCommand::CodeAction(aa) = actions
            .iter()
            .find(|a| match a {
                async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) => {
                    action.title.contains("Aa.m")
                }
                _ => false,
            })
            .expect("Aa quick-fix")
        else {
            panic!("not a code action");
        };
        let rewritten = apply_edits(code, aa.edit.as_ref().expect("edit"), &uri);
        assert!(
            rewritten.contains("let x = Aa.m(n)"),
            "rewritten source: {rewritten}"
        );
    }

    #[test]
    fn missing_witness_quick_fix_inserts_requirement_stub() {
        let code = "protocol Foo {\n\tfunc foo() -> Int\n\tfunc bar(value: Int) -> Bool\n}\nstruct Thing {}\nextend Thing: Foo {\n\tfunc foo() -> Int { 1 }\n}\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("missing_witness_fix.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let document_id = super::document_id_for_uri(&uri);
        let everywhere = Range::new(
            async_lsp::lsp_types::Position::new(0, 0),
            async_lsp::lsp_types::Position::new(999, 0),
        );
        let actions = super::compute_code_actions(&module, &document_id, &uri, everywhere);
        let async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) = actions
            .iter()
            .find(|a| match a {
                async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) => {
                    action.title.contains("bar")
                }
                _ => false,
            })
            .expect("bar quick-fix")
        else {
            panic!("not a code action");
        };
        let rewritten = apply_edits(code, action.edit.as_ref().expect("edit"), &uri);
        assert!(
            rewritten.contains("func bar(value: Int) -> Bool"),
            "rewritten source: {rewritten}"
        );
        assert!(rewritten.contains("{}"), "rewritten source: {rewritten}");
    }

    #[test]
    fn non_exhaustive_match_quick_fix_inserts_missing_arms() {
        let code = "enum Color {\n\tcase red, green\n}\nlet c = Color.red\nlet x = match c {\n\t.red -> 1\n}\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("missing_match_arm_fix.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let document_id = super::document_id_for_uri(&uri);
        let everywhere = Range::new(
            async_lsp::lsp_types::Position::new(0, 0),
            async_lsp::lsp_types::Position::new(999, 0),
        );
        let actions = super::compute_code_actions(&module, &document_id, &uri, everywhere);
        let async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) = actions
            .iter()
            .find(|a| match a {
                async_lsp::lsp_types::CodeActionOrCommand::CodeAction(action) => {
                    action.title.contains("match arm")
                }
                _ => false,
            })
            .expect("match quick-fix")
        else {
            panic!("not a code action");
        };
        let rewritten = apply_edits(code, action.edit.as_ref().expect("edit"), &uri);
        assert!(
            rewritten.contains(".green -> {}"),
            "rewritten source: {rewritten}"
        );
    }

    /// Apply a WorkspaceEdit's UTF-16 text edits to source.
    fn apply_edits(text: &str, edit: &WorkspaceEdit, uri: &Url) -> String {
        let mut edits: Vec<&async_lsp::lsp_types::TextEdit> = edit
            .changes
            .as_ref()
            .and_then(|c| c.get(uri))
            .expect("missing edits for uri")
            .iter()
            .collect();
        let line_starts: Vec<usize> = std::iter::once(0)
            .chain(text.match_indices('\n').map(|(i, _)| i + 1))
            .collect();
        let to_byte = |p: &async_lsp::lsp_types::Position| {
            let line_start = line_starts[p.line as usize];
            let line_end = text[line_start..]
                .find('\n')
                .map(|offset| line_start + offset)
                .unwrap_or(text.len());
            let line = &text[line_start..line_end];
            let mut utf16 = 0u32;
            for (byte, character) in line.char_indices() {
                if utf16 == p.character {
                    return line_start + byte;
                }
                utf16 += character.len_utf16() as u32;
            }
            assert_eq!(utf16, p.character, "position splits a UTF-16 character");
            line_end
        };
        edits.sort_by_key(|e| std::cmp::Reverse((e.range.start.line, e.range.start.character)));
        let mut out = text.to_string();
        for e in edits {
            let (start, end) = (to_byte(&e.range.start), to_byte(&e.range.end));
            out.replace_range(start..end, &e.new_text);
        }
        out
    }

    #[test]
    fn document_work_waits_for_quiet_and_coalesces_generations() {
        let mut state = super::ServerState {
            client: ClientSocket::new_closed(),
            documents: Default::default(),
            next_work_generation: 0,
            pending_document_work: Default::default(),
            roots: Default::default(),
            core: None,
            core_build_requested: false,
            stdlib_modules: Default::default(),
            stdlib_modules_requested: Default::default(),
            workspace_roots: Default::default(),
            analysis: test_analysis_channel(),
        };
        let uri = Url::parse("file:///test/file.tlk").expect("file uri");
        let started = Instant::now();

        let first = state.queue_document_work(uri.clone(), started);
        assert!(!state.take_document_work(
            &uri,
            first,
            started + super::DOCUMENT_QUIET_PERIOD - Duration::from_millis(1)
        ));
        assert!(state.take_document_work(&uri, first, started + super::DOCUMENT_QUIET_PERIOD));

        let second = state.queue_document_work(uri.clone(), started);
        let replacement_at = started + Duration::from_millis(100);
        let third = state.queue_document_work(uri.clone(), replacement_at);
        assert!(third > second);
        assert!(
            !state.take_document_work(&uri, second, started + super::DOCUMENT_QUIET_PERIOD),
            "the superseded generation must not run"
        );
        assert!(
            !state.take_document_work(&uri, third, started + super::DOCUMENT_QUIET_PERIOD),
            "the replacement generation must restart the quiet period"
        );
        assert!(state.take_document_work(
            &uri,
            third,
            replacement_at + super::DOCUMENT_QUIET_PERIOD
        ));
        assert!(
            !state.take_document_work(&uri, third, replacement_at + super::DOCUMENT_QUIET_PERIOD),
            "a generation must be taken only once"
        );
    }

    #[test]
    fn hover_shows_local_type() {
        let code = "let foo = 1\nfoo\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("hover_shows_local_type.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let byte_offset = code.match_indices("foo").nth(1).expect("second foo").0 as u32;
        let hover = super::hover_at_lsp(&module, &uri, byte_offset).expect("hover");
        let HoverContents::Markup(markup) = hover.contents else {
            panic!("unexpected hover: {hover:?}");
        };
        assert!(markup.value.contains("foo: Int"), "{markup:?}");
    }

    #[test]
    fn hover_shows_member_type() {
        let code = "struct Foo {\n\tlet bar: Int\n}\n\nlet foo = Foo(bar: 1)\nfoo.bar\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("hover_shows_member_type.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let byte_offset = code.match_indices("bar").last().expect("last bar").0 as u32;
        let hover = super::hover_at_lsp(&module, &uri, byte_offset).expect("hover");
        let HoverContents::Markup(markup) = hover.contents else {
            panic!("unexpected hover: {hover:?}");
        };
        assert!(markup.value.contains("Int"), "{markup:?}");
    }

    #[test]
    fn hover_shows_generic_scheme_and_use_site_instantiation() {
        let code = "func id(x) { x }\nid(123)\nid(1.23)\n";
        let uri = Url::from_file_path(
            std::env::temp_dir().join("hover_shows_generic_scheme_and_instantiation.tlk"),
        )
        .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let id_offsets: Vec<usize> = code.match_indices("id").map(|(i, _)| i).collect();
        assert_eq!(id_offsets.len(), 3, "expected 3 `id` occurrences");
        for (index, offset) in id_offsets.into_iter().enumerate() {
            let hover = super::hover_at_lsp(&module, &uri, offset as u32).expect("hover");
            let HoverContents::Markup(markup) = hover.contents else {
                panic!("unexpected hover: {hover:?}");
            };
            assert!(
                markup.value.contains("func id<X>(borrow x: X) -> &X"),
                "{markup:?}"
            );
            match index {
                0 => {
                    assert!(!markup.value.contains("X = Int"), "{markup:?}");
                    assert!(!markup.value.contains("X = Float"), "{markup:?}");
                }
                1 => assert!(markup.value.contains("X = Int"), "{markup:?}"),
                2 => assert!(markup.value.contains("X = Float"), "{markup:?}"),
                _ => unreachable!(),
            }
        }
    }

    #[test]
    fn goto_definition_on_variant_pattern() {
        let code = "enum Opt<T> {\n\tcase some(T)\n\tcase none\n}\n\nlet r = match Opt.some(123) {\n\t.some(x) -> x,\n\t.none -> 0\n}\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_variant_pattern.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Inside "some" of the pattern ".some(x)"
        let byte_offset = code.find(".some(x)").expect("variant pattern") as u32 + 1;
        let target = goto_for_test(&module, None, &uri, byte_offset);
        assert!(
            target.is_some(),
            "should find the variant definition from the pattern"
        );
    }

    // ADR 0042: a rename never manufactures a collision — the LSP path
    // must refuse exactly like the analysis path does.
    #[test]
    fn rename_refuses_to_create_a_collision() {
        let code = "let first = 1\nlet second = 2\nfirst + second\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("rename_lsp_collision.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let offset = code.rfind("first").expect("target") as u32;
        assert!(
            super::rename_at(&module, &uri, offset, "second").is_none(),
            "rename onto an existing binding must refuse"
        );
    }

    #[test]
    fn rename_renames_local_binding() {
        let code = r#"func main() {
  let foo = 1
  foo
}
"#;
        let uri =
            Url::from_file_path(std::env::temp_dir().join("rename_renames_local_binding.tlk"))
                .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);

        let foo_offsets: Vec<usize> = code.match_indices("foo").map(|(i, _)| i).collect();
        assert_eq!(foo_offsets.len(), 2, "expected 2 foo occurrences");

        let byte_offset = foo_offsets[1] as u32;
        let edit = super::rename_at(&module, &uri, byte_offset, "bar").expect("workspace edit");

        let expected_ranges: Vec<Range> = foo_offsets
            .into_iter()
            .map(|start| {
                super::byte_span_to_range_utf16(code, start as u32, (start + 3) as u32)
                    .expect("range")
            })
            .collect();

        assert_eq!(edit_ranges_for_uri(&edit, &uri), expected_ranges);
    }

    #[test]
    fn rename_renames_symbol_across_files() {
        let uri_a = Url::from_file_path(std::env::temp_dir().join("rename_across_files_a.tlk"))
            .expect("file uri");
        let uri_b = Url::from_file_path(std::env::temp_dir().join("rename_across_files_b.tlk"))
            .expect("file uri");
        let code_a = "pub let foo = 1\n";
        let code_b = "use package::rename_across_files_a::{ foo }\nfoo\n";

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Find the "foo" reference in file B (after the import statement)
        let foo_in_b = code_b.rfind("foo").expect("foo");
        let byte_offset = foo_in_b as u32;
        let edit = super::rename_at(&module, &uri_b, byte_offset, "bar").expect("workspace edit");
        let import_edit = super::rename_at(
            &module,
            &uri_b,
            code_b.find("foo").expect("foo") as u32,
            "bar",
        )
        .expect("workspace edit from import");

        let range_a = super::byte_span_to_range_utf16(
            code_a,
            code_a.find("foo").expect("foo") as u32,
            (code_a.find("foo").expect("foo") + 3) as u32,
        )
        .expect("range a");
        let range_b_import = super::byte_span_to_range_utf16(
            code_b,
            code_b.find("foo").expect("foo") as u32,
            (code_b.find("foo").expect("foo") + 3) as u32,
        )
        .expect("range b import");
        let range_b_reference =
            super::byte_span_to_range_utf16(code_b, foo_in_b as u32, (foo_in_b + 3) as u32)
                .expect("range b reference");

        assert_eq!(edit_ranges_for_uri(&edit, &uri_a), vec![range_a]);
        assert_eq!(
            edit_ranges_for_uri(&edit, &uri_b),
            vec![range_b_import, range_b_reference]
        );
        assert_eq!(edit_ranges_for_uri(&import_edit, &uri_a), vec![range_a]);
        assert_eq!(
            edit_ranges_for_uri(&import_edit, &uri_b),
            vec![range_b_import, range_b_reference]
        );
    }

    #[test]
    fn rename_imported_symbol_with_alias_preserves_alias_uses() {
        let uri_a =
            Url::from_file_path(std::env::temp_dir().join("rename_alias_a.tlk")).expect("file uri");
        let uri_b =
            Url::from_file_path(std::env::temp_dir().join("rename_alias_b.tlk")).expect("file uri");
        let code_a = "pub struct Point {}\n";
        let code_b = "use package::rename_alias_a::{ Point as Pt }\nlet p = Pt()\n";

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);
        let alias_use = code_b.rfind("Pt").expect("alias use");
        let edit =
            super::rename_at(&module, &uri_b, alias_use as u32, "Vec3").expect("workspace edit");
        let import_edit = super::rename_at(
            &module,
            &uri_b,
            code_b.find("Point").expect("imported name") as u32,
            "Vec3",
        )
        .expect("workspace edit from import");

        let range_a = super::byte_span_to_range_utf16(
            code_a,
            code_a.find("Point").expect("Point") as u32,
            (code_a.find("Point").expect("Point") + 5) as u32,
        )
        .expect("range a");
        let range_b_import = super::byte_span_to_range_utf16(
            code_b,
            code_b.find("Point").expect("Point") as u32,
            (code_b.find("Point").expect("Point") + 5) as u32,
        )
        .expect("range b import");

        assert_eq!(edit_ranges_for_uri(&edit, &uri_a), vec![range_a]);
        assert_eq!(edit_ranges_for_uri(&edit, &uri_b), vec![range_b_import]);
        assert_eq!(edit_ranges_for_uri(&import_edit, &uri_a), vec![range_a]);
        assert_eq!(
            edit_ranges_for_uri(&import_edit, &uri_b),
            vec![range_b_import]
        );

        let rewritten_b = apply_edits(code_b, &edit, &uri_b);
        assert!(
            rewritten_b.contains("use package::rename_alias_a::{ Vec3 as Pt }"),
            "{rewritten_b}"
        );
        assert!(rewritten_b.contains("let p = Pt()"), "{rewritten_b}");
    }

    #[test]
    fn rename_imported_symbol_with_mixed_alias_keeps_unaliased_uses() {
        let uri_a = Url::from_file_path(std::env::temp_dir().join("rename_mixed_alias_a.tlk"))
            .expect("file uri");
        let uri_b = Url::from_file_path(std::env::temp_dir().join("rename_mixed_alias_b.tlk"))
            .expect("file uri");
        let code_a = "pub struct Point {}\n";
        let code_b = "use package::rename_mixed_alias_a::{ Point as Pt, Point }\nlet a = Point()\nlet b = Pt()\n";

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);
        let unaliased_use = code_b.rfind("Point").expect("unaliased use");
        let edit = super::rename_at(&module, &uri_b, unaliased_use as u32, "Vec3")
            .expect("workspace edit");

        let point_offsets: Vec<_> = code_b.match_indices("Point").map(|(idx, _)| idx).collect();
        assert_eq!(point_offsets.len(), 3, "source: {code_b}");
        let expected_b: Vec<_> = point_offsets
            .iter()
            .map(|start| {
                super::byte_span_to_range_utf16(code_b, *start as u32, (*start + 5) as u32)
                    .expect("range")
            })
            .collect();

        assert_eq!(edit_ranges_for_uri(&edit, &uri_b), expected_b);

        let rewritten_b = apply_edits(code_b, &edit, &uri_b);
        assert!(
            rewritten_b.contains("use package::rename_mixed_alias_a::{ Vec3 as Pt, Vec3 }"),
            "{rewritten_b}"
        );
        assert!(rewritten_b.contains("let a = Vec3()"), "{rewritten_b}");
        assert!(rewritten_b.contains("let b = Pt()"), "{rewritten_b}");
    }

    #[test]
    fn rename_renames_property_member_access() {
        let code = "struct Point {\n  let x: Int\n}\nfunc make() -> Point { Point(x: 1) }\nfunc read(point: Point) -> Int { point.x }\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("rename_property_member.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let member_use = code.rfind("x").expect("member use");
        let edit = super::rename_at(&module, &uri, member_use as u32, "y").expect("edit");
        let rewritten = apply_edits(code, &edit, &uri);

        assert!(rewritten.contains("let y: Int"), "{rewritten}");
        assert!(rewritten.contains("Point(y: 1)"), "{rewritten}");
        assert!(rewritten.contains("point.y"), "{rewritten}");
    }

    #[test]
    fn rename_renames_method_member_access() {
        let code = "struct Thing {}\nextend Thing {\n  func foo() -> Int { 1 }\n}\nfunc read(thing: Thing) -> Int { thing.foo() }\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("rename_method_member.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let member_use = code.rfind("foo").expect("member use");
        let edit = super::rename_at(&module, &uri, member_use as u32, "bar").expect("edit");
        let rewritten = apply_edits(code, &edit, &uri);

        assert!(rewritten.contains("func bar()"), "{rewritten}");
        assert!(rewritten.contains("thing.bar()"), "{rewritten}");
    }

    #[test]
    fn rename_renames_effect_declaration_and_uses() {
        let code = "effect 'boom(message: String) -> ()\nfunc emit() 'boom -> () {\n  'boom(\"x\")\n}\n#handle 'boom { message in emit() }\n";
        let uri =
            Url::from_file_path(std::env::temp_dir().join("rename_effect.tlk")).expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let perform = code.find("boom(\"x\")").expect("perform");
        let edit = super::rename_at(&module, &uri, perform as u32, "zap").expect("edit");
        let rewritten = apply_edits(code, &edit, &uri);

        assert!(rewritten.contains("effect 'zap"), "{rewritten}");
        assert!(rewritten.contains("func emit() 'zap"), "{rewritten}");
        assert!(rewritten.contains("'zap(\"x\")"), "{rewritten}");
        assert!(rewritten.contains("#handle 'zap"), "{rewritten}");
    }

    #[test]
    fn rename_renames_variant_patterns_and_constructors() {
        let code = "enum Opt<T> {\n  case some(T)\n  case none\n}\nlet r = match Opt.some(123) {\n  .some(x) -> x,\n  .none -> 0\n}\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("rename_variant_pattern.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let pattern = code.find(".some(x)").expect("pattern") + 1;
        let edit = super::rename_at(&module, &uri, pattern as u32, "present").expect("edit");
        let rewritten = apply_edits(code, &edit, &uri);

        assert!(rewritten.contains("case present(T)"), "{rewritten}");
        assert!(rewritten.contains("Opt.present(123)"), "{rewritten}");
        assert!(rewritten.contains(".present(x)"), "{rewritten}");
    }

    #[test]
    fn rename_renames_associated_type_bindings() {
        let code = "protocol Iterator {\n  associated Element\n}\nfunc read(it: any Iterator<Element = Int>) -> Int { 1 }\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("rename_assoc_binding.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let binding = code.rfind("Element").expect("binding");
        let edit = super::rename_at(&module, &uri, binding as u32, "Item").expect("edit");
        let rewritten = apply_edits(code, &edit, &uri);

        assert!(rewritten.contains("associated Item"), "{rewritten}");
        assert!(rewritten.contains("Iterator<Item = Int>"), "{rewritten}");
    }

    #[test]
    fn goto_definition_finds_unopened_file_in_workspace() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "talk_lsp_workspace_test_{}_{}",
            std::process::id(),
            nonce
        ));
        std::fs::create_dir_all(&root).expect("create temp root");

        let path_a = root.join("a.tlk");
        let path_b = root.join("b.tlk");
        let code_a = "use package::b::{ foo }\nfoo\n";
        let code_b = "pub let foo = 1\n";
        std::fs::write(&path_a, code_a).expect("write a");
        std::fs::write(&path_b, code_b).expect("write b");

        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let uri_b = Url::from_file_path(&path_b).expect("uri b");

        let mut state = super::ServerState {
            client: ClientSocket::new_closed(),
            documents: Default::default(),
            next_work_generation: 0,
            pending_document_work: Default::default(),
            roots: Default::default(),
            core: None,
            core_build_requested: false,
            stdlib_modules: Default::default(),
            stdlib_modules_requested: Default::default(),
            workspace_roots: vec![root],
            analysis: test_analysis_channel(),
        };
        state
            .documents
            .insert(uri_a.clone(), Document::new(0, code_a.to_string()));

        let mut build = super::AnalysisBuild::default();
        let workspace = analyze(&mut build, &state, &uri_a, true).expect("workspace");
        // Find the "foo" reference after the import statement
        let byte_offset = code_a.rfind("foo").expect("foo") as u32;

        let target = goto_for_test(&workspace, None, &uri_a, byte_offset)
            .expect("definition location");
        assert_eq!(target.uri, uri_b);
    }

    #[test]
    fn diagnostics_accept_package_manifest() {
        let code = r#"Package(
    name: "demo",
    version: "0.1.0",
    builds: [.bin(named: "main", from: "src/main.tlk")],
    dependencies: [.path(package: "local", path: "../local")]
)
"#;
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "talk_lsp_package_manifest_test_{}_{}",
            std::process::id(),
            nonce
        ));
        std::fs::create_dir_all(root.join("src")).expect("create source directory");
        std::fs::write(root.join("src/main.tlk"), "print(42)\n").expect("write source");
        let uri = Url::from_file_path(root.join("package.tlk")).expect("file uri");
        let workspace = workspace_for_docs(vec![(uri.clone(), code)]);
        let doc_id = super::document_id_for_uri(&uri);
        let diagnostics = workspace
            .diagnostics
            .get(&doc_id)
            .cloned()
            .unwrap_or_default();
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
        std::fs::remove_dir_all(root).expect("remove temp root");
    }

    #[test]
    fn diagnostics_report_missing_package_target() {
        let code = r#"Package(
    name: "demo",
    version: "0.1.0",
    builds: [.bin(named: "main", from: "src/missing.tlk")],
    dependencies: []
)
"#;
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "talk_lsp_package_target_test_{}_{}",
            std::process::id(),
            nonce
        ));
        std::fs::create_dir_all(root.join("src")).expect("create source directory");
        let uri = Url::from_file_path(root.join("package.tlk")).expect("file uri");
        let workspace = workspace_for_docs(vec![(uri.clone(), code)]);
        let doc_id = super::document_id_for_uri(&uri);
        let diagnostics = workspace
            .diagnostics
            .get(&doc_id)
            .cloned()
            .unwrap_or_default();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("failed to find package target")),
            "expected missing-target diagnostic, got: {diagnostics:?}"
        );
        std::fs::remove_dir_all(root).expect("remove temp root");
    }

    #[test]
    fn diagnostics_report_undefined_name() {
        let code = "x\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("diagnostics_undefined_name.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let doc_id = super::document_id_for_uri(&uri);
        let diagnostics = module.diagnostics.get(&doc_id).cloned().unwrap_or_default();
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains("Undefined name: x")),
            "expected undefined-name diagnostic, got: {diagnostics:?}"
        );
    }

    #[test]
    fn diagnostics_report_parse_error() {
        let code = "let = 1\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("diagnostics_parse_error.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let doc_id = super::document_id_for_uri(&uri);
        let diagnostics = module.diagnostics.get(&doc_id).cloned().unwrap_or_default();
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains("Unexpected token")),
            "expected parse diagnostic, got: {diagnostics:?}"
        );
    }

    #[test]
    fn workspace_analysis_handles_extend_before_struct_across_files() {
        let uri_a = Url::from_file_path(std::env::temp_dir().join("extend_before_struct_a.tlk"))
            .expect("file uri");
        let uri_b = Url::from_file_path(std::env::temp_dir().join("extend_before_struct_b.tlk"))
            .expect("file uri");

        let code_a = r#"use package::extend_before_struct_b::{ Person }
extend Person {
  func foo() {}
}
"#;
        let code_b = "pub struct Person {}\n";

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);
        let doc_id = super::document_id_for_uri(&uri_a);
        let diagnostics_a = module.diagnostics.get(&doc_id).cloned().unwrap_or_default();
        assert!(
            diagnostics_a.is_empty(),
            "expected no diagnostics, got: {diagnostics_a:?}"
        );
    }

    #[test]
    fn goto_definition_finds_type_parameter() {
        let code = "func id<T>(x: T) -> T { x }\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_type_param.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Find the T in the return type position
        let return_t_offset = code.find(") -> T").expect("return T") + 5;
        let target = goto_for_test(&module, None, &uri, return_t_offset as u32);
        assert!(target.is_some(), "should find type parameter definition");
    }

    #[test]
    fn goto_definition_finds_nominal_inside_optional_method_return() {
        // `Token?` is represented as a synthesized Optional<Token> whose
        // outer span overlaps Token. The nested source nominal must win.
        let code = "struct Token {}\nstruct Lexer {\n  func next() -> Token? { .none }\n}\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_optional_nominal.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let token_offset = code.rfind("Token?").expect("return Token") as u32;
        let target =
            goto_for_test(&module, None, &uri, token_offset).expect("Token definition");
        assert_eq!(target.uri, uri);
        assert_eq!(target.range.start.line, 0);
    }

    #[test]
    fn goto_definition_finds_pattern_binding() {
        let code = r#"func main() {
  let (a, b) = (1, 2)
  a
}
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_pattern_bind.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Find the usage of `a` at the end
        let a_usage_offset = code.rfind("a\n").expect("a usage") as u32;
        let target = goto_for_test(&module, None, &uri, a_usage_offset);
        assert!(target.is_some(), "should find pattern binding definition");
    }

    #[test]
    fn goto_definition_finds_local_variable() {
        let code = r#"func main() {
  let x = 1
  x
}
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_local_var.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Find the usage of x at the end
        let x_usage_offset = code.rfind("x\n").expect("x usage") as u32;
        let target = goto_for_test(&module, None, &uri, x_usage_offset);
        assert!(target.is_some(), "should find local variable definition");
    }

    #[test]
    fn goto_definition_finds_generic_decl() {
        let code = "func id<T>(x: T) -> T { x }\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_generic_decl.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Find the T in the generic declaration <T>
        let generic_t_offset = code.find("<T>").expect("generic T") + 1;
        let target = goto_for_test(&module, None, &uri, generic_t_offset as u32);
        assert!(target.is_some(), "should find generic declaration");
    }

    #[test]
    fn goto_definition_reaches_right_static_operand() {
        let code = "struct Grid<static Rows: Int> {}\nfunc f<static N: Int, static M: Int>(consume g: Grid<N + M>) -> Int where 0 < N { 1 }\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_static_rhs.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let m_offset = code.find("N + M>").expect("static argument") + "N + ".len();
        let target = goto_for_test(&module, None, &uri, m_offset as u32)
            .expect("the right operand of static arithmetic must navigate");
        let func_line = code.lines().nth(1).expect("func line");
        let m_char = func_line.find("static M").expect("M declaration") + "static ".len();
        assert_eq!(
            (
                target.range.start.line,
                target.range.start.character as usize
            ),
            (1, m_char),
            "must navigate to `static M`'s declaration, not another symbol"
        );
    }

    #[test]
    fn goto_definition_on_imported_symbol_navigates_to_definition() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "talk_import_symbol_test_{}_{}",
            std::process::id(),
            nonce
        ));
        std::fs::create_dir_all(&root).expect("create temp root");

        let path_a = root.join("a.tlk");
        let path_b = root.join("b.tlk");
        let code_a = "pub let foo = 1\n";
        let code_b = "use package::a::{ foo }\nfoo\n";
        std::fs::write(&path_a, code_a).expect("write a");
        std::fs::write(&path_b, code_b).expect("write b");

        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let uri_b = Url::from_file_path(&path_b).expect("uri b");

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Click on "foo" in the import - should navigate to definition in a.tlk
        let import_foo_offset = code_b.find("{ foo }").expect("import foo") + 2;
        let target = goto_for_test(&module, None, &uri_b, import_foo_offset as u32)
            .expect("target");

        assert_eq!(target.uri, uri_a, "should navigate to a.tlk");
        // Should point to the definition location in a.tlk
        assert_eq!(target.range.start.line, 0);
    }

    /// 0-indexed line of `needle` in the stdlib source that `uri` points to,
    /// falling back to the bundled text when it is not a file on disk.
    fn stdlib_source_line(uri: &Url, needle: &str) -> u32 {
        let source = uri
            .to_file_path()
            .ok()
            .and_then(|path| std::fs::read_to_string(path).ok())
            .unwrap_or_else(|| include_str!("../../stdlib/fs.tlk").to_string());
        source
            .lines()
            .position(|line| line.contains(needle))
            .unwrap_or_else(|| panic!("`{needle}` must exist in stdlib source")) as u32
    }

    #[test]
    fn goto_definition_on_stdlib_imported_symbol_navigates_to_definition() {
        let code = "use fs::{ Directory }\nlet dir: Directory\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_stdlib_import.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);

        let import_directory_offset = code.find("{ Directory }").expect("import Directory") + 2;
        let target = goto_for_test(&module, None, &uri, import_directory_offset as u32)
            .expect("stdlib definition");

        assert!(
            target.uri.path().ends_with("stdlib/fs.tlk"),
            "should jump to stdlib fs, got {:?}",
            target.uri
        );
        assert_eq!(
            target.range.start.line,
            stdlib_source_line(&target.uri, "pub struct Directory")
        );
    }

    #[test]
    fn goto_definition_on_stdlib_symbol_inside_call_argument_navigates_to_definition() {
        let code = "use fs::{ Directory, Path }\nfunc walk(directory: &Directory) {}\nfunc main() { walk(Directory(path: Path([\".\"]))) }\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_stdlib_call_arg.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);

        let directory_offset = code.rfind("Directory(path").expect("Directory constructor") as u32;
        let target = goto_for_test(&module, None, &uri, directory_offset)
            .expect("stdlib definition");

        assert!(
            target.uri.path().ends_with("stdlib/fs.tlk"),
            "should jump to stdlib fs instead of the outer call, got {:?}",
            target.uri
        );
        assert_eq!(
            target.range.start.line,
            stdlib_source_line(&target.uri, "pub struct Directory")
        );
    }

    #[test]
    fn goto_definition_on_stdlib_qualified_type_annotation_navigates_to_definition() {
        let code = "use fs::{ Directory }\nfunc walk(directory: &fs::Directory) {}\n";
        let uri =
            Url::from_file_path(std::env::temp_dir().join("goto_def_stdlib_qualified_type.tlk"))
                .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);

        let directory_offset = code.find("fs::Directory").expect("qualified type") + "fs::".len();
        let target = goto_for_test(&module, None, &uri, directory_offset as u32)
            .expect("stdlib definition");

        assert!(
            target.uri.path().ends_with("stdlib/fs.tlk"),
            "should jump to stdlib fs, got {:?}",
            target.uri
        );
        assert_eq!(
            target.range.start.line,
            stdlib_source_line(&target.uri, "pub struct Directory")
        );
    }

    #[test]
    fn goto_definition_on_import_path_navigates_to_file() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "talk_import_path_test_{}_{}",
            std::process::id(),
            nonce
        ));
        std::fs::create_dir_all(&root).expect("create temp root");

        let path_a = root.join("a.tlk");
        let path_b = root.join("b.tlk");
        let code_a = "pub let foo = 1\n";
        let code_b = "use package::a::{ foo }\nfoo\n";
        std::fs::write(&path_a, code_a).expect("write a");
        std::fs::write(&path_b, code_b).expect("write b");

        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let uri_b = Url::from_file_path(&path_b).expect("uri b");

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Click on "package::a" in the import path - should navigate to a.tlk
        let path_offset = code_b.find("package::a").expect("import path") as u32;
        let target = goto_for_test(&module, None, &uri_b, path_offset).expect("target");

        assert_eq!(target.uri, uri_a, "should navigate to a.tlk");
        // Should point to the start of the file
        assert_eq!(target.range.start.line, 0);
        assert_eq!(target.range.start.character, 0);
    }

    #[test]
    fn format_does_not_add_extra_newlines() {
        // Simulates what LSP formatting does: calculate range, get formatted text, apply edit
        fn apply_format(input: &str) -> String {
            let formatted = crate::compiling::frontend::format_string(input);
            let newline_count = input.matches('\n').count();
            let ends_with_newline = input.ends_with('\n');
            let last_line = newline_count;
            let last_char = if ends_with_newline {
                0
            } else {
                input
                    .rsplit('\n')
                    .next()
                    .map(|s| s.len())
                    .unwrap_or(input.len())
            };

            // Apply the edit: replace range [0,0] to [last_line, last_char] with formatted
            let mut result = String::new();
            for (i, line) in input.lines().enumerate() {
                if i == last_line {
                    // This line gets partially replaced
                    result.push_str(&line[last_char..]);
                    break;
                }
            }
            // If we ended exactly at the end, result is empty (full replacement)
            format!("{formatted}{result}")
        }

        assert_eq!(apply_format("let x = 1\n"), "let x = 1\n");
        assert_eq!(apply_format("let x = 1\n\n\n"), "let x = 1\n");
        assert_eq!(apply_format("let x=1\n"), "let x = 1\n");
        assert_eq!(apply_format("let x=1\n\n"), "let x = 1\n");
    }

    #[test]
    fn goto_definition_on_effect_call() {
        let code = r#"effect 'fizz() -> Int

#handle 'fizz { 0 }

'fizz()
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_effect_call.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Effect name span excludes the leading ', so find "fizz" in the call (third occurrence)
        let byte_offset = code.match_indices("fizz").nth(2).expect("effect call").0 as u32;
        let target = goto_for_test(&module, None, &uri, byte_offset);
        assert!(target.is_some(), "should find effect definition from call");
    }

    #[test]
    fn goto_definition_on_effect_handler() {
        let code = r#"effect 'fizz() -> Int

#handle 'fizz { 0 }
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_effect_handler.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Effect name span excludes the leading ', so find "fizz" in the handler (second occurrence)
        let byte_offset = code.match_indices("fizz").nth(1).expect("handler").0 as u32;
        let target = goto_for_test(&module, None, &uri, byte_offset);
        assert!(
            target.is_some(),
            "should find effect definition from handler"
        );
    }

    #[test]
    fn goto_definition_on_effect_decl() {
        let code = "effect 'fizz() -> Int\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_effect_decl.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Effect name span excludes the leading ', so point to 'fizz' (after ')
        let byte_offset = code.find("fizz").expect("effect name") as u32;
        let target = goto_for_test(&module, None, &uri, byte_offset);
        assert!(
            target.is_some(),
            "should find effect declaration definition"
        );
    }

    #[test]
    fn goto_definition_on_cross_file_function_call() {
        let code_a = "pub func helper() -> Int { 1 }\n";
        let code_b = "use package::goto_cross_a::{ helper }\nhelper()\n";
        let uri_a =
            Url::from_file_path(std::env::temp_dir().join("goto_cross_a.tlk")).expect("file uri");
        let uri_b =
            Url::from_file_path(std::env::temp_dir().join("goto_cross_b.tlk")).expect("file uri");

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Find "helper" in the call (second occurrence in code_b)
        let byte_offset = code_b.rfind("helper").expect("helper call") as u32;
        let target = goto_for_test(&module, None, &uri_b, byte_offset);
        assert!(
            target.is_some(),
            "should find cross-file function definition"
        );
        let target = target.expect("target");
        assert_eq!(target.uri, uri_a, "should navigate to definition file");
    }

    #[test]
    fn goto_definition_on_effect_in_func_signature() {
        let code = r#"effect 'fizz() -> Int

func foo() 'fizz -> Int {
    'fizz()
}
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_effect_in_func_sig.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Find "fizz" in the function signature (second occurrence)
        let byte_offset = code
            .match_indices("fizz")
            .nth(1)
            .expect("func sig effect")
            .0 as u32;
        let target = goto_for_test(&module, None, &uri, byte_offset);
        assert!(
            target.is_some(),
            "should find effect definition from function signature"
        );
        let target = target.expect("target");
        assert_eq!(target.range.start.line, 0, "should point to effect decl");
    }

    #[test]
    fn goto_definition_on_self_type() {
        let code = r#"struct Foo {
    func make() -> Self { Foo() }
}
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_self_type.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let byte_offset = code.find("Self").expect("Self type") as u32;
        let target = goto_for_test(&module, None, &uri, byte_offset);
        assert!(target.is_some(), "should find Self type definition");
        let target = target.expect("target");
        // Should navigate to the struct Foo definition (line 0)
        assert_eq!(target.range.start.line, 0);
    }

    #[test]
    fn goto_definition_on_core_function() {
        // print_raw is defined in core/IO.tlk and available via the core prelude
        let code = "print_raw(\"hello\")\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_core_func.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let core = super::AnalysisWorkspace::core();

        let byte_offset = code.find("print_raw").expect("print_raw") as u32;
        let target = goto_for_test(&module, core.as_ref(), &uri, byte_offset);
        assert!(target.is_some(), "should find core function definition");
    }

    #[test]
    fn goto_definition_on_core_member() {
        let code = "let bytes = \"hello\".utf8()\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_core_member.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let core = super::AnalysisWorkspace::core();

        let byte_offset = code.find("utf8").expect("utf8") as u32;
        let target = goto_for_test(&module, core.as_ref(), &uri, byte_offset)
            .expect("core member definition");
        assert!(
            target.uri.path().ends_with("String.tlk"),
            "should jump to the core String member, got {:?}",
            target.uri
        );
    }

    #[test]
    fn goto_definition_on_core_member_inside_extension() {
        let code = "extend String {\n\tfunc ends_with(needle: &String) -> Bool {\n\t\tlet i = 0\n\t\tloop i < needle.count() {\n\t\t\tif self.utf8().at(self.count() - i - 1) != needle.utf8().at(i) { return false }\n\t\t\ti = i + 1\n\t\t}\n\t\ttrue\n\t}\n}\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_core_member_ext.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let core = super::AnalysisWorkspace::core();

        let byte_offset = code.find("utf8").expect("utf8") as u32;
        let target = goto_for_test(&module, core.as_ref(), &uri, byte_offset)
            .expect("core member definition inside extension");
        assert!(
            target.uri.path().ends_with("String.tlk"),
            "should jump to the core String member, got {:?}",
            target.uri
        );
    }

    #[test]
    fn goto_def_on_call_callee() {
        let code = "func foo() -> Int { 1 }\nfoo()\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_call_callee.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);

        // Find "foo" in the call expression "foo()" (second occurrence)
        let byte_offset = code.rfind("foo").expect("foo call") as u32;
        let target = goto_for_test(&module, None, &uri, byte_offset);
        assert!(
            target.is_some(),
            "should find function definition from call callee"
        );
        let target = target.expect("target");
        // Should point to the function definition on line 0
        assert_eq!(target.range.start.line, 0);
    }

    #[test]
    fn goto_definition_on_handler_effect_tick() {
        // Clicking on the ' in '#handle 'fizz' should still navigate to the effect
        let code = r#"effect 'fizz() -> Int

#handle 'fizz { 0 }
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_handler_tick.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Find the ' before "fizz" in the handler (the second ' in the code)
        let tick_offset = code.match_indices("'").nth(1).expect("handler tick").0;
        assert_eq!(&code[tick_offset..tick_offset + 1], "'");
        let target = goto_for_test(&module, None, &uri, tick_offset as u32);
        assert!(
            target.is_some(),
            "should find effect definition when clicking on tick mark"
        );
    }

    fn test_analysis_channel() -> std::sync::mpsc::Sender<super::AnalysisJob> {
        let (tx, _rx) = std::sync::mpsc::channel();
        tx
    }

    /// Goto-definition with a stdlib module cache: on `NeedsModule`
    /// the test builds the module workspace in place (production
    /// builds it on the analysis worker) and retries, exactly like the
    /// server's request-build-retry loop.
    fn goto_for_test(
        module: &super::AnalysisWorkspace,
        core: Option<&super::AnalysisWorkspace>,
        uri: &Url,
        byte_offset: u32,
    ) -> Option<async_lsp::lsp_types::Location> {
        let mut stdlib_modules: rustc_hash::FxHashMap<
            crate::compiling::module::ModuleId,
            std::sync::Arc<super::AnalysisWorkspace>,
        > = Default::default();
        loop {
            match super::goto_definition(module, core, &stdlib_modules, uri, byte_offset) {
                super::LspGoto::Found(location) => return Some(location),
                super::LspGoto::NeedsModule(module_id) => {
                    let workspace =
                        super::AnalysisWorkspace::stdlib_module_workspace(module_id, None)?;
                    stdlib_modules.insert(module_id, std::sync::Arc::new(workspace));
                }
                super::LspGoto::NotFound => return None,
            }
        }
    }

    /// Drive the worker-side build pipeline synchronously, the way the
    /// analysis worker would: one job per call, flags explicit.
    fn analyze(
        build: &mut super::AnalysisBuild,
        state: &super::ServerState,
        focus: &Url,
        inventory_changed: bool,
    ) -> Option<std::sync::Arc<super::AnalysisWorkspace>> {
        let root = super::analysis_root_for_uri(state, focus).expect("root");
        let open_docs = state
            .documents
            .iter()
            .filter(|(uri, _)| super::is_tlk_uri(uri))
            .filter(|(uri, _)| *uri == focus || super::uri_is_under_root(uri, &root))
            .map(|(uri, doc)| super::OpenDocument {
                uri: uri.clone(),
                version: doc.version,
                text: doc.text.clone(),
            })
            .collect();
        build
            .workspace(super::WorkspaceBuildJob {
                root,
                focus: focus.clone(),
                open_docs,
                inventory_changed,
            })
            .expect("build")
    }

    fn state_with_roots(roots: Vec<std::path::PathBuf>) -> super::ServerState {
        super::ServerState {
            client: ClientSocket::new_closed(),
            documents: Default::default(),
            next_work_generation: 0,
            pending_document_work: Default::default(),
            roots: Default::default(),
            core: None,
            core_build_requested: false,
            stdlib_modules: Default::default(),
            stdlib_modules_requested: Default::default(),
            workspace_roots: roots,
            analysis: test_analysis_channel(),
        }
    }

    fn temp_root(name: &str) -> std::path::PathBuf {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "talk_lsp_generations_{name}_{}_{}",
            std::process::id(),
            nonce
        ));
        std::fs::create_dir_all(&root).expect("create temp root");
        root
    }

    #[test]
    fn package_workspace_anchors_imports_at_manifest_source_root() {
        let root = temp_root("package_anchor");
        std::fs::create_dir_all(root.join("src/documentables")).expect("create source dirs");
        std::fs::create_dir_all(root.join("tests")).expect("create tests dir");
        std::fs::write(
            root.join("package.tlk"),
            "Package(\n    name: \"demo\",\n    version: \"0.1.0\",\n    builds: [.bin(named: \"main\", from: \"src/main.tlk\")],\n    dependencies: []\n)\n",
        )
        .expect("write manifest");
        std::fs::write(
            root.join("package.lock"),
            "Lock(\n    format: 1,\n    fingerprint: \"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\",\n    root_dependencies: [],\n    packages: [\n    ]\n)\n",
        )
        .expect("write lock");
        std::fs::write(root.join("src/main.tlk"), "let x = 1\n").expect("write main");
        std::fs::write(
            root.join("src/documentables/property.tlk"),
            "pub struct Property {}\n",
        )
        .expect("write property");
        std::fs::write(
            root.join("tests/property.test.tlk"),
            "use package::documentables::property::{ Property }\n\ntest(\"property\") {\n\tlet value = Property()\n}\n",
        )
        .expect("write package test");
        let uri = Url::from_file_path(root.join("tests/property.test.tlk")).expect("test uri");
        // Some clients advertise the test directory itself as the workspace.
        // The enclosing package still owns analysis and module resolution.
        let state = state_with_roots(vec![root.join("tests")]);

        let mut build = super::AnalysisBuild::default();
        let workspace = analyze(&mut build, &state, &uri, true).expect("workspace");
        assert_eq!(
            workspace.source_root,
            root.join("src").canonicalize().expect("canonical src"),
            "package:: anchors at the manifest's source root"
        );
        let doc_id = super::document_id_for_uri(&uri);
        let candidates = workspace.import_candidates(&doc_id);
        assert!(
            candidates
                .iter()
                .any(|candidate| candidate.name == "Property"
                    && candidate.module_path == "package::documentables::property"),
            "auto-import path must match what talk check accepts: {candidates:?}"
        );
        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn unchanged_inputs_reuse_the_last_build() {
        let root = temp_root("cache");
        let path_a = root.join("a.tlk");
        std::fs::write(&path_a, "let x = 1\n").expect("write a");
        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let state = state_with_roots(vec![root]);
        let mut build = super::AnalysisBuild::default();

        let first = analyze(&mut build, &state, &uri_a, true).expect("workspace");

        // The disk changes underneath, but no event reaches the server:
        // the cached inventory keeps the old stamps, the versions match
        // the last build's, and the workspace comes back untouched.
        std::fs::write(&path_a, "let x = 2\n").expect("rewrite a");
        let second = analyze(&mut build, &state, &uri_a, false).expect("workspace");
        assert!(
            std::sync::Arc::ptr_eq(&first, &second),
            "unchanged inputs return the cached workspace"
        );

        // The watched-file event re-walks; the new stamp changes the
        // inputs and the next build picks the change up.
        let third = analyze(&mut build, &state, &uri_a, true).expect("workspace");
        assert!(
            !std::sync::Arc::ptr_eq(&first, &third),
            "a refreshed inventory rebuilds"
        );
        assert!(
            third
                .texts
                .iter()
                .any(|text| text.text().contains("let x = 2")),
            "the rebuilt workspace reads the new disk content"
        );
        std::fs::remove_dir_all(state.workspace_roots.first().expect("root")).ok();
    }

    #[test]
    fn builds_are_scoped_to_the_containing_root() {
        let root_a = temp_root("scope_a");
        let root_b = temp_root("scope_b");
        std::fs::write(root_a.join("main.tlk"), "let a = 1\n").expect("write a");
        std::fs::write(root_b.join("main.tlk"), "let b = 1\n").expect("write b");
        let uri_a = Url::from_file_path(root_a.join("main.tlk")).expect("uri a");
        let uri_b = Url::from_file_path(root_b.join("main.tlk")).expect("uri b");
        let state = state_with_roots(vec![root_a.clone(), root_b]);
        let mut build = super::AnalysisBuild::default();

        let workspace_a = analyze(&mut build, &state, &uri_a, true).expect("workspace a");
        let workspace_b = analyze(&mut build, &state, &uri_b, true).expect("workspace b");

        // A disk change in root A followed by its watched-file event:
        // root A rebuilds, root B is untouched.
        std::fs::write(root_a.join("main.tlk"), "let a = 2\n").expect("rewrite a");

        let workspace_b_after = analyze(&mut build, &state, &uri_b, false).expect("workspace b");
        assert!(
            std::sync::Arc::ptr_eq(&workspace_b, &workspace_b_after),
            "an unrelated root keeps its analysis"
        );
        let workspace_a_after = analyze(&mut build, &state, &uri_a, true).expect("workspace a");
        assert!(
            !std::sync::Arc::ptr_eq(&workspace_a, &workspace_a_after),
            "the changed root rebuilds"
        );
        for root in &state.workspace_roots {
            std::fs::remove_dir_all(root).ok();
        }
    }

    #[test]
    fn content_edits_do_not_rewalk_the_inventory() {
        let root = temp_root("inventory");
        let path_a = root.join("a.tlk");
        std::fs::write(&path_a, "let x = 1\n").expect("write a");
        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let mut state = state_with_roots(vec![root.clone()]);
        state.documents.insert(
            uri_a.clone(),
            super::Document::new(0, "let x = 1\n".to_string()),
        );
        let mut build = super::AnalysisBuild::default();

        let first = analyze(&mut build, &state, &uri_a, true).expect("workspace");

        // A new file appears on disk with no watched-file event, then a
        // content edit: the rebuild reuses the walked inventory, so the
        // new file is not discovered yet.
        let path_b = root.join("b.tlk");
        std::fs::write(&path_b, "let y = 2\n").expect("write b");
        if let Some(document) = state.documents.get_mut(&uri_a) {
            document.text = "let x = 2\n".to_string();
            document.version = 1;
        }
        let second = analyze(&mut build, &state, &uri_a, false).expect("workspace");
        assert!(
            !std::sync::Arc::ptr_eq(&first, &second),
            "a content change rebuilds"
        );
        let doc_b = super::document_id_for_uri(&Url::from_file_path(&path_b).expect("uri b"));
        assert!(
            !second.versions.contains_key(&doc_b),
            "an edit-triggered rebuild keeps the previous inventory"
        );

        // Only the inventory-affecting event re-walks.
        let third = analyze(&mut build, &state, &uri_a, true).expect("workspace");
        assert!(
            third.versions.contains_key(&doc_b),
            "a watched-file event refreshes the inventory"
        );
        std::fs::remove_dir_all(&root).ok();
    }
}
