struct TickEvent;

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
use ignore::WalkBuilder;
use rustc_hash::{FxHashMap, FxHashSet};
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
use crate::lsp::goto_definition::goto_definition;
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

struct ServerState {
    client: ClientSocket,
    counter: i32,
    documents: FxHashMap<Url, Document>,
    dirty_documents: FxHashSet<Url>,
    workspaces: FxHashMap<PathBuf, Arc<AnalysisWorkspace>>,
    workspace_analysis_backoffs: FxHashMap<PathBuf, WorkspaceAnalysisBackoff>,
    core: Option<Arc<AnalysisWorkspace>>,
    workspace_roots: Vec<PathBuf>,
}

struct WorkspaceAnalysisBackoff {
    versions: FxHashMap<DocumentId, i32>,
    consecutive_failures: u32,
    retry_at: Instant,
}

impl WorkspaceAnalysisBackoff {
    const MAX_DELAY_SECS: u64 = 30;

    fn after_failure(
        versions: FxHashMap<DocumentId, i32>,
        previous: Option<&Self>,
        now: Instant,
    ) -> Self {
        let consecutive_failures = previous
            .filter(|failure| failure.versions == versions)
            .map_or(1, |failure| failure.consecutive_failures.saturating_add(1));
        let exponent = consecutive_failures.saturating_sub(1).min(5);
        let delay_secs = (1_u64 << exponent).min(Self::MAX_DELAY_SECS);

        Self {
            versions,
            consecutive_failures,
            retry_at: now + Duration::from_secs(delay_secs),
        }
    }

    fn blocks(&self, versions: &FxHashMap<DocumentId, i32>, now: Instant) -> bool {
        self.versions == *versions && now < self.retry_at
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
    payload: &(dyn Any + Send),
) {
    let detail = panic_payload_message(payload);
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
            report_lsp_internal_error(state, uri, context, payload.as_ref());
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
        tokio::spawn({
            let client = client.clone();
            async move {
                let mut interval = tokio::time::interval(Duration::from_millis(200));
                loop {
                    interval.tick().await;
                    if client.emit(TickEvent).is_err() {
                        break;
                    }
                }
            }
        });

        let mut router = Router::new(ServerState {
            client: client.clone(),
            counter: 0,
            documents: Default::default(),
            dirty_documents: Default::default(),
            workspaces: Default::default(),
            workspace_analysis_backoffs: Default::default(),
            core: None,
            workspace_roots: Default::default(),
        });

        router
            .request::<request::Initialize, _>(|st, params| {
                tracing::trace!("Initialize with {params:?}");

                let roots = workspace_roots_from_initialize(&params);
                if !roots.is_empty() {
                    tracing::info!("workspace roots: {roots:?}");
                }
                st.workspace_roots = roots;
                st.workspaces.clear();
                st.workspace_analysis_backoffs.clear();

                async move {
                    Ok(InitializeResult {
                        capabilities: ServerCapabilities {
                            definition_provider: Some(OneOf::Left(true)),
                            hover_provider: Some(HoverProviderCapability::Simple(true)),
                            rename_provider: Some(OneOf::Left(true)),
                            completion_provider: Some(completion_options()),
                            document_formatting_provider: Some(OneOf::Left(true)),
                            code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
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

                state.documents.insert(
                    document_url.clone(),
                    Document {
                        version,
                        text,
                        last_edited_tick: state.counter,
                        semantic_tokens: None,
                    },
                );
                state.dirty_documents.insert(document_url);
                state.workspaces.clear();
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
                    document.last_edited_tick = state.counter;
                    state.dirty_documents.insert(uri.clone());
                    state.workspaces.clear();
                }
                if let Some(payload) = panic_payload {
                    report_lsp_internal_error(
                        state,
                        Some(&uri),
                        "applying document changes",
                        payload.as_ref(),
                    );
                }

                std::ops::ControlFlow::Continue(())
            })
            .notification::<notification::DidCloseTextDocument>(|state, params| {
                let document_url = params.text_document.uri;
                tracing::info!("did close {document_url}");

                state.documents.remove(&document_url);
                state.dirty_documents.remove(&document_url);
                state.workspaces.clear();

                if is_tlk_uri(&document_url) {
                    if let Some(workspace) = workspace_analysis(state, &document_url) {
                        publish_workspace_diagnostics(state, &workspace);
                    } else {
                        let _ = state.client.publish_diagnostics(PublishDiagnosticsParams {
                            uri: document_url.clone(),
                            diagnostics: vec![],
                            version: None,
                        });
                    }
                }

                std::ops::ControlFlow::Continue(())
            })
            .request::<request::Formatting, _>(|st, params| {
                let uri = params.text_document.uri;
                let text = st.documents.get(&uri).map(|document| document.text.clone());
                let result = if let Some(text) = text {
                    let formatted =
                        recover_lsp(st, Some(&uri), "formatting document", None, || {
                            Some(crate::formatter::format_string(&text))
                        });
                    if let Some(formatted) = formatted {
                        let newline_count = text.matches('\n').count();
                        let ends_with_newline = text.ends_with('\n');
                        let last_line = newline_count as u32;
                        let last_char = if ends_with_newline {
                            0
                        } else {
                            text.rsplit('\n')
                                .next()
                                .map(|s| s.len())
                                .unwrap_or(text.len()) as u32
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

                let workspace = workspace_analysis(st, &uri);
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
                let workspace = workspace_analysis(st, &uri);
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

                let workspace = workspace_analysis(st, &uri);
                let core = core_analysis(st, &uri);
                let result = match (byte_offset, workspace) {
                    (Some(byte_offset), Some(workspace)) => {
                        recover_lsp(st, Some(&uri), "resolving definition", None, || {
                            goto_definition(&workspace, core.as_deref(), &uri, byte_offset)
                                .map(GotoDefinitionResponse::Scalar)
                        })
                    }
                    _ => None,
                };

                async move { Ok(result) }
            })
            .request::<request::Completion, _>(|st, params| {
                let uri = params.text_document_position.text_document.uri.clone();
                let position = params.text_document_position.position;

                let byte_offset = st
                    .documents
                    .get(&uri)
                    .and_then(|document| document.byte_offset(position).map(|o| o as u32));
                let workspace = workspace_analysis(st, &uri);
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
                            let items = completion::to_lsp_items(items);
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
                let workspace = workspace_analysis(state, &uri);
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

                    if state.documents.contains_key(&uri) {
                        state.dirty_documents.insert(uri);
                        continue;
                    }

                    if let Some(root) = analysis_root_for_uri(state, &uri) {
                        diagnostics_workspaces.entry(root).or_insert(uri);
                    }
                }

                state.workspaces.clear();
                for focus_uri in diagnostics_workspaces.values() {
                    if let Some(workspace) = workspace_analysis(state, focus_uri) {
                        publish_workspace_diagnostics(state, &workspace);
                    }
                }

                ControlFlow::Continue(())
            })
            .event::<TickEvent>(|state, _| {
                state.counter += 1;
                let current_tick = state.counter;

                // Pick documents whose last edit happened before this tick
                let ready: Vec<Url> = state
                    .dirty_documents
                    .iter()
                    .filter(|u| {
                        state
                            .documents
                            .get(*u)
                            .map(|d| d.last_edited_tick < current_tick)
                            .unwrap_or(false)
                    })
                    .cloned()
                    .collect();

                let mut diagnostics_workspaces: FxHashMap<PathBuf, Url> = FxHashMap::default();
                let mut needs_refresh = false;

                for document_url in ready {
                    if is_tlk_uri(&document_url)
                        && let Some(root) = analysis_root_for_uri(state, &document_url)
                    {
                        diagnostics_workspaces
                            .entry(root)
                            .or_insert_with(|| document_url.clone());
                    }

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
                    if let Some(document) = state.documents.get_mut(&document_url) {
                        document.semantic_tokens = semantic_tokens;
                        needs_refresh = true;
                    }
                    state.dirty_documents.remove(&document_url);
                }

                for focus_uri in diagnostics_workspaces.values() {
                    if let Some(workspace) = workspace_analysis(state, focus_uri) {
                        publish_workspace_diagnostics(state, &workspace);
                    }
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

fn tlk_files_under_root(root: &PathBuf) -> Vec<PathBuf> {
    let mut result = Vec::new();

    for entry in WalkBuilder::new(root).build() {
        let Ok(entry) = entry else {
            continue;
        };

        if !entry.file_type().is_some_and(|t| t.is_file()) {
            continue;
        }

        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("tlk") {
            result.push(path.to_path_buf());
        }
    }

    result
}

fn workspace_analysis(state: &mut ServerState, focus_uri: &Url) -> Option<Arc<AnalysisWorkspace>> {
    let root = analysis_root_for_uri(state, focus_uri)?;
    let mut docs_by_uri: FxHashMap<Url, i32> = FxHashMap::default();

    for path in tlk_files_under_root(&root) {
        let Ok(uri) = Url::from_file_path(&path) else {
            continue;
        };
        docs_by_uri.insert(uri, file_stamp_version(&path));
    }

    for (uri, doc) in state.documents.iter() {
        if !is_tlk_uri(uri) {
            continue;
        }
        if uri == focus_uri || uri_is_under_root(uri, &root) {
            docs_by_uri.insert(uri.clone(), doc.version);
        }
    }

    if docs_by_uri.is_empty() {
        return None;
    }

    let versions: FxHashMap<DocumentId, i32> = docs_by_uri
        .iter()
        .map(|(uri, version)| (document_id_for_uri(uri), *version))
        .collect();
    if let Some(existing) = state.workspaces.get(&root)
        && existing.versions == versions
    {
        return Some(existing.clone());
    }
    if state
        .workspace_analysis_backoffs
        .get(&root)
        .is_some_and(|backoff| backoff.blocks(&versions, Instant::now()))
    {
        return None;
    }

    let mut uris: Vec<Url> = docs_by_uri.keys().cloned().collect();
    uris.sort_by(|a, b| a.as_str().cmp(b.as_str()));

    let mut docs: Vec<DocumentInput> = vec![];
    for uri in uris {
        let Some(version) = docs_by_uri.get(&uri) else {
            continue;
        };
        let text = if let Some(doc) = state.documents.get(&uri)
            && (uri == *focus_uri || uri_is_under_root(&uri, &root))
        {
            doc.text.clone()
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
            text,
        });
    }

    if docs.is_empty() {
        return None;
    }

    let analysis = match recover_lsp_result(state, Some(focus_uri), "analyzing workspace", || {
        AnalysisWorkspace::new(docs)
    }) {
        Ok(Some(analysis)) => analysis,
        Ok(None) => return None,
        Err(()) => {
            let backoff = WorkspaceAnalysisBackoff::after_failure(
                versions,
                state.workspace_analysis_backoffs.get(&root),
                Instant::now(),
            );
            state.workspace_analysis_backoffs.insert(root, backoff);
            return None;
        }
    };
    let analysis = Arc::new(analysis);
    state.workspace_analysis_backoffs.remove(&root);
    state.workspaces.insert(root, analysis.clone());
    Some(analysis)
}

fn publish_workspace_diagnostics(state: &mut ServerState, workspace: &AnalysisWorkspace) {
    for (idx, doc_id) in workspace.file_id_to_document.iter().enumerate() {
        let Some(uri) = url_from_document_id(doc_id) else {
            continue;
        };
        let text = workspace.texts.get(idx).map(|t| t.as_str()).unwrap_or("");
        let diagnostics = workspace
            .diagnostics
            .get(doc_id)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter_map(|diagnostic| lsp_diagnostic_for_analysis(text, &diagnostic))
            .collect();
        let version = state.documents.get(&uri).map(|d| d.version);

        let _ = state.client.publish_diagnostics(PublishDiagnosticsParams {
            uri,
            diagnostics,
            version,
        });
    }
}

fn core_analysis(state: &mut ServerState, focus_uri: &Url) -> Option<Arc<AnalysisWorkspace>> {
    if let Some(core) = state.core.as_ref() {
        return Some(core.clone());
    }

    let core = recover_lsp(state, Some(focus_uri), "analyzing core", None, || {
        AnalysisWorkspace::core()
    })?;
    let core = Arc::new(core);
    state.core = Some(core.clone());
    Some(core)
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
        let (start_line, start_col, _, _) =
            crate::common::text::line_info_for_offset_utf16(text, hover.range.start);
        let (end_line, end_col, _, _) =
            crate::common::text::line_info_for_offset_utf16(text, hover.range.end);
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

fn lsp_diagnostic_for_analysis(text: &str, diagnostic: &AnalysisDiagnostic) -> Option<Diagnostic> {
    let range = byte_span_to_range_utf16(text, diagnostic.range.start, diagnostic.range.end)?;
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
    let start = byte_offset_to_utf16_position(text, start)?;
    let end = byte_offset_to_utf16_position(text, end)?;
    Some(Range::new(start, end))
}

fn byte_offset_to_utf16_position(text: &str, byte_offset: u32) -> Option<Position> {
    let byte_offset = byte_offset as usize;
    if byte_offset > text.len() {
        return None;
    }

    let before = text.get(..byte_offset)?;
    let line = before.matches('\n').count() as u32;
    let line_start = before.rfind('\n').map(|i| i + 1).unwrap_or(0);
    let col_slice = text.get(line_start..byte_offset)?;
    let col = col_slice.encode_utf16().count() as u32;
    Some(Position::new(line, col))
}

#[cfg(test)]
mod tests {
    use super::{AnalysisWorkspace, DocumentInput, WorkspaceAnalysisBackoff};
    use crate::lsp::document::Document;
    use async_lsp::ClientSocket;
    use async_lsp::lsp_types::HoverContents;
    use async_lsp::lsp_types::Range;
    use async_lsp::lsp_types::Url;
    use async_lsp::lsp_types::WorkspaceEdit;
    use std::path::PathBuf;
    use std::time::{Duration, Instant};

    #[test]
    fn workspace_analysis_failures_back_off_until_the_input_changes() {
        let now = Instant::now();
        let versions = [("main.tlk".to_string(), 1)].into_iter().collect();
        let first = WorkspaceAnalysisBackoff::after_failure(versions, None, now);
        assert!(first.blocks(&first.versions, now + Duration::from_millis(999)));
        assert!(!first.blocks(&first.versions, now + Duration::from_secs(1)));

        let versions = first.versions.clone();
        let second = WorkspaceAnalysisBackoff::after_failure(versions, Some(&first), now);
        assert_eq!(second.retry_at, now + Duration::from_secs(2));

        let changed_versions = [("main.tlk".to_string(), 2)].into_iter().collect();
        assert!(!second.blocks(&changed_versions, now));
        let changed = WorkspaceAnalysisBackoff::after_failure(changed_versions, Some(&second), now);
        assert_eq!(changed.retry_at, now + Duration::from_secs(1));
    }

    #[test]
    fn workspace_analysis_backoff_is_capped() {
        let now = Instant::now();
        let versions = [("main.tlk".to_string(), 1)].into_iter().collect();
        let mut backoff = WorkspaceAnalysisBackoff::after_failure(versions, None, now);
        for _ in 0..10 {
            backoff = WorkspaceAnalysisBackoff::after_failure(
                backoff.versions.clone(),
                Some(&backoff),
                now,
            );
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
                text: text.to_string(),
            })
            .collect();
        AnalysisWorkspace::new(inputs).expect("workspace")
    }

    fn parser_workspace(uri: &Url, text: &str) -> AnalysisWorkspace {
        use crate::analysis::workspace::diagnostic_for_any;
        use crate::ast::{AST, NameResolved};
        use crate::compiling::module::ModuleId;
        use crate::diagnostic::{AnyDiagnostic, Diagnostic, Severity};
        use crate::lexer::Lexer;
        use crate::node_id::{FileID, NodeID};
        use crate::parser::Parser;
        use rustc_hash::FxHashMap;

        let file_id = FileID(0);
        let parser = Parser::new(uri.path(), file_id, Lexer::preserving_comments(text));
        let (ast, diagnostics) = match parser.parse() {
            Ok((ast, diagnostics)) => (AST::<NameResolved>::from(ast), diagnostics),
            Err(error) => (
                AST::<NameResolved> {
                    path: uri.path().to_string(),
                    roots: vec![],
                    meta: Default::default(),
                    phase: NameResolved,
                    node_ids: Default::default(),
                    synthsized_ids: Default::default(),
                    file_id,
                    skip_core_prelude: false,
                },
                vec![AnyDiagnostic::Parsing(Diagnostic {
                    id: NodeID(file_id, 0),
                    severity: Severity::Error,
                    kind: error,
                })],
            ),
        };
        let document_id = super::document_id_for_uri(uri);
        let file_id_to_document = vec![document_id.clone()];
        let texts = vec![text.to_string()];
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
            local_module_id: ModuleId::Current,
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
        let (resolved_names, types) = phase.program.into_semantic_parts();
        let diagnostics_any = phase.diagnostics;
        let document_id = super::document_id_for_uri(uri);
        let file_id_to_document = vec![document_id.clone()];
        let document_to_file_id = [(document_id.clone(), crate::node_id::FileID(0))]
            .into_iter()
            .collect();
        let texts = vec![text.to_string()];
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
            diagnostics,
            stdlib_module_ids: Default::default(),
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
    fn arity_code_actions_add_and_remove_value_arguments() {
        let missing = "func add(a: Int, b: Int) -> Int { a }\nlet n = add(1)\n";
        assert_eq!(
            type_action_rewrite(missing, "Add missing argument"),
            "func add(a: Int, b: Int) -> Int { a }\nlet n = add(1, {})\n"
        );

        let multiple_missing = "func add(a: Int, b: Int) -> Int { a }\nlet n = add()\n";
        assert_eq!(
            type_action_rewrite(multiple_missing, "Add 2 missing arguments"),
            "func add(a: Int, b: Int) -> Int { a }\nlet n = add({}, {})\n"
        );

        let effect_call = "effect 'ask(a: Int, b: Int) -> Int\nlet n = 'ask(1)\n";
        assert_eq!(
            type_action_rewrite(effect_call, "Add missing argument"),
            "effect 'ask(a: Int, b: Int) -> Int\nlet n = 'ask(1, {})\n"
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
            "func apply(value: Int, fn: () -> Int) -> Int { value }\nlet n = apply({}) { 1 }\n"
        );

        let extra_block = "func identity(value: Int) -> Int { value }\nlet n = identity(1) { 2 }\n";
        assert_eq!(
            type_action_rewrite(extra_block, "Remove extra argument"),
            "func identity(value: Int) -> Int { value }\nlet n = identity(1)\n"
        );

        let omitted_parentheses = "func combine(value: String, n: Int) -> String { value }\nlet missing = combine \"x\"\nfunc no_args() -> Int { 1 }\nlet extra = no_args \"x\"\n";
        assert_eq!(
            type_action_rewrite(omitted_parentheses, "Add missing argument"),
            "func combine(value: String, n: Int) -> String { value }\nlet missing = combine(\"x\", {})\nfunc no_args() -> Int { 1 }\nlet extra = no_args \"x\"\n"
        );
        assert_eq!(
            type_action_rewrite(omitted_parentheses, "Remove extra argument"),
            "func combine(value: String, n: Int) -> String { value }\nlet missing = combine \"x\"\nfunc no_args() -> Int { 1 }\nlet extra = no_args()\n"
        );

        let parenthesized_blocks = "func apply(value: Int, fn: () -> Int) -> Int { value }\nlet missing = apply({ 1 })\nfunc identity(value: Int) -> Int { value }\nlet extra = identity(1, { 2 })\n";
        assert_eq!(
            type_action_rewrite(parenthesized_blocks, "Add missing argument"),
            "func apply(value: Int, fn: () -> Int) -> Int { value }\nlet missing = apply({}, { 1 })\nfunc identity(value: Int) -> Int { value }\nlet extra = identity(1, { 2 })\n"
        );
        assert_eq!(
            type_action_rewrite(parenthesized_blocks, "Remove extra argument"),
            "func apply(value: Int, fn: () -> Int) -> Int { value }\nlet missing = apply({ 1 })\nfunc identity(value: Int) -> Int { value }\nlet extra = identity(1)\n"
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
        let published =
            super::lsp_diagnostic_for_analysis("x", &diagnostic).expect("published diagnostic");
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

    #[test]
    fn undefined_name_quick_fix_inserts_separated_import() {
        let main_code = "foo\n";
        let lib_code = "public let foo = 1\n";
        let uri_main =
            Url::from_file_path(std::env::temp_dir().join("auto_import_path_only_main.tlk"))
                .expect("main uri");
        let uri_lib =
            Url::from_file_path(std::env::temp_dir().join("auto_import_path_only_lib.tlk"))
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
            .find(|a| match a {
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
            "use package::auto_import_path_only_lib::{ foo }\n\nfoo\n"
        );
    }

    #[test]
    fn undefined_name_quick_fix_follows_no_core_comment() {
        let main_code = "// no-core\nfoo\n";
        let lib_code = "public let foo = 1\n";
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
        let existing_code = "public let existing = 1\n";
        let foo_code = "public let foo = 2\n";
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
    #[allow(clippy::vec_init_then_push)]
    fn test_debouncing_logic() {
        // Test the debouncing counter logic
        let mut counter = 0;
        let mut pending_diagnostics: Vec<PathBuf> = Vec::new();

        // Simulate adding a pending diagnostic
        pending_diagnostics.push(PathBuf::from("/test/file.tlk"));
        let last_change_tick = counter;

        // At the same tick - should not process
        let should_process = !pending_diagnostics.is_empty() && counter > last_change_tick;
        assert!(!should_process, "Should not process at same tick");

        // After one tick - should process
        counter += 1;
        let should_process = !pending_diagnostics.is_empty() && counter > last_change_tick;
        assert!(should_process, "Should process after tick");
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
    fn hover_shows_generic_function_type_not_instantiation() {
        let code = "func id(x) { x }\nid(123)\nid(1.23)\n";
        let uri =
            Url::from_file_path(std::env::temp_dir().join("hover_shows_generic_function_type.tlk"))
                .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let id_offsets: Vec<usize> = code.match_indices("id").map(|(i, _)| i).collect();
        assert_eq!(id_offsets.len(), 3, "expected 3 `id` occurrences");
        for offset in id_offsets {
            let hover = super::hover_at_lsp(&module, &uri, offset as u32).expect("hover");
            let HoverContents::Markup(markup) = hover.contents else {
                panic!("unexpected hover: {hover:?}");
            };
            // The scheme, not a use site's instantiation.
            assert!(markup.value.contains("id: <T0>(&T0) -> &T0"), "{markup:?}");
            assert!(!markup.value.contains("Int"), "{markup:?}");
            assert!(!markup.value.contains("Float"), "{markup:?}");
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
        let target = super::goto_definition(&module, None, &uri, byte_offset);
        assert!(
            target.is_some(),
            "should find the variant definition from the pattern"
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
        let code_a = "public let foo = 1\n";
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
        let code_a = "public struct Point {}\n";
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
        let code_a = "public struct Point {}\n";
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
        let code = "effect 'boom(message: String) -> ()\nfunc emit() 'boom -> () {\n  'boom(\"x\")\n}\n@handle 'boom { message in emit() }\n";
        let uri =
            Url::from_file_path(std::env::temp_dir().join("rename_effect.tlk")).expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let perform = code.find("boom(\"x\")").expect("perform");
        let edit = super::rename_at(&module, &uri, perform as u32, "zap").expect("edit");
        let rewritten = apply_edits(code, &edit, &uri);

        assert!(rewritten.contains("effect 'zap"), "{rewritten}");
        assert!(rewritten.contains("func emit() 'zap"), "{rewritten}");
        assert!(rewritten.contains("'zap(\"x\")"), "{rewritten}");
        assert!(rewritten.contains("@handle 'zap"), "{rewritten}");
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
        let code_b = "public let foo = 1\n";
        std::fs::write(&path_a, code_a).expect("write a");
        std::fs::write(&path_b, code_b).expect("write b");

        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let uri_b = Url::from_file_path(&path_b).expect("uri b");

        let mut state = super::ServerState {
            client: ClientSocket::new_closed(),
            counter: 0,
            documents: Default::default(),
            dirty_documents: Default::default(),
            workspaces: Default::default(),
            workspace_analysis_backoffs: Default::default(),
            core: None,
            workspace_roots: vec![root],
        };
        state.documents.insert(
            uri_a.clone(),
            Document {
                version: 0,
                text: code_a.to_string(),
                last_edited_tick: 0,
                semantic_tokens: None,
            },
        );

        let workspace = super::workspace_analysis(&mut state, &uri_a).expect("workspace");
        // Find the "foo" reference after the import statement
        let byte_offset = code_a.rfind("foo").expect("foo") as u32;

        let target = super::goto_definition(&workspace, None, &uri_a, byte_offset)
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
        let code_b = "public struct Person {}\n";

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
        let target = super::goto_definition(&module, None, &uri, return_t_offset as u32);
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
            super::goto_definition(&module, None, &uri, token_offset).expect("Token definition");
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
        let target = super::goto_definition(&module, None, &uri, a_usage_offset);
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
        let target = super::goto_definition(&module, None, &uri, x_usage_offset);
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
        let target = super::goto_definition(&module, None, &uri, generic_t_offset as u32);
        assert!(target.is_some(), "should find generic declaration");
    }

    #[test]
    fn goto_definition_reaches_right_static_operand() {
        let code = "struct Grid<static Rows: Int> {}\nfunc f<static N: Int, static M: Int>(consume g: Grid<N + M>) -> Int where 0 < N { 1 }\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_static_rhs.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        let m_offset = code.find("N + M>").expect("static argument") + "N + ".len();
        let target = super::goto_definition(&module, None, &uri, m_offset as u32)
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
        let code_a = "public let foo = 1\n";
        let code_b = "use package::a::{ foo }\nfoo\n";
        std::fs::write(&path_a, code_a).expect("write a");
        std::fs::write(&path_b, code_b).expect("write b");

        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let uri_b = Url::from_file_path(&path_b).expect("uri b");

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Click on "foo" in the import - should navigate to definition in a.tlk
        let import_foo_offset = code_b.find("{ foo }").expect("import foo") + 2;
        let target = super::goto_definition(&module, None, &uri_b, import_foo_offset as u32)
            .expect("target");

        assert_eq!(target.uri, uri_a, "should navigate to a.tlk");
        // Should point to the definition location in a.tlk
        assert_eq!(target.range.start.line, 0);
    }

    #[test]
    fn goto_definition_on_stdlib_imported_symbol_navigates_to_definition() {
        let code = "use fs::{ Directory }\nlet dir: Directory\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_stdlib_import.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);

        let import_directory_offset = code.find("{ Directory }").expect("import Directory") + 2;
        let target = super::goto_definition(&module, None, &uri, import_directory_offset as u32)
            .expect("stdlib definition");

        assert!(
            target.uri.path().ends_with("stdlib/fs.tlk"),
            "should jump to stdlib fs, got {:?}",
            target.uri
        );
        assert_eq!(target.range.start.line, 39);
    }

    #[test]
    fn goto_definition_on_stdlib_symbol_inside_call_argument_navigates_to_definition() {
        let code = "use fs::{ Directory }\nfunc walk(directory: &Directory) {}\nfunc main() { walk(Directory(path: Path([\".\"]))) }\n";
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_stdlib_call_arg.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);

        let directory_offset = code.rfind("Directory(path").expect("Directory constructor") as u32;
        let target = super::goto_definition(&module, None, &uri, directory_offset)
            .expect("stdlib definition");

        assert!(
            target.uri.path().ends_with("stdlib/fs.tlk"),
            "should jump to stdlib fs instead of the outer call, got {:?}",
            target.uri
        );
        assert_eq!(target.range.start.line, 39);
    }

    #[test]
    fn goto_definition_on_stdlib_qualified_type_annotation_navigates_to_definition() {
        let code = "use fs::{ Directory }\nfunc walk(directory: &fs::Directory) {}\n";
        let uri =
            Url::from_file_path(std::env::temp_dir().join("goto_def_stdlib_qualified_type.tlk"))
                .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);

        let directory_offset = code.find("fs::Directory").expect("qualified type") + "fs::".len();
        let target = super::goto_definition(&module, None, &uri, directory_offset as u32)
            .expect("stdlib definition");

        assert!(
            target.uri.path().ends_with("stdlib/fs.tlk"),
            "should jump to stdlib fs, got {:?}",
            target.uri
        );
        assert_eq!(target.range.start.line, 39);
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
        let code_a = "public let foo = 1\n";
        let code_b = "use package::a::{ foo }\nfoo\n";
        std::fs::write(&path_a, code_a).expect("write a");
        std::fs::write(&path_b, code_b).expect("write b");

        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let uri_b = Url::from_file_path(&path_b).expect("uri b");

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Click on "package::a" in the import path - should navigate to a.tlk
        let path_offset = code_b.find("package::a").expect("import path") as u32;
        let target = super::goto_definition(&module, None, &uri_b, path_offset).expect("target");

        assert_eq!(target.uri, uri_a, "should navigate to a.tlk");
        // Should point to the start of the file
        assert_eq!(target.range.start.line, 0);
        assert_eq!(target.range.start.character, 0);
    }

    #[test]
    fn format_does_not_add_extra_newlines() {
        // Simulates what LSP formatting does: calculate range, get formatted text, apply edit
        fn apply_format(input: &str) -> String {
            let formatted = crate::formatter::format_string(input);
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

@handle 'fizz { 0 }

'fizz()
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_effect_call.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Effect name span excludes the leading ', so find "fizz" in the call (third occurrence)
        let byte_offset = code.match_indices("fizz").nth(2).expect("effect call").0 as u32;
        let target = super::goto_definition(&module, None, &uri, byte_offset);
        assert!(target.is_some(), "should find effect definition from call");
    }

    #[test]
    fn goto_definition_on_effect_handler() {
        let code = r#"effect 'fizz() -> Int

@handle 'fizz { 0 }
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_effect_handler.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Effect name span excludes the leading ', so find "fizz" in the handler (second occurrence)
        let byte_offset = code.match_indices("fizz").nth(1).expect("handler").0 as u32;
        let target = super::goto_definition(&module, None, &uri, byte_offset);
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
        let target = super::goto_definition(&module, None, &uri, byte_offset);
        assert!(
            target.is_some(),
            "should find effect declaration definition"
        );
    }

    #[test]
    fn goto_definition_on_cross_file_function_call() {
        let code_a = "public func helper() -> Int { 1 }\n";
        let code_b = "use package::goto_cross_a::{ helper }\nhelper()\n";
        let uri_a =
            Url::from_file_path(std::env::temp_dir().join("goto_cross_a.tlk")).expect("file uri");
        let uri_b =
            Url::from_file_path(std::env::temp_dir().join("goto_cross_b.tlk")).expect("file uri");

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Find "helper" in the call (second occurrence in code_b)
        let byte_offset = code_b.rfind("helper").expect("helper call") as u32;
        let target = super::goto_definition(&module, None, &uri_b, byte_offset);
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
        let target = super::goto_definition(&module, None, &uri, byte_offset);
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
        let target = super::goto_definition(&module, None, &uri, byte_offset);
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
        let target = super::goto_definition(&module, core.as_ref(), &uri, byte_offset);
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
        let target = super::goto_definition(&module, core.as_ref(), &uri, byte_offset)
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
        let target = super::goto_definition(&module, core.as_ref(), &uri, byte_offset)
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
        let target = super::goto_definition(&module, None, &uri, byte_offset);
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
        // Clicking on the ' in '@handle 'fizz' should still navigate to the effect
        let code = r#"effect 'fizz() -> Int

@handle 'fizz { 0 }
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("goto_def_handler_tick.tlk"))
            .expect("file uri");
        let module = workspace_for_docs(vec![(uri.clone(), code)]);
        // Find the ' before "fizz" in the handler (the second ' in the code)
        let tick_offset = code.match_indices("'").nth(1).expect("handler tick").0;
        assert_eq!(&code[tick_offset..tick_offset + 1], "'");
        let target = super::goto_definition(&module, None, &uri, tick_offset as u32);
        assert!(
            target.is_some(),
            "should find effect definition when clicking on tick mark"
        );
    }
}
