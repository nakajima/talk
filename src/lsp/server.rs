struct TickEvent;

use async_lsp::LanguageClient;
use async_lsp::lsp_types::{
    CodeAction, CodeActionKind, CodeActionOrCommand, CodeActionProviderCapability,
    CodeActionResponse, CompletionOptions, Diagnostic, DiagnosticSeverity, Position, Range,
    SemanticTokens, SemanticTokensResult, TextDocumentSyncCapability, TextDocumentSyncKind,
    TextDocumentSyncOptions, TextDocumentSyncSaveOptions, TextEdit,
};
use async_lsp::{
    ClientSocket,
    client_monitor::ClientProcessMonitorLayer,
    concurrency::ConcurrencyLayer,
    lsp_types::{
        CompletionResponse, GotoDefinitionResponse, Hover, HoverContents, HoverProviderCapability,
        InitializeParams, InitializeResult, MarkupContent, MarkupKind, OneOf,
        PublishDiagnosticsParams, SemanticTokensFullOptions, SemanticTokensLegend,
        SemanticTokensOptions, SemanticTokensServerCapabilities, ServerCapabilities,
        TextDocumentItem, Url, WorkspaceEdit, WorkspaceFolder, notification, request,
    },
    panic::CatchUnwindLayer,
    router::Router,
    server::LifecycleLayer,
    tracing::TracingLayer,
};
use ignore::WalkBuilder;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fs::File;
use std::sync::Arc;
use std::{ops::ControlFlow, path::PathBuf, time::Duration};
use tokio::spawn;
use tower::ServiceBuilder;
use tracing::Level;

use crate::analysis::{
    Diagnostic as AnalysisDiagnostic, DiagnosticSeverity as AnalysisSeverity, DocumentId,
    DocumentInput, Hover as AnalysisHover, Workspace as AnalysisWorkspace,
    completion as analysis_completion, hover as analysis_hover,
};
use crate::lsp::semantic_tokens::collect;
use crate::lsp::{completion, document::Document, semantic_tokens::TOKEN_TYPES};
use crate::lsp::goto_definition::goto_definition;
use crate::lsp::rename::rename_at;

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
    core: Option<Arc<AnalysisWorkspace>>,
    workspace_roots: Vec<PathBuf>,
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

                async move {
                    Ok(InitializeResult {
                        capabilities: ServerCapabilities {
                            hover_provider: Some(HoverProviderCapability::Simple(true)),
                            definition_provider: Some(OneOf::Left(true)),
                            rename_provider: Some(OneOf::Left(true)),
                            completion_provider: Some(CompletionOptions {
                                trigger_characters: Some(vec![".".to_string()]),
                                ..Default::default()
                            }),
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
                        analysis: None,
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

                if let Some(document) = state.documents.get_mut(&uri) {
                    document.apply_changes(&params.content_changes);
                    document.version = version;
                    document.last_edited_tick = state.counter;
                    state.dirty_documents.insert(uri);
                    document.analysis = None;
                    state.workspaces.clear();
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
                let result = if let Some(result) = st.documents.get(&uri) {
                    let formatted = crate::formatter::format_string(&result.text);
                    let newline_count = result.text.matches('\n').count();
                    let ends_with_newline = result.text.ends_with('\n');
                    let last_line = newline_count as u32;
                    let last_char = if ends_with_newline {
                        0
                    } else {
                        result
                            .text
                            .rsplit('\n')
                            .next()
                            .map(|s| s.len())
                            .unwrap_or(result.text.len()) as u32
                    };

                    Ok(Some(vec![TextEdit::new(
                        Range::new(
                            Position::new(0, 0),
                            Position::new(last_line, last_char),
                        ),
                        formatted,
                    )]))
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
                let core = core_analysis(st);

                async move {
                    let Some(byte_offset) = byte_offset else {
                        return Ok(None);
                    };

                    let Some(workspace) = workspace else {
                        return Ok(None);
                    };

                    Ok(hover_at_lsp(&workspace, core.as_deref(), &uri, byte_offset))
                }
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

                async move {
                    let Some(byte_offset) = byte_offset else {
                        return Ok(None);
                    };

                    let Some(workspace) = workspace else {
                        return Ok(None);
                    };

                    Ok(rename_at(&workspace, &uri, byte_offset, &new_name))
                }
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
                let core = core_analysis(st);

                async move {
                    let Some(byte_offset) = byte_offset else {
                        return Ok(None);
                    };

                    let Some(workspace) = workspace else {
                        return Ok(None);
                    };

                    let Some(target) =
                        goto_definition(&workspace, core.as_deref(), &uri, byte_offset)
                    else {
                        return Ok(None);
                    };

                    Ok(Some(GotoDefinitionResponse::Scalar(target)))
                }
            })
            .request::<request::Completion, _>(|st, params| {
                let uri = params.text_document_position.text_document.uri.clone();
                let position = params.text_document_position.position;

                let byte_offset = st
                    .documents
                    .get(&uri)
                    .and_then(|document| document.byte_offset(position).map(|o| o as u32));
                let workspace = workspace_analysis(st, &uri);

                async move {
                    let Some(byte_offset) = byte_offset else {
                        return Ok(None);
                    };

                    let Some(workspace) = workspace else {
                        return Ok(Some(CompletionResponse::Array(vec![])));
                    };

                    let document_id = document_id_for_uri(&uri);
                    let items = analysis_completion::complete_in_workspace(
                        &workspace,
                        &document_id,
                        byte_offset,
                    );
                    let items = completion::to_lsp_items(items);
                    Ok(Some(CompletionResponse::Array(items)))
                }
            })
            .notification::<notification::Initialized>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::DidChangeConfiguration>(|_, _| ControlFlow::Continue(()))
            .request::<request::CodeActionRequest, _>(|state, params| {
                let uri = params.text_document.uri.clone();
                let range = params.range;
                let workspace = workspace_analysis(state, &uri);

                async move {
                    let Some(workspace) = workspace else {
                        return Ok(None);
                    };

                    let document_id = document_id_for_uri(&uri);
                    let actions = compute_code_actions(&workspace, &document_id, &uri, range);
                    if actions.is_empty() {
                        Ok(None)
                    } else {
                        Ok(Some(actions))
                    }
                }
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

                for document_url in ready {
                    if is_tlk_uri(&document_url)
                        && let Some(root) = analysis_root_for_uri(state, &document_url)
                    {
                        diagnostics_workspaces
                            .entry(root)
                            .or_insert_with(|| document_url.clone());
                    }

                    if let Some(document) = state.documents.get_mut(&document_url) {
                        document.semantic_tokens =
                            Some(SemanticTokensResult::Tokens(SemanticTokens {
                                result_id: None,
                                data: collect(document.text.clone()),
                            }));

                        let client = state.client.clone();
                        spawn(async move {
                            client
                                .request::<request::SemanticTokensRefresh>(())
                                .await
                                .ok();
                        });

                        document.analysis = None;
                    }
                    state.dirty_documents.remove(&document_url);
                }

                for focus_uri in diagnostics_workspaces.values() {
                    if let Some(workspace) = workspace_analysis(state, focus_uri) {
                        publish_workspace_diagnostics(state, &workspace);
                    }
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
    // Open (or create) a file for logs
    #[allow(clippy::expect_used)]
    let file = File::options()
        .create(true)
        .write(true)
        .truncate(true)
        .open("server.log")
        .expect("Could not create LSP server log");

    tracing_subscriber::fmt()
        .with_max_level(Level::TRACE)
        .with_ansi(false)
        .with_writer(file)
        .with_target(false)
        .with_file(false)
        .with_line_number(false)
        .init();

    // Prefer truly asynchronous piped stdin/stdout without blocking tasks.
    #[cfg(unix)]
    #[allow(clippy::unwrap_used)]
    let (stdin, stdout) = (
        async_lsp::stdio::PipeStdin::lock_tokio().unwrap(),
        async_lsp::stdio::PipeStdout::lock_tokio().unwrap(),
    );
    // Fallback to spawn blocking read/write otherwise.
    #[cfg(not(unix))]
    let (stdin, stdout) = (
        tokio_util::compat::TokioAsyncReadCompatExt::compat(tokio::io::stdin()),
        tokio_util::compat::TokioAsyncWriteCompatExt::compat_write(tokio::io::stdout()),
    );

    #[allow(clippy::unwrap_used)]
    server.run_buffered(stdin, stdout).await.unwrap();
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

    let analysis = AnalysisWorkspace::new(docs)?;
    let analysis = Arc::new(analysis);
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

fn core_analysis(state: &mut ServerState) -> Option<Arc<AnalysisWorkspace>> {
    if let Some(core) = state.core.as_ref() {
        return Some(core.clone());
    }

    let core = AnalysisWorkspace::core()?;
    let core = Arc::new(core);
    state.core = Some(core.clone());
    Some(core)
}

pub(crate) fn document_id_for_uri(uri: &Url) -> DocumentId {
    uri.as_str().to_string()
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
        source: Some("talk".to_string()),
        message: diagnostic.message.clone(),
        ..Diagnostic::default()
    })
}

fn hover_at_lsp(
    workspace: &AnalysisWorkspace,
    core: Option<&AnalysisWorkspace>,
    uri: &Url,
    byte_offset: u32,
) -> Option<Hover> {
    let document_id = document_id_for_uri(uri);
    let hover = analysis_hover::hover_at(workspace, core, &document_id, byte_offset)?;
    let text = workspace.text_for(&document_id)?;
    Some(hover_to_lsp(text, hover))
}

fn hover_to_lsp(text: &str, hover: AnalysisHover) -> Hover {
    let range = hover
        .range
        .and_then(|range| byte_span_to_range_utf16(text, range.start, range.end));
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```talk\n{}\n```", hover.contents),
        }),
        range,
    }
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

/// Compute code actions for a document, including auto-import suggestions
fn compute_code_actions(
    workspace: &AnalysisWorkspace,
    document_id: &DocumentId,
    uri: &Url,
    range: Range,
) -> CodeActionResponse {
    let mut actions: Vec<CodeActionOrCommand> = Vec::new();

    // Get diagnostics for this document
    let Some(diagnostics) = workspace.diagnostics.get(document_id) else {
        return actions;
    };

    // Get the file ID for this document
    let Some(&file_id) = workspace.document_to_file_id.get(document_id) else {
        return actions;
    };

    // Get the text for this document
    let Some(text) = workspace.texts.get(file_id.0 as usize) else {
        return actions;
    };

    // Build an index of public symbols from all other files
    // Map from symbol name -> (source file path, symbol)
    let mut public_exports: FxHashMap<String, Vec<(String, crate::name_resolution::symbol::Symbol)>> =
        FxHashMap::default();

    for (idx, doc_id) in workspace.file_id_to_document.iter().enumerate() {
        if doc_id == document_id {
            continue; // Skip current file
        }

        let target_file_id = crate::node_id::FileID(idx as u32);
        let scope_id = crate::node_id::NodeID(target_file_id, 0);

        if let Some(scope) = workspace.resolved_names.scopes.get(&scope_id) {
            for (name, &symbol) in &scope.values {
                if workspace.resolved_names.public_symbols.contains(&symbol) {
                    public_exports
                        .entry(name.clone())
                        .or_default()
                        .push((doc_id.clone(), symbol));
                }
            }
            for (name, &symbol) in &scope.types {
                if workspace.resolved_names.public_symbols.contains(&symbol) {
                    public_exports
                        .entry(name.clone())
                        .or_default()
                        .push((doc_id.clone(), symbol));
                }
            }
        }
    }

    // Check each diagnostic for undefined name errors
    for diagnostic in diagnostics {
        // Only handle diagnostics that are in the range
        let diag_range = byte_span_to_range_utf16(text, diagnostic.range.start, diagnostic.range.end);
        let Some(diag_range) = diag_range else { continue };

        // Check if this diagnostic intersects with the requested range
        if diag_range.end.line < range.start.line
            || diag_range.start.line > range.end.line
        {
            continue;
        }

        // Check if this is an "undefined name" diagnostic
        if !diagnostic.message.starts_with("Undefined name:") {
            continue;
        }

        // Extract the undefined name from the message
        let Some(name) = diagnostic.message.strip_prefix("Undefined name: ") else {
            continue;
        };

        // Look up if this name exists as a public export
        if let Some(sources) = public_exports.get(name) {
            for (source_path, _symbol) in sources {
                // Compute relative path from current file to source file
                let current_path = std::path::Path::new(document_id);
                let source_path_obj = std::path::Path::new(source_path);

                let relative_path = if let (Some(current_dir), Some(source_file)) = (
                    current_path.parent(),
                    source_path_obj.file_name(),
                ) {
                    // Simple case: both files in same directory
                    if current_dir == source_path_obj.parent().unwrap_or(std::path::Path::new("")) {
                        format!("./{}", source_file.to_string_lossy())
                    } else {
                        source_path.clone()
                    }
                } else {
                    source_path.clone()
                };

                // Create the import statement
                let import_stmt = format!("import {{ {} }} from {}\n", name, relative_path);

                // Find where to insert (at the start of the file, after any existing imports)
                let insert_position = Position::new(0, 0);

                let edit = TextEdit::new(
                    Range::new(insert_position, insert_position),
                    import_stmt,
                );

                let mut changes: std::collections::HashMap<Url, Vec<TextEdit>> =
                    std::collections::HashMap::new();
                changes.insert(uri.clone(), vec![edit]);

                let action = CodeAction {
                    title: format!("Import '{}' from {}", name, relative_path),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: Some(vec![Diagnostic {
                        range: diag_range,
                        severity: Some(DiagnosticSeverity::ERROR),
                        source: Some("talk".to_string()),
                        message: diagnostic.message.clone(),
                        ..Default::default()
                    }]),
                    edit: Some(WorkspaceEdit {
                        changes: Some(changes),
                        document_changes: None,
                        change_annotations: None,
                    }),
                    command: None,
                    is_preferred: Some(sources.len() == 1),
                    disabled: None,
                    data: None,
                };

                actions.push(CodeActionOrCommand::CodeAction(action));
            }
        }
    }

    actions
}

#[cfg(test)]
mod tests {
    use super::{AnalysisWorkspace, DocumentInput};
    use crate::lsp::document::Document;
    use async_lsp::ClientSocket;
    use async_lsp::lsp_types::HoverContents;
    use async_lsp::lsp_types::Range;
    use async_lsp::lsp_types::Url;
    use async_lsp::lsp_types::WorkspaceEdit;
    use std::path::PathBuf;

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

        let hover = super::hover_at_lsp(&module, None, &uri, byte_offset).expect("hover");
        let HoverContents::Markup(markup) = hover.contents else {
            panic!("unexpected hover: {hover:?}");
        };
        assert!(markup.value.contains("foo: Int"), "{markup:?}");
    }

    #[test]
    fn hover_shows_member_type() {
        let code = r#"struct Foo {
    let bar: Int
}

let foo = Foo(bar: 1)
foo.bar
"#;
        let uri = Url::from_file_path(std::env::temp_dir().join("hover_shows_member_type.tlk"))
            .expect("file uri");

        let module = workspace_for_docs(vec![(uri.clone(), code)]);

        let byte_offset = code.match_indices("bar").last().expect("last bar").0 as u32;

        let hover = super::hover_at_lsp(&module, None, &uri, byte_offset).expect("hover");
        let HoverContents::Markup(markup) = hover.contents else {
            panic!("unexpected hover: {hover:?}");
        };
        assert!(markup.value.contains("bar: Int"), "{markup:?}");
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

        for offset in [id_offsets[0], id_offsets[1], id_offsets[2]] {
            let hover = super::hover_at_lsp(&module, None, &uri, offset as u32).expect("hover");
            let HoverContents::Markup(markup) = hover.contents else {
                panic!("unexpected hover: {hover:?}");
            };

            // Row params are hidden for cleaner display
            assert!(
                markup.value.contains("id: <T>(T) -> T"),
                "{markup:?}"
            );
            assert!(!markup.value.contains("TypeParamId"), "{markup:?}");
            assert!(!markup.value.contains("Int"), "{markup:?}");
            assert!(!markup.value.contains("Float"), "{markup:?}");
        }
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
        let code_b = "import { foo } from ./rename_across_files_a.tlk\nfoo\n";

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Find the "foo" reference in file B (after the import statement)
        let foo_in_b = code_b.rfind("foo").expect("foo");
        let byte_offset = foo_in_b as u32;
        let edit = super::rename_at(&module, &uri_b, byte_offset, "bar").expect("workspace edit");

        let range_a = super::byte_span_to_range_utf16(
            code_a,
            code_a.find("foo").expect("foo") as u32,
            (code_a.find("foo").expect("foo") + 3) as u32,
        )
        .expect("range a");
        // The foo reference in B is at the last occurrence
        let range_b = super::byte_span_to_range_utf16(code_b, foo_in_b as u32, (foo_in_b + 3) as u32)
            .expect("range b");

        assert_eq!(edit_ranges_for_uri(&edit, &uri_a), vec![range_a]);
        assert_eq!(edit_ranges_for_uri(&edit, &uri_b), vec![range_b]);
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
        let code_a = "import { foo } from ./b.tlk\nfoo\n";
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
                analysis: None,
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

        let code_a = r#"import { Person } from ./extend_before_struct_b.tlk
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
        let code_b = "import { foo } from ./a.tlk\nfoo\n";
        std::fs::write(&path_a, code_a).expect("write a");
        std::fs::write(&path_b, code_b).expect("write b");

        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let uri_b = Url::from_file_path(&path_b).expect("uri b");

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Click on "foo" in "import { foo }" - should navigate to definition in a.tlk
        let import_foo_offset = code_b.find("{ foo }").expect("import foo") + 2;
        let target =
            super::goto_definition(&module, None, &uri_b, import_foo_offset as u32).expect("target");

        assert_eq!(target.uri, uri_a, "should navigate to a.tlk");
        // Should point to the definition location in a.tlk
        assert_eq!(target.range.start.line, 0);
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
        let code_b = "import { foo } from ./a.tlk\nfoo\n";
        std::fs::write(&path_a, code_a).expect("write a");
        std::fs::write(&path_b, code_b).expect("write b");

        let uri_a = Url::from_file_path(&path_a).expect("uri a");
        let uri_b = Url::from_file_path(&path_b).expect("uri b");

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        // Click on "./a.tlk" in "from ./a.tlk" - should navigate to a.tlk
        let path_offset = code_b.find("./a.tlk").expect("import path") as u32;
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
                input.rsplit('\n').next().map(|s| s.len()).unwrap_or(input.len())
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
}
