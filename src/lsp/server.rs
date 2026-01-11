struct TickEvent;

use async_lsp::LanguageClient;
use async_lsp::lsp_types::{
    CompletionOptions, Diagnostic, DiagnosticSeverity, Position, Range, SemanticTokens,
    SemanticTokensResult, TextDocumentSyncCapability, TextDocumentSyncKind,
    TextDocumentSyncOptions, TextDocumentSyncSaveOptions, TextEdit,
};
use async_lsp::{
    ClientSocket,
    client_monitor::ClientProcessMonitorLayer,
    concurrency::ConcurrencyLayer,
    lsp_types::{
        CompletionResponse, GotoDefinitionResponse, Hover, HoverContents, HoverProviderCapability,
        InitializeParams, InitializeResult, Location, MarkupContent, MarkupKind, OneOf,
        PublishDiagnosticsParams, SemanticTokensFullOptions, SemanticTokensLegend,
        SemanticTokensOptions, SemanticTokensServerCapabilities, ServerCapabilities,
        TextDocumentItem, Url, WorkspaceEdit, WorkspaceFolder, notification, request,
    },
    panic::CatchUnwindLayer,
    router::Router,
    server::LifecycleLayer,
    tracing::TracingLayer,
};
use derive_visitor::{Drive, Visitor};
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
use crate::compiling::module::ModuleId;
use crate::lexer::Lexer;
use crate::lsp::semantic_tokens::collect;
use crate::lsp::{completion, document::Document, semantic_tokens::TOKEN_TYPES};
use crate::name_resolution::symbol::{EffectId, Symbol};
use crate::node_kinds::{
    decl::Decl,
    expr::Expr,
    func::Func,
    func_signature::FuncSignature,
    generic_decl::GenericDecl,
    parameter::Parameter,
    pattern::{Pattern, RecordFieldPattern},
    type_annotation::TypeAnnotation,
};
use crate::token_kind::TokenKind;

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
                    let last_line = result.text.lines().count() as u32;
                    let last_char = result
                        .text
                        .lines()
                        .last()
                        .map(|line| line.len().saturating_sub(1));

                    Ok(Some(vec![TextEdit::new(
                        Range::new(
                            Position::new(0, 0),
                            Position::new(last_line, last_char.unwrap_or(0) as u32),
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

                    if !is_valid_identifier(&new_name) {
                        return Ok(None);
                    }

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
        .append(true)
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

fn document_id_for_uri(uri: &Url) -> DocumentId {
    uri.as_str().to_string()
}

fn document_path_for_uri(uri: &Url) -> String {
    uri.to_file_path()
        .map(|p| p.display().to_string())
        .unwrap_or_else(|_| uri.as_str().to_string())
}

fn url_from_document_id(id: &DocumentId) -> Option<Url> {
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

fn identifier_span_at_offset(
    meta: &crate::node_meta::NodeMeta,
    byte_offset: u32,
) -> Option<(u32, u32)> {
    meta.identifiers
        .iter()
        .find(|tok| tok.start <= byte_offset && byte_offset <= tok.end)
        .map(|tok| (tok.start, tok.end))
}

fn is_valid_identifier(name: &str) -> bool {
    let mut lexer = Lexer::new(name);
    let Ok(token) = lexer.next() else {
        return false;
    };
    if !matches!(token.kind, TokenKind::Identifier(..)) {
        return false;
    }
    matches!(lexer.next().ok().map(|t| t.kind), Some(TokenKind::EOF))
}

fn is_symbol_renamable(symbol: Symbol) -> bool {
    use crate::name_resolution::symbol::{
        AssociatedTypeId, EnumId, GlobalId, InitializerId, InstanceMethodId, MethodRequirementId,
        PropertyId, ProtocolId, StaticMethodId, StructId, TypeAliasId, VariantId,
    };

    match symbol {
        Symbol::Builtin(..) | Symbol::Main | Symbol::Library | Symbol::Synthesized(..) => false,

        Symbol::Struct(StructId { module_id, .. })
        | Symbol::Enum(EnumId { module_id, .. })
        | Symbol::TypeAlias(TypeAliasId { module_id, .. })
        | Symbol::Global(GlobalId { module_id, .. })
        | Symbol::Property(PropertyId { module_id, .. })
        | Symbol::InstanceMethod(InstanceMethodId { module_id, .. })
        | Symbol::Initializer(InitializerId { module_id, .. })
        | Symbol::StaticMethod(StaticMethodId { module_id, .. })
        | Symbol::Variant(VariantId { module_id, .. })
        | Symbol::Protocol(ProtocolId { module_id, .. })
        | Symbol::AssociatedType(AssociatedTypeId { module_id, .. })
        | Symbol::Effect(EffectId { module_id, .. })
        | Symbol::MethodRequirement(MethodRequirementId { module_id, .. }) => {
            module_id == ModuleId::Current
        }

        Symbol::TypeParameter(..)
        | Symbol::DeclaredLocal(..)
        | Symbol::PatternBindLocal(..)
        | Symbol::ParamLocal(..) => true,
    }
}

fn rename_at(
    module: &AnalysisWorkspace,
    uri: &Url,
    byte_offset: u32,
    new_name: &str,
) -> Option<WorkspaceEdit> {
    let symbol = rename_symbol_at_offset(module, uri, byte_offset)?;
    if !is_symbol_renamable(symbol) {
        return None;
    }

    let mut changes: std::collections::HashMap<Url, Vec<TextEdit>> = Default::default();
    for (idx, doc_id) in module.file_id_to_document.iter().enumerate() {
        let Some(file_uri) = url_from_document_id(doc_id) else {
            continue;
        };
        let text = module.texts.get(idx)?;
        let Some(ast) = module.asts.get(idx).and_then(|a| a.as_ref()) else {
            continue;
        };
        let spans = rename_spans_in_ast(ast, module.types.as_ref(), symbol);

        let mut edits: Vec<TextEdit> = spans
            .into_iter()
            .filter_map(|(start, end)| {
                let range = byte_span_to_range_utf16(text, start, end)?;
                Some(TextEdit::new(range, new_name.to_string()))
            })
            .collect();

        if edits.is_empty() {
            continue;
        }

        edits.sort_by_key(|edit| (edit.range.start.line, edit.range.start.character));
        changes.insert(file_uri, edits);
    }

    if changes.is_empty() {
        return None;
    }

    Some(WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    })
}

fn rename_symbol_at_offset(
    module: &AnalysisWorkspace,
    uri: &Url,
    byte_offset: u32,
) -> Option<Symbol> {
    let document_id = document_id_for_uri(uri);
    let file_id = *module.document_to_file_id.get(&document_id)?;
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|a| a.as_ref())?;
    let candidate_ids = node_ids_at_offset(ast, byte_offset);

    for node_id in candidate_ids {
        let Some(node) = ast.find(node_id) else {
            continue;
        };

        let symbol = match node {
            crate::node::Node::Expr(expr) => {
                goto_definition_symbol_from_expr(module.types.as_ref(), &expr, byte_offset)
            }
            crate::node::Node::Stmt(stmt) => {
                goto_definition_symbol_from_stmt(module.types.as_ref(), &stmt, byte_offset)
            }
            crate::node::Node::TypeAnnotation(ty) => {
                goto_definition_symbol_from_type_annotation(&ty, byte_offset)
            }
            crate::node::Node::Decl(decl) => goto_definition_symbol_from_decl(&decl, byte_offset),
            crate::node::Node::Parameter(param) => {
                if span_contains(param.name_span, byte_offset) {
                    param.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::Func(func) => {
                if span_contains(func.name_span, byte_offset) {
                    func.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::FuncSignature(sig) => {
                let meta = ast.meta.get(&sig.id)?;
                let (start, end) = meta.identifiers.first().map(|t| (t.start, t.end))?;
                if start <= byte_offset && byte_offset <= end {
                    sig.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::GenericDecl(generic) => {
                if span_contains(generic.name_span, byte_offset) {
                    generic.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::Pattern(pattern) => match &pattern.kind {
                crate::node_kinds::pattern::PatternKind::Bind(name) => {
                    let meta = ast.meta.get(&pattern.id)?;
                    let (start, end) = identifier_span_at_offset(meta, byte_offset)?;
                    if start <= byte_offset && byte_offset <= end {
                        name.symbol().ok()
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        };

        if symbol.is_some() {
            return symbol;
        }
    }

    None
}

fn rename_spans_in_ast(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    types: Option<&crate::types::types::Types>,
    symbol: Symbol,
) -> Vec<(u32, u32)> {
    let mut collector = RenameCollector {
        ast,
        types,
        target: symbol,
        spans: FxHashSet::default(),
    };

    for root in &ast.roots {
        root.drive(&mut collector);
    }

    let mut spans: Vec<(u32, u32)> = collector.spans.into_iter().collect();
    spans.sort_unstable();
    spans
}

#[derive(Visitor)]
#[visitor(
    Decl(enter),
    Expr(enter),
    Func(enter),
    FuncSignature(enter),
    GenericDecl(enter),
    Parameter(enter),
    Pattern(enter),
    RecordFieldPattern(enter),
    TypeAnnotation(enter)
)]
struct RenameCollector<'a> {
    ast: &'a crate::ast::AST<crate::ast::NameResolved>,
    types: Option<&'a crate::types::types::Types>,
    target: Symbol,
    spans: FxHashSet<(u32, u32)>,
}

impl RenameCollector<'_> {
    fn push_span(&mut self, span: crate::span::Span) {
        self.spans.insert((span.start, span.end));
    }

    fn push_u32_span(&mut self, start: u32, end: u32) {
        self.spans.insert((start, end));
    }

    fn enter_decl(&mut self, decl: &crate::node_kinds::decl::Decl) {
        use crate::node_kinds::decl::DeclKind;

        match &decl.kind {
            DeclKind::Struct {
                name, name_span, ..
            }
            | DeclKind::Protocol {
                name, name_span, ..
            }
            | DeclKind::Extend {
                name, name_span, ..
            }
            | DeclKind::Enum {
                name, name_span, ..
            }
            | DeclKind::Property {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            DeclKind::TypeAlias(name, name_span, ..)
            | DeclKind::EnumVariant(name, name_span, ..) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            _ => {}
        }
    }

    fn enter_func(&mut self, func: &crate::node_kinds::func::Func) {
        if func.name.symbol().ok() == Some(self.target) {
            self.push_span(func.name_span);
        }
    }

    fn enter_func_signature(&mut self, sig: &crate::node_kinds::func_signature::FuncSignature) {
        if sig.name.symbol().ok() != Some(self.target) {
            return;
        }

        let Some(meta) = self.ast.meta.get(&sig.id) else {
            return;
        };
        let Some(tok) = meta.identifiers.first() else {
            return;
        };
        self.push_u32_span(tok.start, tok.end);
    }

    fn enter_generic_decl(&mut self, generic: &crate::node_kinds::generic_decl::GenericDecl) {
        if generic.name.symbol().ok() == Some(self.target) {
            self.push_span(generic.name_span);
        }
    }

    fn enter_parameter(&mut self, param: &crate::node_kinds::parameter::Parameter) {
        if param.name.symbol().ok() == Some(self.target) {
            self.push_span(param.name_span);
        }
    }

    fn enter_pattern(&mut self, pattern: &crate::node_kinds::pattern::Pattern) {
        use crate::node_kinds::pattern::PatternKind;

        let PatternKind::Bind(name) = &pattern.kind else {
            return;
        };

        if name.symbol().ok() == Some(self.target) {
            self.push_span(pattern.span);
        }
    }

    fn enter_record_field_pattern(
        &mut self,
        field: &crate::node_kinds::pattern::RecordFieldPattern,
    ) {
        use crate::node_kinds::pattern::RecordFieldPatternKind;

        match &field.kind {
            RecordFieldPatternKind::Bind(name) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(field.span);
                }
            }
            RecordFieldPatternKind::Equals {
                name, name_span, ..
            } => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            RecordFieldPatternKind::Rest => {}
        }
    }

    fn enter_type_annotation(&mut self, ty: &crate::node_kinds::type_annotation::TypeAnnotation) {
        use crate::node_kinds::type_annotation::TypeAnnotationKind;

        let TypeAnnotationKind::Nominal {
            name, name_span, ..
        } = &ty.kind
        else {
            return;
        };

        if name.symbol().ok() == Some(self.target) {
            self.push_span(*name_span);
        }
    }

    fn enter_expr(&mut self, expr: &crate::node_kinds::expr::Expr) {
        use crate::node_kinds::expr::ExprKind;

        match &expr.kind {
            ExprKind::Variable(name) | ExprKind::Constructor(name) => {
                if name.symbol().ok() == Some(self.target) {
                    self.push_span(expr.span);
                }
            }
            ExprKind::Member(receiver, label, name_span) => {
                let Some(receiver) = receiver.as_ref() else {
                    return;
                };
                let member_sym = resolve_member_symbol(self.types, receiver, label);
                if member_sym == Some(self.target) {
                    self.push_span(*name_span);
                }
            }
            _ => {}
        }
    }
}

fn goto_definition(
    module: &AnalysisWorkspace,
    core: Option<&AnalysisWorkspace>,
    uri: &Url,
    byte_offset: u32,
) -> Option<Location> {
    let document_id = document_id_for_uri(uri);
    let file_id = *module.document_to_file_id.get(&document_id)?;
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|a| a.as_ref())?;
    let candidate_ids = node_ids_at_offset(ast, byte_offset);

    for node_id in candidate_ids {
        let Some(node) = ast.find(node_id) else {
            continue;
        };

        let symbol = match node {
            crate::node::Node::Expr(expr) => {
                goto_definition_symbol_from_expr(module.types.as_ref(), &expr, byte_offset)
            }
            crate::node::Node::Stmt(stmt) => {
                goto_definition_symbol_from_stmt(module.types.as_ref(), &stmt, byte_offset)
            }
            crate::node::Node::TypeAnnotation(ty) => {
                goto_definition_symbol_from_type_annotation(&ty, byte_offset)
            }
            crate::node::Node::Decl(decl) => goto_definition_symbol_from_decl(&decl, byte_offset),
            crate::node::Node::Parameter(param) => {
                if span_contains(param.name_span, byte_offset) {
                    param.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::Func(func) => {
                if span_contains(func.name_span, byte_offset) {
                    func.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::FuncSignature(sig) => {
                let meta = ast.meta.get(&sig.id)?;
                let (start, end) = meta.identifiers.first().map(|t| (t.start, t.end))?;
                if start <= byte_offset && byte_offset <= end {
                    sig.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::GenericDecl(generic) => {
                if span_contains(generic.name_span, byte_offset) {
                    generic.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::Pattern(pattern) => match &pattern.kind {
                crate::node_kinds::pattern::PatternKind::Bind(name) => {
                    let meta = ast.meta.get(&pattern.id)?;
                    let (start, end) = identifier_span_at_offset(meta, byte_offset)?;
                    if start <= byte_offset && byte_offset <= end {
                        name.symbol().ok()
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        };

        if let Some(symbol) = symbol
            && let Some(target) = definition_location_for_symbol(module, core, symbol)
        {
            return Some(target);
        }
    }

    None
}

fn goto_definition_symbol_from_expr(
    types: Option<&crate::types::types::Types>,
    expr: &crate::node_kinds::expr::Expr,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::expr::ExprKind;

    match &expr.kind {
        ExprKind::Variable(name) | ExprKind::Constructor(name) => name.symbol().ok(),
        ExprKind::Member(receiver, label, name_span) => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }

            let receiver = receiver.as_ref()?;

            resolve_member_symbol(types, receiver, label)
        }
        _ => None,
    }
}

fn goto_definition_symbol_from_stmt(
    types: Option<&crate::types::types::Types>,
    stmt: &crate::node_kinds::stmt::Stmt,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::stmt::StmtKind;

    match &stmt.kind {
        StmtKind::Expr(expr) => goto_definition_symbol_from_expr(types, expr, byte_offset),
        StmtKind::Return(Some(expr)) => goto_definition_symbol_from_expr(types, expr, byte_offset),
        StmtKind::If(cond, ..) => goto_definition_symbol_from_expr(types, cond, byte_offset),
        StmtKind::Loop(Some(cond), ..) => {
            goto_definition_symbol_from_expr(types, cond, byte_offset)
        }
        StmtKind::Assignment(lhs, rhs) => goto_definition_symbol_from_expr(types, lhs, byte_offset)
            .or_else(|| goto_definition_symbol_from_expr(types, rhs, byte_offset)),
        _ => None,
    }
}

fn goto_definition_symbol_from_type_annotation(
    ty: &crate::node_kinds::type_annotation::TypeAnnotation,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    match &ty.kind {
        TypeAnnotationKind::Nominal {
            name, name_span, ..
        } => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        _ => None,
    }
}

fn goto_definition_symbol_from_decl(
    decl: &crate::node_kinds::decl::Decl,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::decl::DeclKind;

    match &decl.kind {
        DeclKind::Struct {
            name, name_span, ..
        }
        | DeclKind::Protocol {
            name, name_span, ..
        }
        | DeclKind::Extend {
            name, name_span, ..
        }
        | DeclKind::Enum {
            name, name_span, ..
        }
        | DeclKind::Property {
            name, name_span, ..
        } => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        DeclKind::TypeAlias(name, name_span, ..) => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        DeclKind::EnumVariant(name, name_span, ..) => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        _ => None,
    }
}

fn resolve_member_symbol(
    types: Option<&crate::types::types::Types>,
    receiver: &crate::node_kinds::expr::Expr,
    label: &crate::label::Label,
) -> Option<Symbol> {
    use crate::node_kinds::expr::ExprKind;
    use crate::types::ty::Ty;

    if let ExprKind::Constructor(name) = &receiver.kind {
        let receiver_symbol = name.symbol().ok()?;
        let types = types?;
        return types.catalog.lookup_static_member(&receiver_symbol, label);
    }

    let types = types?;
    let entry = types.get(&receiver.id)?;
    let ty = entry.as_mono_ty();

    match ty {
        Ty::Nominal { symbol, .. } => types.catalog.lookup_member(symbol, label).map(|m| m.0),
        Ty::Primitive(symbol) => types.catalog.lookup_member(symbol, label).map(|m| m.0),
        _ => None,
    }
}

fn definition_location_for_symbol(
    module: &AnalysisWorkspace,
    core: Option<&AnalysisWorkspace>,
    symbol: Symbol,
) -> Option<Location> {
    if let Some(module_id) = symbol.external_module_id() {
        if module_id == ModuleId::Core {
            let core = core?;
            return definition_location_in_module(core, symbol);
        }
        return None;
    }

    definition_location_in_module(module, symbol)
}

fn definition_location_in_module(module: &AnalysisWorkspace, symbol: Symbol) -> Option<Location> {
    let def_node = *module.resolved_names.symbols_to_node.get(&symbol)?;
    let file_id = def_node.0;
    let doc_id = module.file_id_to_document.get(file_id.0 as usize)?;
    let uri = url_from_document_id(doc_id)?;
    let text = module.texts.get(file_id.0 as usize)?;
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|a| a.as_ref())?;

    let meta = ast.meta.get(&def_node)?;
    let (start, end) = match meta.identifiers.first() {
        Some(tok) => (tok.start, tok.end),
        None => (meta.start.start, meta.end.end),
    };
    let range = byte_span_to_range_utf16(text, start, end)?;

    Some(Location { uri, range })
}

fn node_ids_at_offset(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    byte_offset: u32,
) -> Vec<crate::node_id::NodeID> {
    let mut candidates: Vec<(crate::node_id::NodeID, u32)> = ast
        .meta
        .iter()
        .filter_map(|(id, meta)| {
            let start = meta.start.start;
            let end = meta.end.end;
            if start <= byte_offset && byte_offset <= end {
                Some((*id, end.saturating_sub(start)))
            } else {
                None
            }
        })
        .collect();

    candidates.sort_by_key(|(_, len)| *len);
    candidates.into_iter().map(|(id, _)| id).collect()
}

fn byte_span_to_range_utf16(text: &str, start: u32, end: u32) -> Option<Range> {
    let start = byte_offset_to_utf16_position(text, start)?;
    let end = byte_offset_to_utf16_position(text, end)?;
    Some(Range::new(start, end))
}

fn span_contains(span: crate::span::Span, byte_offset: u32) -> bool {
    span.start <= byte_offset && byte_offset <= span.end
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

            // Effect row is now polymorphic for functions without declared effects
            assert!(
                markup.value.contains("id: <T, R>(T) ..R -> T"),
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
        let code_a = "let foo = 1\n";
        let code_b = "foo\n";

        let module = workspace_for_docs(vec![(uri_a.clone(), code_a), (uri_b.clone(), code_b)]);

        let byte_offset = code_b.find("foo").expect("foo") as u32;
        let edit = super::rename_at(&module, &uri_b, byte_offset, "bar").expect("workspace edit");

        let range_a = super::byte_span_to_range_utf16(
            code_a,
            code_a.find("foo").expect("foo") as u32,
            (code_a.find("foo").expect("foo") + 3) as u32,
        )
        .expect("range a");
        let range_b = super::byte_span_to_range_utf16(code_b, 0, 3).expect("range b");

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
        let code_a = "foo\n";
        let code_b = "let foo = 1\n";
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
        let byte_offset = code_a.find("foo").expect("foo") as u32;

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

        let code_a = r#"
extend Person {
  func foo() {}
}
"#;
        let code_b = "struct Person {}\n";

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
}
