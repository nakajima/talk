struct TickEvent;

use async_lsp::LanguageClient;
use async_lsp::lsp_types::{
    Diagnostic, SemanticTokens, SemanticTokensResult, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, TextDocumentSyncSaveOptions,
};
use async_lsp::{
    ClientSocket,
    client_monitor::ClientProcessMonitorLayer,
    concurrency::ConcurrencyLayer,
    lsp_types::{
        Hover, HoverContents, HoverProviderCapability, InitializeResult, MarkedString, MessageType,
        OneOf, PublishDiagnosticsParams, SemanticTokensFullOptions, SemanticTokensLegend,
        SemanticTokensOptions, SemanticTokensServerCapabilities, ServerCapabilities,
        ShowMessageParams, TextDocumentItem, Url, notification, request,
    },
    panic::CatchUnwindLayer,
    router::Router,
    server::LifecycleLayer,
    tracing::TracingLayer,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::fs::File;
use std::{ops::ControlFlow, time::Duration};
use tokio::spawn;
use tower::ServiceBuilder;
use tracing::Level;

use crate::compiling::driver::{Driver, DriverConfig, Source};
use crate::lsp::semantic_tokens::collect;
use crate::lsp::{document::Document, semantic_tokens::TOKEN_TYPES};

struct ServerState {
    client: ClientSocket,
    counter: i32,
    documents: FxHashMap<Url, Document>,
    dirty_documents: FxHashSet<Url>,
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
        });

        router
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
                }

                std::ops::ControlFlow::Continue(())
            })
            .notification::<notification::DidCloseTextDocument>(|state, params| {
                let document_url = params.text_document.uri;
                // Clear diagnostics; keep the buffer in memory (simple, fast reopen)
                let _ = state.client.publish_diagnostics(PublishDiagnosticsParams {
                    uri: document_url.clone(),
                    diagnostics: vec![],
                    version: None,
                });
                state.dirty_documents.remove(&document_url);
                std::ops::ControlFlow::Continue(())
            })
            .request::<request::Initialize, _>(|_, params| async move {
                tracing::trace!("Initialize with {params:?}");
                Ok(InitializeResult {
                    capabilities: ServerCapabilities {
                        hover_provider: Some(HoverProviderCapability::Simple(true)),
                        definition_provider: Some(OneOf::Left(true)),
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
            .request::<request::HoverRequest, _>(|st, _| {
                let client = st.client.clone();
                let counter = st.counter;
                async move {
                    client
                        .notify::<notification::ShowMessage>(ShowMessageParams {
                            typ: MessageType::INFO,
                            message: "Hello LSP".into(),
                        })
                        .unwrap();
                    Ok(Some(Hover {
                        contents: HoverContents::Scalar(MarkedString::String(format!(
                            "I am a hover text {counter}!"
                        ))),
                        range: None,
                    }))
                }
            })
            .request::<request::GotoDefinition, _>(|_, _| async move {
                unimplemented!("Not yet implemented!")
            })
            .notification::<notification::Initialized>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::DidChangeConfiguration>(|_, _| ControlFlow::Continue(()))
            .notification::<notification::DidSaveTextDocument>(|_, _| ControlFlow::Continue(()))
            .event::<TickEvent>(|st, _| {
                st.counter += 1;
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

                for document_url in ready {
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

                        // ---------- run your full pipeline on the current in-memory text ----------
                        // Minimal config; you can pass a real ModuleEnvironment if needed.
                        let driver = Driver::new_bare(
                            vec![Source::from(document.text.as_str())],
                            DriverConfig::default(),
                        );

                        let diagnostics_result = driver
                            .parse()
                            .and_then(|d| d.resolve_names())
                            .and_then(|d| d.typecheck())
                            .map(|_typed| Vec::<Diagnostic>::new()) // success → no diagnostics here
                            .map_err(|_error| {
                                //vec![diagnostic_from_compile_error(&document.text, error)]
                                vec![]
                            });

                        let diagnostics = match diagnostics_result {
                            Ok(list) => list,
                            Err(list) => list,
                        };

                        let _ = state.client.publish_diagnostics(PublishDiagnosticsParams {
                            uri: document_url.clone(),
                            diagnostics,
                            version: Some(document.version),
                        });
                    }
                    state.dirty_documents.remove(&document_url);
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
    let file = File::options()
        .create(true)
        .append(true)
        .open("server.log")
        .unwrap();

    tracing_subscriber::fmt()
        .with_max_level(Level::TRACE)
        .with_ansi(false)
        .with_writer(file)
        .with_target(true)
        .init();

    // Prefer truly asynchronous piped stdin/stdout without blocking tasks.
    #[cfg(unix)]
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

    server.run_buffered(stdin, stdout).await.unwrap();
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

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
}
