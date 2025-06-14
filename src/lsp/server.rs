use std::collections::HashMap;
use std::ops::ControlFlow;
use std::path::PathBuf;
use std::time::Duration;

use async_lsp::LanguageClient;
use async_lsp::client_monitor::ClientProcessMonitorLayer;
use async_lsp::concurrency::ConcurrencyLayer;
use async_lsp::lsp_types::notification::DidChangeWatchedFiles;
use async_lsp::lsp_types::{
    DidChangeConfigurationParams, DidChangeTextDocumentParams, DidChangeWatchedFilesParams,
    DidOpenTextDocumentParams, DidSaveTextDocumentParams, Hover, HoverContents, HoverParams,
    HoverProviderCapability, InitializeParams, InitializeResult, MarkedString, MessageType, OneOf,
    SemanticTokenType, SemanticTokens, SemanticTokensFullOptions, SemanticTokensLegend,
    SemanticTokensOptions, SemanticTokensParams, SemanticTokensResult,
    SemanticTokensServerCapabilities, ServerCapabilities, ShowMessageParams,
    TextDocumentSyncCapability, TextDocumentSyncKind, Url,
};
use async_lsp::panic::CatchUnwindLayer;
use async_lsp::router::Router;
use async_lsp::server::LifecycleLayer;
use async_lsp::tracing::TracingLayer;
use async_lsp::{ClientSocket, LanguageServer, ResponseError};
use futures::future::BoxFuture;
use tower::ServiceBuilder;

use crate::lsp::semantic_tokens;
use crate::parser::parse;

pub const TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::KEYWORD,
    SemanticTokenType::VARIABLE,
    SemanticTokenType::FUNCTION,
    SemanticTokenType::PARAMETER,
    SemanticTokenType::NUMBER,
    SemanticTokenType::TYPE,
    SemanticTokenType::ENUM_MEMBER,
    SemanticTokenType::STRUCT,
    SemanticTokenType::ENUM,
    SemanticTokenType::TYPE_PARAMETER,
    SemanticTokenType::OPERATOR,
    SemanticTokenType::METHOD,
];

#[allow(dead_code)]
struct ServerState {
    client: ClientSocket,
    counter: i32,
    src_cache: HashMap<Url, String>,
}

impl LanguageServer for ServerState {
    type Error = ResponseError;
    type NotifyResult = ControlFlow<async_lsp::Result<()>>;

    fn initialize(
        &mut self,
        _params: InitializeParams,
    ) -> BoxFuture<'static, Result<InitializeResult, Self::Error>> {
        Box::pin(async move {
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
                    text_document_sync: Some(TextDocumentSyncCapability::Kind(
                        TextDocumentSyncKind::FULL,
                    )),

                    ..ServerCapabilities::default()
                },
                server_info: None,
            })
        })
    }

    fn semantic_tokens_full(
        &mut self,
        params: SemanticTokensParams,
    ) -> BoxFuture<'static, Result<Option<SemanticTokensResult>, Self::Error>> {
        let contents = if let Some(contents) = self.src_cache.get(&params.text_document.uri) {
            contents.clone()
        } else {
            match std::fs::read_to_string(params.text_document.uri.path()) {
                Ok(s) => {
                    self.src_cache
                        .insert(params.text_document.uri.clone(), s.clone());
                    s
                }
                Err(e) => {
                    eprintln!("Failed to read file: {:?}", e);
                    return Box::pin(async { Ok(None) }); // Return None instead of error
                }
            }
        };

        let source_file = match parse(&contents, 0) {
            Ok(sf) => sf,
            Err(e) => {
                eprintln!("Failed to parse file: {:?}", e);
                // Return empty tokens instead of error
                return Box::pin(async { Ok(None) });
            }
        };

        Box::pin(async {
            Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
                result_id: None,
                data: semantic_tokens::collect(source_file, contents).clone(),
            })))
        })
    }

    fn hover(&mut self, _: HoverParams) -> BoxFuture<'static, Result<Option<Hover>, Self::Error>> {
        let mut client = self.client.clone();
        let counter = self.counter;
        Box::pin(async move {
            tokio::time::sleep(Duration::from_secs(1)).await;
            client
                .show_message(ShowMessageParams {
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
        })
    }

    fn did_open(&mut self, params: DidOpenTextDocumentParams) -> Self::NotifyResult {
        let Ok(path) = params.text_document.uri.to_file_path() else {
            return ControlFlow::Continue(());
        };

        let Ok(contents) = std::fs::read_to_string(&path) else {
            return ControlFlow::Continue(());
        };

        self.src_cache.insert(params.text_document.uri, contents);
        self.refresh_semantic_tokens();
        ControlFlow::Continue(())
    }

    fn did_save(&mut self, params: DidSaveTextDocumentParams) -> Self::NotifyResult {
        if let Some(text) = params.text {
            self.src_cache
                .insert(params.text_document.uri, text.to_string());
            self.refresh_semantic_tokens();
        }
        self.refresh_semantic_tokens();
        ControlFlow::Continue(())
    }

    fn did_change(&mut self, params: DidChangeTextDocumentParams) -> Self::NotifyResult {
        if let Some(change) = params.content_changes.first() {
            self.src_cache
                .insert(params.text_document.uri, change.text.to_string());
            self.refresh_semantic_tokens();
        }

        ControlFlow::Continue(())
    }

    // fn definition(
    //     &mut self,
    //     _: GotoDefinitionParams,
    // ) -> BoxFuture<'static, Result<Option<GotoDefinitionResponse>, ResponseError>> {
    //     unimplemented!("Not yet implemented!");
    // }

    fn did_change_configuration(
        &mut self,
        _: DidChangeConfigurationParams,
    ) -> ControlFlow<async_lsp::Result<()>> {
        ControlFlow::Continue(())
    }
}

struct TickEvent;

impl ServerState {
    fn new_router(client: ClientSocket) -> Router<Self> {
        let mut router = Router::from_language_server(Self {
            client,
            counter: 0,
            src_cache: Default::default(),
        });
        router.event(Self::on_tick);
        router
    }

    fn on_tick(&mut self, _: TickEvent) -> ControlFlow<async_lsp::Result<()>> {
        // log::info!("tick");
        self.counter += 1;
        ControlFlow::Continue(())
    }

    fn refresh_semantic_tokens(&self) {
        let mut client = self.client.clone();
        tokio::spawn(async move {
            client.semantic_tokens_refresh(()).await.ok();
        });
    }
}

pub async fn start() {
    log::info!("Starting LSP…");

    let (server, _) = async_lsp::MainLoop::new_server(|client| {
        tokio::spawn({
            let client = client.clone();
            async move {
                let mut interval = tokio::time::interval(Duration::from_secs(1));
                loop {
                    interval.tick().await;
                    if client.emit(TickEvent).is_err() {
                        break;
                    }
                }
            }
        });

        ServiceBuilder::new()
            .layer(TracingLayer::default())
            .layer(LifecycleLayer::default())
            .layer(CatchUnwindLayer::default())
            .layer(ConcurrencyLayer::default())
            .layer(ClientProcessMonitorLayer::new(client.clone()))
            .service(ServerState::new_router(client))
    });

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

    match server.run_buffered(stdin, stdout).await {
        Ok(()) => {
            eprintln!("All done.");
        }
        Err(e) => eprintln!("server.run_buffered err: {:?}", e),
    }
}
