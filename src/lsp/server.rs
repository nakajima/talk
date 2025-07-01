use std::ops::ControlFlow;
use std::time::Duration;

use async_lsp::LanguageClient;
use async_lsp::client_monitor::ClientProcessMonitorLayer;
use async_lsp::concurrency::ConcurrencyLayer;
use async_lsp::lsp_types::{
    CompletionOptions, CompletionParams, CompletionResponse, CompletionTriggerKind,
    DiagnosticOptions, DidChangeConfigurationParams, DidChangeTextDocumentParams,
    DidChangeWatchedFilesParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DidSaveTextDocumentParams, DocumentDiagnosticParams, DocumentDiagnosticReport,
    DocumentDiagnosticReportResult, DocumentFormattingParams, FullDocumentDiagnosticReport,
    GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverParams, HoverProviderCapability,
    InitializeParams, InitializeResult, Location, OneOf, Position, Range,
    RelatedFullDocumentDiagnosticReport, RelatedUnchangedDocumentDiagnosticReport,
    SemanticTokenType, SemanticTokens, SemanticTokensFullOptions, SemanticTokensLegend,
    SemanticTokensOptions, SemanticTokensParams, SemanticTokensResult,
    SemanticTokensServerCapabilities, ServerCapabilities, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextEdit, UnchangedDocumentDiagnosticReport, Url,
};
use async_lsp::panic::CatchUnwindLayer;
use async_lsp::router::Router;
use async_lsp::server::LifecycleLayer;
use async_lsp::tracing::TracingLayer;
use async_lsp::{ClientSocket, LanguageServer, ResponseError};
use futures::future::BoxFuture;
use tower::ServiceBuilder;

use crate::compiling::driver::Driver;
use crate::environment::Environment;
use crate::lexer::Lexer;
use crate::lsp::completion::CompletionContext;
use crate::lsp::formatter::format;
use crate::lsp::semantic_tokens;
use crate::parser::Parser;

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
    SemanticTokenType::PROPERTY,
];

#[allow(dead_code)]
struct ServerState {
    client: ClientSocket,
    counter: i32,
    driver: Driver,
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
                    document_formatting_provider: Some(OneOf::Left(true)),
                    completion_provider: Some(CompletionOptions {
                        resolve_provider: Some(false),
                        trigger_characters: Some(vec![".".to_string(), ":".to_string()]),
                        ..Default::default()
                    }),
                    diagnostic_provider: Some(
                        async_lsp::lsp_types::DiagnosticServerCapabilities::Options(
                            DiagnosticOptions {
                                ..Default::default()
                            },
                        ),
                    ),
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

    fn definition(
        &mut self,
        params: GotoDefinitionParams,
    ) -> BoxFuture<'static, Result<Option<GotoDefinitionResponse>, Self::Error>> {
        let Ok(_path) = params
            .text_document_position_params
            .text_document
            .uri
            .to_file_path()
        else {
            log::error!(
                "no file path from: {:?}",
                params.text_document_position_params.text_document.uri
            );
            return Box::pin(async { Ok(None) });
        };

        let position = params.text_document_position_params.position;

        let Some((_, symbol_id)) = self
            .driver
            .symbol_table
            .symbol_map
            .iter()
            .find(|(span, _)| {
                span.contains(&crate::diagnostic::Position {
                    line: position.line,
                    col: position.character,
                })
            })
        else {
            return Box::pin(async { Ok(None) });
        };

        let Some(info) = self.driver.symbol_table.get(symbol_id) else {
            return Box::pin(async { Ok(None) });
        };

        let Some(definition) = &info.definition else {
            return Box::pin(async { Ok(None) });
        };

        let Ok(path) = Url::from_file_path(definition.path.clone()) else {
            return Box::pin(async { Ok(None) });
        };

        let response = GotoDefinitionResponse::Scalar(Location::new(
            path,
            Range {
                start: Position::new(definition.line, definition.col),
                end: Position::new(definition.line, definition.col),
            },
        ));

        Box::pin(async { Ok(Some(response)) })
    }

    fn completion(
        &mut self,
        params: CompletionParams,
    ) -> BoxFuture<'static, Result<Option<CompletionResponse>, Self::Error>> {
        log::info!("completions requested: {params:?}");

        let Ok(path) = params
            .text_document_position
            .text_document
            .uri
            .to_file_path()
        else {
            log::error!(
                "no file path from: {:?}",
                params.text_document_position.text_document.uri
            );
            return Box::pin(async { Ok(None) });
        };

        let position = params.text_document_position.position;

        // Get the typed AST for the file
        let Some(source_file) = self.driver.typed_source_file(&path) else {
            return Box::pin(async { Ok(None) });
        };

        let completion = CompletionContext {
            source_file: &source_file,
            driver: &self.driver,
            env: &self.driver.units[0].env,
            position,
            is_member_lookup: params
                .context
                .map(|c| c.trigger_kind == CompletionTriggerKind::TRIGGER_CHARACTER)
                .unwrap_or(false),
        };
        let completion_items = completion.get_completions();
        log::info!("completion_items: {completion_items:?}");
        Box::pin(async move {
            if completion_items.is_empty() {
                Ok(None)
            } else {
                Ok(Some(CompletionResponse::Array(completion_items)))
            }
        })
    }

    fn document_diagnostic(
        &mut self,
        params: DocumentDiagnosticParams,
    ) -> BoxFuture<'static, Result<DocumentDiagnosticReportResult, Self::Error>> {
        let Ok(path) = params.text_document.uri.to_file_path() else {
            log::error!("no file path from: {:?}", params.text_document.uri);
            return Box::pin(async {
                Ok(DocumentDiagnosticReportResult::Report(
                    DocumentDiagnosticReport::Unchanged(RelatedUnchangedDocumentDiagnosticReport {
                        related_documents: None,
                        unchanged_document_diagnostic_report: UnchangedDocumentDiagnosticReport {
                            result_id: "".into(),
                        },
                    }),
                ))
            });
        };

        log::trace!("Getting diagnostics");

        let diagnostics = self.driver.diagnostics(&path);

        Box::pin(async {
            Ok(DocumentDiagnosticReportResult::Report(
                DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
                    related_documents: None,
                    full_document_diagnostic_report: FullDocumentDiagnosticReport {
                        result_id: None,
                        items: diagnostics,
                    },
                }),
            ))
        })
    }

    fn semantic_tokens_full(
        &mut self,
        params: SemanticTokensParams,
    ) -> BoxFuture<'static, Result<Option<SemanticTokensResult>, Self::Error>> {
        let Ok(path) = params.text_document.uri.to_file_path() else {
            log::error!("no file path from: {:?}", params.text_document.uri);
            return Box::pin(async { Ok(None) });
        };

        let Some(source_file) = self.driver.parsed_source_file(&path) else {
            eprintln!("Failed to find parsed file: {:?}", params.text_document.uri);
            return Box::pin(async { Ok(None) });
        };

        let response = Ok(Some(SemanticTokensResult::Tokens(
            SemanticTokens {
                result_id: None,
                data: semantic_tokens::collect(source_file, self.driver.contents(&path)),
            }
            .clone(),
        )));

        Box::pin(async { response })
    }

    fn hover(
        &mut self,
        params: HoverParams,
    ) -> BoxFuture<'static, Result<Option<Hover>, Self::Error>> {
        let Ok(_path) = params
            .text_document_position_params
            .text_document
            .uri
            .to_file_path()
        else {
            log::error!(
                "no file path from: {:?}",
                params.text_document_position_params.text_document.uri
            );
            return Box::pin(async { Ok(None) });
        };

        Box::pin(async { Ok(None) })
    }

    fn formatting(
        &mut self,
        params: DocumentFormattingParams,
    ) -> BoxFuture<'static, Result<Option<Vec<TextEdit>>, Self::Error>> {
        let Some(code) = self.fetch(&params.text_document.uri) else {
            return Box::pin(async { Ok(None) });
        };

        let Ok(path) = params.text_document.uri.to_file_path() else {
            return Box::pin(async { Ok(None) });
        };

        let mut env = Environment::default();
        let lexer = Lexer::new(&code);
        let mut parser = Parser::new(self.driver.session.clone(), lexer, path, &mut env);
        parser.parse();
        let source_file = parser.parse_tree;

        Box::pin(async move {
            let formatted = format(&source_file, 80);
            let last_line = code.lines().count() as u32;
            let last_char = code.lines().last().map(|line| line.len() - 1);

            Ok(Some(vec![TextEdit::new(
                Range::new(
                    Position::new(0, 0),
                    Position::new(last_line, last_char.unwrap_or(0) as u32),
                ),
                formatted,
            )]))
        })
    }

    fn did_open(&mut self, params: DidOpenTextDocumentParams) -> Self::NotifyResult {
        let Ok(path) = params.text_document.uri.to_file_path() else {
            return ControlFlow::Continue(());
        };

        let Ok(contents) = std::fs::read_to_string(&path) else {
            return ControlFlow::Continue(());
        };

        if !self.driver.has_file(&path) {
            // TODO: Add additional files
            self.driver.update_file(&path, contents.clone());
        }

        self.driver.update_file(&path, contents);
        self.refresh_semantic_tokens();
        ControlFlow::Continue(())
    }

    fn did_save(&mut self, params: DidSaveTextDocumentParams) -> Self::NotifyResult {
        let Ok(path) = params.text_document.uri.to_file_path() else {
            log::error!("no file path from: {:?}", params.text_document.uri);
            return ControlFlow::Continue(());
        };

        if let Some(text) = params.text {
            self.driver.update_file(&path, text);
        }
        self.refresh_semantic_tokens();
        ControlFlow::Continue(())
    }

    fn did_change(&mut self, params: DidChangeTextDocumentParams) -> Self::NotifyResult {
        let Ok(path) = params.text_document.uri.to_file_path() else {
            log::error!("no file path from: {:?}", params.text_document.uri);
            return ControlFlow::Continue(());
        };

        if let Some(change) = params.content_changes.first() {
            self.driver.update_file(&path, change.text.clone());
            self.refresh_semantic_tokens();
        }

        ControlFlow::Continue(())
    }

    fn did_change_configuration(
        &mut self,
        _: DidChangeConfigurationParams,
    ) -> ControlFlow<async_lsp::Result<()>> {
        ControlFlow::Continue(())
    }

    fn did_change_watched_files(
        &mut self,
        _params: DidChangeWatchedFilesParams,
    ) -> Self::NotifyResult {
        ControlFlow::Continue(())
    }

    fn did_close(&mut self, _params: DidCloseTextDocumentParams) -> Self::NotifyResult {
        ControlFlow::Continue(())
    }
}

struct TickEvent;

impl ServerState {
    fn new_router(client: ClientSocket) -> Router<Self> {
        let mut router = Router::from_language_server(Self {
            client,
            counter: 0,
            driver: Driver::with_files(vec![]),
        });
        router.event(Self::on_tick);
        router
    }

    fn on_tick(&mut self, _: TickEvent) -> ControlFlow<async_lsp::Result<()>> {
        // log::info!("tick");
        self.counter += 1;
        ControlFlow::Continue(())
    }

    fn fetch(&mut self, url: &Url) -> Option<String> {
        let Ok(path) = url.to_file_path() else {
            log::error!("no file path from: {url:?}");
            return None;
        };

        Some(self.driver.contents(&path))
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

    match server.run_buffered(stdin, stdout).await {
        Ok(()) => {
            eprintln!("All done.");
        }
        Err(e) => eprintln!("server.run_buffered err: {e:?}"),
    }
}
