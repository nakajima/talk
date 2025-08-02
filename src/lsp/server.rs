use std::ops::ControlFlow;
use std::path::PathBuf;
use std::time::Duration;

use async_lsp::LanguageClient;
use async_lsp::client_monitor::ClientProcessMonitorLayer;
use async_lsp::concurrency::ConcurrencyLayer;
use async_lsp::lsp_types::{
    CompletionOptions, CompletionParams, CompletionResponse, CompletionTriggerKind, Diagnostic,
    DiagnosticOptions, DiagnosticSeverity, DidChangeConfigurationParams,
    DidChangeTextDocumentParams, DidChangeWatchedFilesParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, DidSaveTextDocumentParams, DocumentDiagnosticParams,
    DocumentDiagnosticReport, DocumentDiagnosticReportResult, DocumentFormattingParams,
    DocumentHighlight, DocumentHighlightKind, DocumentHighlightParams, DocumentSymbol,
    DocumentSymbolParams, DocumentSymbolResponse, FullDocumentDiagnosticReport,
    GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverContents, HoverParams,
    HoverProviderCapability, InitializeParams, InitializeResult, Location, MarkupContent,
    MarkupKind, OneOf, Position, PublishDiagnosticsParams, Range, ReferenceParams,
    RelatedFullDocumentDiagnosticReport, RelatedUnchangedDocumentDiagnosticReport, RenameOptions,
    RenameParams, SemanticTokens, SemanticTokensFullOptions, SemanticTokensLegend,
    SemanticTokensOptions, SemanticTokensParams, SemanticTokensResult,
    SemanticTokensServerCapabilities, ServerCapabilities, SymbolKind as LspSymbolKind,
    TextDocumentSyncCapability, TextDocumentSyncKind, TextEdit, UnchangedDocumentDiagnosticReport,
    Url, WorkspaceEdit,
};
use async_lsp::panic::CatchUnwindLayer;
use async_lsp::router::Router;
use async_lsp::server::LifecycleLayer;
use async_lsp::tracing::TracingLayer;
use async_lsp::{ClientSocket, LanguageServer, ResponseError};
use futures::future::BoxFuture;
use tower::ServiceBuilder;

use crate::compiling::compilation_unit::{CompilationUnit, StageTrait};
use crate::compiling::driver::{Driver, DriverConfig};
use crate::environment::Environment;
use crate::lexer::Lexer;
use crate::lsp::completion::CompletionContext;
use crate::lsp::semantic_tokens::{self, TOKEN_TYPES};
use crate::parser::Parser;
use crate::semantic_index::QueryDatabase;

#[allow(dead_code)]
struct ServerState {
    client: ClientSocket,
    counter: i32,
    driver: Driver,
    pending_diagnostics: Vec<PathBuf>,
    last_change_tick: i32,
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
                    references_provider: Some(OneOf::Left(true)),
                    document_highlight_provider: Some(OneOf::Left(true)),
                    document_formatting_provider: Some(OneOf::Left(true)),
                    document_symbol_provider: Some(OneOf::Left(true)),
                    rename_provider: Some(OneOf::Right(RenameOptions {
                        prepare_provider: Some(false),
                        work_done_progress_options: Default::default(),
                    })),
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
        let Ok(path) = params
            .text_document_position_params
            .text_document
            .uri
            .to_file_path()
        else {
            tracing::error!(
                "no file path from: {:?}",
                params.text_document_position_params.text_document.uri
            );
            return Box::pin(async { Ok(None) });
        };

        let position = params.text_document_position_params.position;

        // Use the driver's method to find the symbol at the position
        let Some(symbol_id) = self.driver.symbol_at_position(
            crate::diagnostic::Position {
                line: position.line,
                col: position.character,
            },
            &path,
        ) else {
            return Box::pin(async { Ok(None) });
        };

        let Some(info) = self.driver.symbol_table.get(&symbol_id) else {
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

    fn document_highlight(
        &mut self,
        params: DocumentHighlightParams,
    ) -> BoxFuture<'static, Result<Option<Vec<DocumentHighlight>>, Self::Error>> {
        let Ok(path) = params
            .text_document_position_params
            .text_document
            .uri
            .to_file_path()
        else {
            return Box::pin(async { Ok(None) });
        };

        let position = params.text_document_position_params.position;

        // Find the symbol at the current position
        let Some(symbol_id) = self.driver.symbol_at_position(
            crate::diagnostic::Position {
                line: position.line,
                col: position.character,
            },
            &path,
        ) else {
            return Box::pin(async { Ok(None) });
        };

        // Find all occurrences of this symbol in the current file
        let mut highlights = Vec::new();
        for (span, sym_id) in &self.driver.symbol_table.symbol_map {
            if *sym_id == symbol_id && span.path == path {
                highlights.push(DocumentHighlight {
                    range: Range::new(
                        Position::new(span.start_line, span.start_col),
                        Position::new(span.end_line, span.end_col),
                    ),
                    kind: Some(DocumentHighlightKind::TEXT),
                });
            }
        }

        Box::pin(async move {
            if highlights.is_empty() {
                Ok(None)
            } else {
                Ok(Some(highlights))
            }
        })
    }

    fn completion(
        &mut self,
        params: CompletionParams,
    ) -> BoxFuture<'static, Result<Option<CompletionResponse>, Self::Error>> {
        tracing::info!("completions requested: {params:?}");

        let Ok(path) = params
            .text_document_position
            .text_document
            .uri
            .to_file_path()
        else {
            tracing::error!(
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
        tracing::info!("completion_items: {completion_items:?}");
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
            tracing::error!("no file path from: {:?}", params.text_document.uri);
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

        tracing::info!("Getting diagnostics for {path:?}");
        let diagnostics = self.refresh_diagnostics_for(&path);
        tracing::info!(
            "Got {:#?} diagnostics",
            self.driver
                .session
                .lock()
                .ok()
                .map(|d| d.diagnostics.clone())
        );

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
            tracing::error!("no file path from: {:?}", params.text_document.uri);
            return Box::pin(async { Ok(None) });
        };

        let response = Ok(Some(SemanticTokensResult::Tokens(
            SemanticTokens {
                result_id: None,
                data: semantic_tokens::collect(self.driver.contents(&path)),
            }
            .clone(),
        )));

        Box::pin(async { response })
    }

    fn hover(
        &mut self,
        params: HoverParams,
    ) -> BoxFuture<'static, Result<Option<Hover>, Self::Error>> {
        let Ok(path) = params
            .text_document_position_params
            .text_document
            .uri
            .to_file_path()
        else {
            tracing::error!(
                "no file path from: {:?}",
                params.text_document_position_params.text_document.uri
            );
            return Box::pin(async { Ok(None) });
        };

        let position = params.text_document_position_params.position;

        // Find the symbol at the hover position
        let Some(symbol_id) = self.driver.symbol_at_position(
            crate::diagnostic::Position {
                line: position.line,
                col: position.character,
            },
            &path,
        ) else {
            return Box::pin(async { Ok(None) });
        };

        // Get symbol information
        let Some(info) = self.driver.symbol_table.get(&symbol_id) else {
            return Box::pin(async { Ok(None) });
        };

        // Get type information from the environment
        let mut type_info = None;
        for unit in &self.driver.units {
            if unit.has_file(&path) {
                // Try to get type from semantic index first
                if let Some(expr_id) = unit.env.semantic_index.find_expr_at_position(
                    &crate::diagnostic::Position {
                        line: position.line,
                        col: position.character,
                    },
                    &path,
                ) {
                    type_info = unit.env.semantic_index.expr_type(expr_id);
                }

                // Fallback to symbol table lookup
                if type_info.is_none()
                    && let Ok(scheme) = unit.env.lookup_symbol(&symbol_id)
                {
                    type_info = Some(scheme.ty().clone());
                }
                break;
            }
        }

        // Format the hover content
        let mut contents = vec![];

        // Add type signature
        if let Some(ty) = type_info {
            contents.push(format!("```talk\n{}: {}\n```", info.name, ty));
        } else {
            contents.push(format!("```talk\n{}\n```", info.name));
        }

        // Add documentation if available
        if let Some(doc) = &info.documentation {
            contents.push(format!("---\n\n{doc}"));
        }

        // Add symbol kind information
        contents.push(format!("_{:?}_", info.kind));

        // Add definition location if available
        if let Some(def) = &info.definition {
            contents.push(format!("\nDefined at `{}`", def.path.display()));
        }

        let hover_text = contents.join("\n\n");

        Box::pin(async move {
            Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: hover_text,
                }),
                range: None,
            }))
        })
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

        let mut env = Environment::new();
        let lexer = Lexer::new(&code);
        let mut parser = Parser::new(self.driver.session.clone(), lexer, path, &mut env);
        parser.parse();
        let source_file = parser.parse_tree;
        let formatted = crate::parsing::formatter::format(&source_file, 80);

        Box::pin(async move {
            let last_line = code.lines().count() as u32;
            let last_char = code.lines().last().map(|line| line.len().saturating_sub(1));

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
        self.driver.check();
        self.refresh_semantic_tokens();

        // Publish diagnostics for the opened file
        let diagnostics = self.refresh_diagnostics_for(&path);
        if let Ok(uri) = Url::from_file_path(&path) {
            let mut client = self.client.clone();
            tokio::spawn(async move {
                client
                    .publish_diagnostics(PublishDiagnosticsParams {
                        uri,
                        diagnostics,
                        version: None,
                    })
                    .ok();
            });
        }

        ControlFlow::Continue(())
    }

    fn did_save(&mut self, params: DidSaveTextDocumentParams) -> Self::NotifyResult {
        let Ok(path) = params.text_document.uri.to_file_path() else {
            tracing::error!("no file path from: {:?}", params.text_document.uri);
            return ControlFlow::Continue(());
        };

        if let Some(text) = params.text {
            self.driver.update_file(&path, text);
        }

        self.driver.check();
        self.refresh_semantic_tokens();

        // Publish diagnostics for all files since save might affect multiple files
        let files_with_diagnostics = {
            if let Ok(session) = self.driver.session.lock() {
                let mut files_with_diagnostics = std::collections::HashSet::new();
                files_with_diagnostics.insert(path.clone());

                for diagnostic in &session.diagnostics {
                    files_with_diagnostics.insert(diagnostic.path.clone());
                }

                files_with_diagnostics
            } else {
                std::collections::HashSet::new()
            }
        };

        for file_path in files_with_diagnostics {
            let diagnostics = self.refresh_diagnostics_for(&file_path);
            if let Ok(uri) = Url::from_file_path(&file_path) {
                let mut client = self.client.clone();
                tokio::spawn(async move {
                    client
                        .publish_diagnostics(PublishDiagnosticsParams {
                            uri,
                            diagnostics,
                            version: None,
                        })
                        .ok();
                });
            }
        }

        ControlFlow::Continue(())
    }

    fn did_change(&mut self, params: DidChangeTextDocumentParams) -> Self::NotifyResult {
        let Ok(path) = params.text_document.uri.to_file_path() else {
            tracing::error!("no file path from: {:?}", params.text_document.uri);
            return ControlFlow::Continue(());
        };

        if let Some(change) = params.content_changes.first() {
            self.driver.update_file(&path, change.text.clone());
            self.refresh_semantic_tokens();

            // Mark this file as needing diagnostics refresh
            if !self.pending_diagnostics.contains(&path) {
                self.pending_diagnostics.push(path);
            }
            self.last_change_tick = self.counter;
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

    fn document_symbol(
        &mut self,
        params: DocumentSymbolParams,
    ) -> BoxFuture<'static, Result<Option<DocumentSymbolResponse>, Self::Error>> {
        let Ok(path) = params.text_document.uri.to_file_path() else {
            return Box::pin(async { Ok(None) });
        };

        // Check if we have this file
        if !self.driver.has_file(&path) {
            return Box::pin(async { Ok(None) });
        }

        let mut symbols = Vec::new();

        // Collect all symbols from the file
        for (span, symbol_id) in &self.driver.symbol_table.symbol_map {
            if span.path != path {
                continue;
            }

            let Some(info) = self.driver.symbol_table.get(symbol_id) else {
                continue;
            };

            // Convert our symbol kind to LSP symbol kind
            let kind = match info.kind {
                crate::SymbolKind::FuncDef => LspSymbolKind::FUNCTION,
                crate::SymbolKind::Local => LspSymbolKind::VARIABLE,
                crate::SymbolKind::Param => LspSymbolKind::VARIABLE,
                crate::SymbolKind::Struct => LspSymbolKind::STRUCT,
                crate::SymbolKind::Enum => LspSymbolKind::ENUM,
                crate::SymbolKind::EnumVariant(_) => LspSymbolKind::ENUM_MEMBER,
                crate::SymbolKind::Protocol => LspSymbolKind::INTERFACE,
                crate::SymbolKind::Property => LspSymbolKind::PROPERTY,
                crate::SymbolKind::TypeParameter => LspSymbolKind::TYPE_PARAMETER,
                crate::SymbolKind::BuiltinType => LspSymbolKind::CLASS,
                crate::SymbolKind::BuiltinFunc => LspSymbolKind::FUNCTION,
                _ => LspSymbolKind::VARIABLE,
            };

            let range = Range::new(
                Position::new(span.start_line, span.start_col),
                Position::new(span.end_line, span.end_col),
            );

            #[allow(deprecated)]
            symbols.push(DocumentSymbol {
                name: info.name.clone(),
                detail: None,
                kind,
                tags: None,
                deprecated: None,
                range,
                selection_range: range,
                children: None,
            });
        }

        // Sort symbols by position
        symbols.sort_by(|a, b| {
            a.range
                .start
                .line
                .cmp(&b.range.start.line)
                .then(a.range.start.character.cmp(&b.range.start.character))
        });

        Box::pin(async move { Ok(Some(DocumentSymbolResponse::Nested(symbols))) })
    }

    fn rename(
        &mut self,
        params: RenameParams,
    ) -> BoxFuture<'static, Result<Option<WorkspaceEdit>, Self::Error>> {
        let Ok(path) = params
            .text_document_position
            .text_document
            .uri
            .to_file_path()
        else {
            return Box::pin(async { Ok(None) });
        };

        let position = params.text_document_position.position;
        let new_name = params.new_name;

        // Find the symbol at the rename position
        let Some(symbol_id) = self.driver.symbol_at_position(
            crate::diagnostic::Position {
                line: position.line,
                col: position.character,
            },
            &path,
        ) else {
            return Box::pin(async { Ok(None) });
        };

        // Collect all occurrences of this symbol across all files
        let mut edits_by_file: std::collections::HashMap<Url, Vec<TextEdit>> =
            std::collections::HashMap::new();

        for (span, sym_id) in &self.driver.symbol_table.symbol_map {
            if sym_id == &symbol_id {
                let range = Range::new(
                    Position::new(span.start_line, span.start_col),
                    Position::new(span.end_line, span.end_col),
                );

                let text_edit = TextEdit {
                    range,
                    new_text: new_name.clone(),
                };

                if let Ok(uri) = Url::from_file_path(&span.path) {
                    edits_by_file.entry(uri).or_default().push(text_edit);
                }
            }
        }

        // Convert to workspace edit
        let mut changes = std::collections::HashMap::new();
        for (uri, edits) in edits_by_file {
            changes.insert(uri, edits);
        }

        Box::pin(async move {
            Ok(Some(WorkspaceEdit {
                changes: Some(changes),
                document_changes: None,
                change_annotations: None,
            }))
        })
    }

    fn references(
        &mut self,
        params: ReferenceParams,
    ) -> BoxFuture<'static, Result<Option<Vec<Location>>, Self::Error>> {
        let Ok(path) = params
            .text_document_position
            .text_document
            .uri
            .to_file_path()
        else {
            return Box::pin(async { Ok(None) });
        };

        let position = params.text_document_position.position;

        // Find the symbol at the reference position
        let Some(symbol_id) = self.driver.symbol_at_position(
            crate::diagnostic::Position {
                line: position.line,
                col: position.character,
            },
            &path,
        ) else {
            return Box::pin(async { Ok(None) });
        };

        // Collect all references to this symbol
        let mut locations = Vec::new();

        for (span, sym_id) in &self.driver.symbol_table.symbol_map {
            if sym_id == &symbol_id
                && let Ok(uri) = Url::from_file_path(&span.path)
            {
                let location = Location::new(
                    uri,
                    Range::new(
                        Position::new(span.start_line, span.start_col),
                        Position::new(span.end_line, span.end_col),
                    ),
                );
                locations.push(location);
            }
        }

        // Include the definition if requested
        if params.context.include_declaration
            && let Some(info) = self.driver.symbol_table.get(&symbol_id)
            && let Some(def) = &info.definition
            && let Ok(uri) = Url::from_file_path(&def.path)
        {
            let location = Location::new(
                uri,
                Range::new(
                    Position::new(def.line, def.col),
                    Position::new(def.line, def.col),
                ),
            );
            // Only add if not already in the list
            if !locations
                .iter()
                .any(|l| l.uri == location.uri && l.range == location.range)
            {
                locations.push(location);
            }
        }

        Box::pin(async move {
            if locations.is_empty() {
                Ok(None)
            } else {
                Ok(Some(locations))
            }
        })
    }
}

struct TickEvent;

impl ServerState {
    fn new_router(client: ClientSocket) -> Router<Self> {
        let mut router = Router::from_language_server(Self {
            client,
            counter: 0,
            driver: Driver::new(
                "TalkLSP",
                DriverConfig {
                    executable: false,
                    include_prelude: true,
                    include_comments: true,
                },
            ),
            pending_diagnostics: Vec::new(),
            last_change_tick: 0,
        });
        router.event(Self::on_tick);
        router
    }

    fn on_tick(&mut self, _: TickEvent) -> ControlFlow<async_lsp::Result<()>> {
        self.counter += 1;

        // Check if we have pending diagnostics and enough time has passed
        if !self.pending_diagnostics.is_empty() && self.counter > self.last_change_tick {
            // Run diagnostics for all pending files
            self.driver.check();

            // Get all files with diagnostics to publish updates for all affected files
            let mut files_to_publish = std::collections::HashSet::new();

            // Add pending files
            for path in &self.pending_diagnostics {
                files_to_publish.insert(path.clone());
            }

            // Add all files that have diagnostics (to clear stale ones)
            if let Ok(session) = self.driver.session.lock() {
                for diagnostic in &session.diagnostics {
                    files_to_publish.insert(diagnostic.path.clone());
                }
            }

            // Publish diagnostics for each file
            for path in files_to_publish {
                let diagnostics = self.refresh_diagnostics_for(&path);
                if let Ok(uri) = Url::from_file_path(&path) {
                    let mut client = self.client.clone();
                    tokio::spawn(async move {
                        client
                            .publish_diagnostics(PublishDiagnosticsParams {
                                uri,
                                diagnostics,
                                version: None,
                            })
                            .ok();
                    });
                }
            }

            // Clear the pending list
            self.pending_diagnostics.clear();
        }

        ControlFlow::Continue(())
    }

    fn fetch(&mut self, url: &Url) -> Option<String> {
        let Ok(path) = url.to_file_path() else {
            tracing::error!("no file path from: {url:?}");
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

    pub fn refresh_diagnostics_for(&mut self, path: &PathBuf) -> Vec<Diagnostic> {
        let mut result = vec![];
        let mut round = 0;

        if let Ok(session) = &mut self.driver.session.lock() {
            session.clear_diagnostics()
        } else {
            tracing::error!("Unable to clear diagnostics")
        }

        while result.is_empty() && round < 3 {
            let diagnostics = match round {
                0 => {
                    let parsed = self.driver.parse();
                    round += 1;
                    self.encode_diagnostics_from(path, parsed)
                        .unwrap_or_default()
                }
                _ => {
                    let lowered = self.driver.check();
                    round += 1;
                    self.encode_diagnostics_from(path, lowered)
                        .unwrap_or_default()
                }
            };

            result.extend(diagnostics);
        }

        result
    }

    fn encode_diagnostics_from<S: StageTrait>(
        &self,
        path: &PathBuf,
        units: Vec<CompilationUnit<S>>,
    ) -> Option<Vec<Diagnostic>> {
        let mut result = vec![];
        for unit in units {
            tracing::info!("checking for diagnostics in {path:?}");
            if unit.has_file(path)
                && let Some(_source_file) = unit.source_file(path)
            {
                let Ok(session) = self.driver.session.lock() else {
                    return None;
                };
                let diagnostics = session.diagnostics_for(path);
                for diag in diagnostics {
                    if &diag.path != path {
                        // This is definitely the wrong place to be doing this filtering...
                        continue;
                    }

                    let source = self.driver.contents(path);
                    let start = self
                        .line_col_for(diag.span.0 as u32, &source)
                        .unwrap_or_default();
                    let end = self
                        .line_col_for(diag.span.1 as u32, &source)
                        .unwrap_or_default();
                    let range = Range::new(start, end);
                    result.push(Diagnostic::new(
                        range,
                        Some(DiagnosticSeverity::ERROR),
                        None,
                        None,
                        diag.message(),
                        None,
                        None,
                    ));
                }
            }
        }

        Some(result)
    }

    fn line_col_for(&self, position: u32, source: &str) -> Option<Position> {
        if position as usize > source.len() {
            return None;
        }

        let before = &source[..position as usize];
        let line = before.matches('\n').count(); // Remove the +1 here
        let column = before
            .rfind('\n')
            .map(|i| &before[i + 1..])
            .unwrap_or(before)
            .chars()
            .count(); // Also remove the +1 here

        Some(Position::new(line as u32, column as u32))
    }
}

pub async fn start() {
    tracing::info!("Starting LSP…");

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

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_position_conversion() {
        // Test line/column calculation
        let server = ServerState {
            client: unsafe { std::mem::zeroed() }, // We won't use this
            counter: 0,
            driver: Driver::new(
                "TestLSP",
                DriverConfig {
                    executable: false,
                    include_prelude: true,
                    include_comments: true,
                },
            ),
            pending_diagnostics: Vec::new(),
            last_change_tick: 0,
        };

        let source = "line1\nline2\nline3";

        // Test beginning of file
        let pos = server.line_col_for(0, source);
        assert_eq!(pos, Some(Position::new(0, 0)));

        // Test first character of second line
        let pos = server.line_col_for(6, source);
        assert_eq!(pos, Some(Position::new(1, 0)));

        // Test middle of second line
        let pos = server.line_col_for(8, source);
        assert_eq!(pos, Some(Position::new(1, 2)));
    }

    #[test]
    fn test_document_highlight_range_creation() {
        // Test that document highlights create correct ranges
        use crate::lexing::span::Span;

        let span = Span {
            start: 0,
            end: 5,
            start_line: 0,
            start_col: 0,
            end_line: 0,
            end_col: 5,
            path: PathBuf::from("/test/file.tlk"),
        };

        // Verify range creation from span
        let range = Range::new(
            Position::new(span.start_line, span.start_col),
            Position::new(span.end_line, span.end_col),
        );

        assert_eq!(range.start.line, 0);
        assert_eq!(range.start.character, 0);
        assert_eq!(range.end.line, 0);
        assert_eq!(range.end.character, 5);
    }

    #[test]
    fn test_diagnostic_severity() {
        // Verify diagnostic severity is set correctly
        use async_lsp::lsp_types::{Diagnostic, DiagnosticSeverity};

        let diagnostic = Diagnostic::new(
            Range::new(Position::new(0, 0), Position::new(0, 5)),
            Some(DiagnosticSeverity::ERROR),
            None,
            None,
            "Test error".to_string(),
            None,
            None,
        );

        assert_eq!(diagnostic.severity, Some(DiagnosticSeverity::ERROR));
        assert_eq!(diagnostic.message, "Test error");
    }

    #[test]
    fn test_prelude_symbols_have_definitions() {
        // Test that prelude symbols have proper file paths
        let driver = Driver::new(
            "TestLSP",
            DriverConfig {
                executable: false,
                include_prelude: true,
                include_comments: true,
            },
        );

        // Look for Array type in symbol table
        let all_symbols = driver.symbol_table.all();
        let array_symbol = all_symbols
            .iter()
            .find(|(_, info)| info.name == "Array")
            .map(|(id, _)| *id);

        assert!(
            array_symbol.is_some(),
            "Array symbol should exist in prelude"
        );

        if let Some(symbol_id) = array_symbol {
            let info = driver.symbol_table.get(&symbol_id).unwrap();
            assert!(
                info.definition.is_some(),
                "Array symbol should have a definition"
            );

            let definition = info.definition.as_ref().unwrap();
            assert!(
                definition.path.is_absolute(),
                "Prelude symbols should have absolute paths"
            );
            assert!(
                definition.path.to_string_lossy().contains("core/Array.tlk"),
                "Array definition should point to core/Array.tlk"
            );
        }
    }

    #[test]
    fn test_array_member_definition_lookup() {
        // Test that we can find definitions for array member accesses
        let mut driver = Driver::new(
            "TestLSP",
            DriverConfig {
                executable: false,
                include_prelude: true,
                include_comments: false,
            },
        );

        // Add the test file
        let path = PathBuf::from("/test/array_test.tlk");
        let contents = r#"let a = [1,2,3]
print(a.count)"#;
        driver.update_file(&path, contents);

        // Run type checking to populate semantic index
        driver.check();

        // Try to find symbol at position of 'count' (line 1, col 8)
        let symbol =
            driver.symbol_at_position(crate::diagnostic::Position { line: 1, col: 8 }, &path);

        assert!(symbol.is_some(), "Should find symbol for 'count' property");

        if let Some(symbol_id) = symbol {
            let info = driver.symbol_table.get(&symbol_id);
            assert!(info.is_some(), "Symbol should exist in symbol table");

            if let Some(info) = info {
                assert_eq!(info.name, "count", "Symbol should be named 'count'");
                assert!(info.definition.is_some(), "Symbol should have a definition");

                if let Some(def) = &info.definition {
                    assert!(
                        def.path.to_string_lossy().contains("Array.tlk"),
                        "Definition should point to Array.tlk file"
                    );
                }
            }
        }
    }
}
