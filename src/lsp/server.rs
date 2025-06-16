use std::ops::ControlFlow;
use std::path::{Path, PathBuf};
use std::time::Duration;

use async_lsp::LanguageClient;
use async_lsp::client_monitor::ClientProcessMonitorLayer;
use async_lsp::concurrency::ConcurrencyLayer;
use async_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionOptions, CompletionParams, CompletionResponse,
    DiagnosticOptions, DidChangeConfigurationParams, DidChangeTextDocumentParams,
    DidOpenTextDocumentParams, DidSaveTextDocumentParams, DocumentDiagnosticParams,
    DocumentDiagnosticReport, DocumentDiagnosticReportResult, DocumentFormattingParams,
    FullDocumentDiagnosticReport, GotoDefinitionParams, GotoDefinitionResponse, Hover,
    HoverContents, HoverParams, HoverProviderCapability, InitializeParams, InitializeResult,
    Location, MarkedString, OneOf, Position, Range, RelatedFullDocumentDiagnosticReport,
    RelatedUnchangedDocumentDiagnosticReport, SemanticTokenType, SemanticTokens,
    SemanticTokensFullOptions, SemanticTokensLegend, SemanticTokensOptions, SemanticTokensParams,
    SemanticTokensResult, SemanticTokensServerCapabilities, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, TextEdit, UnchangedDocumentDiagnosticReport,
    Url, WorkspaceFoldersServerCapabilities, WorkspaceServerCapabilities,
};
use async_lsp::panic::CatchUnwindLayer;
use async_lsp::router::Router;
use async_lsp::server::LifecycleLayer;
use async_lsp::tracing::TracingLayer;
use async_lsp::{ClientSocket, LanguageServer, ResponseError};
use futures::future::BoxFuture;
use tower::ServiceBuilder;

use crate::compiling::driver::Driver;
use crate::expr::Expr;
use crate::lsp::formatter::format;
use crate::lsp::semantic_tokens;
use crate::name::Name;
use crate::parser::ExprID;
use crate::parser::parse;
use crate::source_file::SourceFile;
use crate::symbol_table::{SymbolID, SymbolKind};
use crate::type_checker::Ty;

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
                    workspace: Some(WorkspaceServerCapabilities {
                        file_operations: None,
                        workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                            change_notifications: Some(OneOf::Left(true)),
                            supported: Some(true),
                        }),
                    }),
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
            log::error!(
                "no file path from: {:?}",
                params.text_document_position_params.text_document.uri
            );
            return Box::pin(async { Ok(None) });
        };

        let position = params.text_document_position_params.position;

        // Get the typed AST for the file
        let typed_units = self.driver.check();

        for unit in typed_units {
            if let Some(source_file) = unit.source_file(&path) {
                // Find the symbol at the cursor position
                if let Some((symbol_id, _)) =
                    self.find_symbol_at_position(&source_file, &path, position)
                {
                    // Look up the symbol definition
                    if let Some(symbol_info) = unit.stage.symbol_table.get(&symbol_id) {
                        if let Some(definition) = &symbol_info.definition {
                            // Convert file ID to path
                            let def_path = unit.input.lookup(definition.file_id);
                            let Some(uri) = Url::from_file_path(def_path).ok() else {
                                return Box::pin(async { Ok(None) });
                            };

                            let location = Location {
                                uri,
                                range: Range::new(
                                    Position::new(definition.line, definition.col),
                                    Position::new(
                                        definition.line,
                                        definition.col + symbol_info.name.len() as u32,
                                    ),
                                ),
                            };

                            return Box::pin(async move {
                                Ok(Some(GotoDefinitionResponse::Scalar(location)))
                            });
                        }
                    }
                }
            }
        }

        Box::pin(async { Ok(None) })
    }

    fn completion(
        &mut self,
        params: CompletionParams,
    ) -> BoxFuture<'static, Result<Option<CompletionResponse>, Self::Error>> {
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
        let typed_units = self.driver.check();

        let mut completion_items = Vec::new();

        for unit in typed_units {
            if let Some(source_file) = unit.source_file(&path) {
                // Check if we're after a dot (member access)
                let is_member_access = self.is_member_access_context(&path, position);
                log::info!("is member access: {is_member_access:?}");

                if is_member_access {
                    // Find the expression before the dot
                    if let Some((_expr_id, receiver_ty)) =
                        self.find_receiver_at_position(source_file, &path, position)
                    {
                        log::info!("receiver at position: {receiver_ty:?}");
                        completion_items.extend(self.get_member_completions(
                            &receiver_ty,
                            &unit.stage.environment,
                            &unit.stage.symbol_table,
                        ));
                    }
                } else {
                    // Global completions - all visible symbols in scope
                    completion_items.extend(self.get_scope_completions(
                        source_file,
                        position,
                        &unit.stage.symbol_table,
                    ));
                    log::info!("global completions: {completion_items:?}");
                }
            }
        }

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

    fn did_change_workspace_folders(
        &mut self,
        _params: <async_lsp::lsp_types::lsp_notification!("workspace/didChangeWorkspaceFolders")as async_lsp::lsp_types::notification::Notification>::Params,
    ) -> Self::NotifyResult {
        eprintln!("did change workspace folders??");
        ControlFlow::Continue(())
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
            log::error!(
                "no file path from: {:?}",
                params.text_document_position_params.text_document.uri
            );
            return Box::pin(async { Ok(None) });
        };

        let position = params.text_document_position_params.position;

        // Get the typed AST for the file
        let typed_units = self.driver.check();

        for unit in typed_units {
            if let Some(source_file) = unit.source_file(&path) {
                // Find the symbol at the cursor position
                if let Some((symbol_id, expr_id)) =
                    self.find_symbol_at_position(source_file, &path, position)
                {
                    // Get type information
                    if let Some(typed_expr) = source_file.typed_expr(&expr_id) {
                        let type_str = self.format_type(&typed_expr.ty);

                        // Get symbol information
                        if let Some(symbol_info) = unit.stage.symbol_table.get(&symbol_id) {
                            let kind_str = match &symbol_info.kind {
                                SymbolKind::Func => "function",
                                SymbolKind::Param => "parameter",
                                SymbolKind::Local => "variable",
                                SymbolKind::Enum => "enum",
                                SymbolKind::Struct => "struct",
                                SymbolKind::TypeParameter => "type parameter",
                                _ => "symbol",
                            };

                            let hover_text = format!(
                                "**{}** `{}`\n\nType: `{}`",
                                kind_str, symbol_info.name, type_str
                            );

                            return Box::pin(async move {
                                Ok(Some(Hover {
                                    contents: HoverContents::Scalar(MarkedString::String(
                                        hover_text,
                                    )),
                                    range: None,
                                }))
                            });
                        }
                    }
                }
            }
        }

        Box::pin(async { Ok(None) })
    }

    fn formatting(
        &mut self,
        params: DocumentFormattingParams,
    ) -> BoxFuture<'static, Result<Option<Vec<TextEdit>>, Self::Error>> {
        let Some(code) = self.fetch(params.text_document.uri) else {
            return Box::pin(async { Ok(None) });
        };

        let source_file = parse(&code, 0);

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

    fn fetch(&mut self, url: Url) -> Option<String> {
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

    // Helper method to find symbol at a given position
    fn find_symbol_at_position(
        &self,
        source_file: &SourceFile<crate::source_file::Typed>,
        path: &PathBuf,
        position: Position,
    ) -> Option<(SymbolID, ExprID)> {
        let byte_offset =
            self.position_to_byte_offset(&self.driver.contents(&PathBuf::from(path)), position)?;

        // Search through all expressions to find one that contains the position
        for (expr_id, typed_expr) in source_file.typed_exprs() {
            let meta = &source_file.meta[*expr_id as usize];
            let range = meta.source_range();

            if range.contains(&byte_offset) {
                // Check if this expression references a symbol
                if let Some(symbol_id) = self.extract_symbol_from_expr(&typed_expr.expr) {
                    return Some((symbol_id, *expr_id));
                }
            }
        }

        None
    }

    // Helper method to extract symbol ID from an expression
    fn extract_symbol_from_expr(&self, expr: &Expr) -> Option<SymbolID> {
        match expr {
            Expr::Variable(Name::Resolved(symbol_id, _), _) => Some(*symbol_id),
            Expr::Func {
                name: Some(Name::Resolved(symbol_id, _)),
                ..
            } => Some(*symbol_id),
            Expr::Parameter(Name::Resolved(symbol_id, _), _) => Some(*symbol_id),
            Expr::Let(Name::Resolved(symbol_id, _), _) => Some(*symbol_id),
            Expr::Struct(Name::Resolved(symbol_id, _), _, _) => Some(*symbol_id),
            Expr::EnumDecl(Name::Resolved(symbol_id, _), _, _) => Some(*symbol_id),
            _ => None,
        }
    }

    // Helper method to convert LSP position to byte offset
    fn position_to_byte_offset(&self, content: &str, position: Position) -> Option<usize> {
        let mut line = 0;
        let mut col = 0;

        for (i, ch) in content.char_indices() {
            if line == position.line && col == position.character {
                return Some(i);
            }

            if ch == '\n' {
                line += 1;
                col = 0;
            } else {
                col += 1;
            }
        }

        None
    }

    // Check if we're in a member access context (after a dot)
    fn is_member_access_context(&self, path: &PathBuf, position: Position) -> bool {
        let content = self.driver.contents(path);
        if let Some(offset) = self.position_to_byte_offset(&content, position) {
            // Check if there's a dot before the cursor
            if offset > 0 {
                let prev_char = content.chars().nth(offset - 1);
                return prev_char == Some('.');
            }
        }
        false
    }

    // Find the receiver expression before a dot
    fn find_receiver_at_position(
        &self,
        source_file: &SourceFile<crate::source_file::Typed>,
        path: &PathBuf,
        position: Position,
    ) -> Option<(ExprID, Ty)> {
        let byte_offset = self.position_to_byte_offset(&self.driver.contents(path), position)?;

        // Look for member access expressions
        for (expr_id, typed_expr) in source_file.typed_exprs() {
            if let Expr::Member(Some(receiver_id), _) = &typed_expr.expr {
                let meta = &source_file.meta[*expr_id as usize];
                let range = meta.source_range();

                // Check if the position is within this member access
                if range.contains(&byte_offset) {
                    // Get the type of the receiver
                    if let Some(receiver_typed) = source_file.typed_expr(receiver_id) {
                        return Some((*receiver_id, receiver_typed.ty.clone()));
                    }
                }
            }
        }

        None
    }

    // Get completions for members of a type
    fn get_member_completions(
        &self,
        ty: &Ty,
        env: &crate::environment::Environment,
        symbol_table: &crate::symbol_table::SymbolTable,
    ) -> Vec<CompletionItem> {
        let mut items = Vec::new();

        match ty {
            Ty::Struct(struct_id, _) => {
                if let Some(crate::environment::TypeDef::Struct(struct_def)) =
                    env.types.get(struct_id)
                {
                    // Add properties
                    for (name, property) in &struct_def.properties {
                        items.push(CompletionItem {
                            label: name.clone(),
                            kind: Some(CompletionItemKind::FIELD),
                            detail: Some(self.format_type(&property.ty)),
                            ..Default::default()
                        });
                    }

                    // Add methods
                    for (name, method) in &struct_def.methods {
                        items.push(CompletionItem {
                            label: name.clone(),
                            kind: Some(CompletionItemKind::METHOD),
                            detail: Some(self.format_type(&method.ty)),
                            ..Default::default()
                        });
                    }
                }
            }
            Ty::Enum(enum_id, _) => {
                if let Some(crate::environment::TypeDef::Enum(enum_def)) = env.types.get(enum_id) {
                    // Add enum variants
                    for variant in &enum_def.variants {
                        let detail = if variant.values.is_empty() {
                            variant.name.clone()
                        } else {
                            format!("{}(...)", variant.name)
                        };

                        items.push(CompletionItem {
                            label: variant.name.clone(),
                            kind: Some(CompletionItemKind::ENUM_MEMBER),
                            detail: Some(detail),
                            ..Default::default()
                        });
                    }
                }
            }
            _ => {}
        }

        items
    }

    // Get completions for all symbols in scope at a position
    fn get_scope_completions(
        &self,
        source_file: &SourceFile<crate::source_file::Typed>,
        position: Position,
        symbol_table: &crate::symbol_table::SymbolTable,
    ) -> Vec<CompletionItem> {
        let mut items = Vec::new();

        // Add all symbols from the symbol table
        for (symbol_id, symbol_info) in symbol_table.all() {
            let kind = match &symbol_info.kind {
                SymbolKind::Func => CompletionItemKind::FUNCTION,
                SymbolKind::Param => CompletionItemKind::VARIABLE,
                SymbolKind::Local => CompletionItemKind::VARIABLE,
                SymbolKind::Enum => CompletionItemKind::ENUM,
                SymbolKind::Struct => CompletionItemKind::STRUCT,
                SymbolKind::TypeParameter => CompletionItemKind::TYPE_PARAMETER,
                SymbolKind::BuiltinType => CompletionItemKind::CLASS,
                SymbolKind::BuiltinFunc => CompletionItemKind::FUNCTION,
                _ => CompletionItemKind::VARIABLE,
            };

            // Get type information if available
            let detail = if let Some(typed_expr) = source_file.typed_expr(&symbol_info.expr_id) {
                Some(self.format_type(&typed_expr.ty))
            } else {
                None
            };

            items.push(CompletionItem {
                label: symbol_info.name.clone(),
                kind: Some(kind),
                detail,
                ..Default::default()
            });
        }

        items
    }

    // Format a type for display
    fn format_type(&self, ty: &Ty) -> String {
        match ty {
            Ty::Void => "Void".to_string(),
            Ty::Int => "Int".to_string(),
            Ty::Bool => "Bool".to_string(),
            Ty::Float => "Float".to_string(),
            Ty::Func(params, ret, _) => {
                let param_strs: Vec<_> = params.iter().map(|p| self.format_type(p)).collect();
                format!("({}) -> {}", param_strs.join(", "), self.format_type(ret))
            }
            Ty::TypeVar(id) => format!("T{}", id.0),
            Ty::Enum(id, generics) => {
                if generics.is_empty() {
                    format!("Enum{}", id.0)
                } else {
                    let generic_strs: Vec<_> =
                        generics.iter().map(|g| self.format_type(g)).collect();
                    format!("Enum{}<{}>", id.0, generic_strs.join(", "))
                }
            }
            Ty::Struct(id, generics) => {
                if generics.is_empty() {
                    format!("Struct{}", id.0)
                } else {
                    let generic_strs: Vec<_> =
                        generics.iter().map(|g| self.format_type(g)).collect();
                    format!("Struct{}<{}>", id.0, generic_strs.join(", "))
                }
            }
            Ty::Array(elem) => format!("Array<{}>", self.format_type(elem)),
            Ty::Tuple(types) => {
                let type_strs: Vec<_> = types.iter().map(|t| self.format_type(t)).collect();
                format!("({})", type_strs.join(", "))
            }
            _ => "Unknown".to_string(),
        }
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
        Err(e) => eprintln!("server.run_buffered err: {e:?}"),
    }
}

#[allow(unused)]
fn find_files_by_extension(dir: &Path, extension: &str) -> std::io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    find_files_recursive(dir, extension, &mut files)?;
    Ok(files)
}

fn find_files_recursive(
    dir: &Path,
    extension: &str,
    files: &mut Vec<PathBuf>,
) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();

        if path.is_dir() {
            find_files_recursive(&path, extension, files)?;
        } else if path.is_file()
            && let Some(ext) = path.extension()
            && ext.to_str() == Some(extension)
        {
            files.push(path);
        }
    }
    Ok(())
}
