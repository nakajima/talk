use std::str::FromStr;

use crate::ast::{AST, NewAST, Parsed};
use crate::diagnostic::{AnyDiagnostic, Diagnostic, Severity};
use crate::label::Label;
use crate::lexer::Lexer;
use crate::name::Name;
use crate::node::Node;
use crate::node_id::{FileID, NodeID};
use crate::node_kinds::block::Block;
use crate::node_kinds::body::Body;
use crate::node_kinds::call_arg::CallArg;
use crate::node_kinds::decl::{
    Decl, DeclKind, Import, ImportPath, ImportedSymbol, ImportedSymbols, Visibility,
};
use crate::node_kinds::expr::{Expr, ExprKind};
use crate::node_kinds::func::{EffectSet, Func};
use crate::node_kinds::func_signature::FuncSignature;
use crate::node_kinds::generic_decl::GenericDecl;
use crate::node_kinds::incomplete_expr::IncompleteExpr;
use crate::node_kinds::inline_ir_instruction::{
    InlineIRInstruction, InlineIRInstructionKind, Register, Value,
};
use crate::node_kinds::match_arm::MatchArm;
use crate::node_kinds::parameter::Parameter;
use crate::node_kinds::pattern::{
    Pattern, PatternKind, RecordFieldPattern, RecordFieldPatternKind,
};
use crate::node_kinds::record_field::{RecordField, RecordFieldTypeAnnotation};
use crate::node_kinds::stmt::{Stmt, StmtKind};
use crate::node_kinds::type_annotation::{TypeAnnotation, TypeAnnotationKind};
use crate::node_meta::NodeMeta;
use crate::parser_error::ParserError;
use crate::precedence::Precedence;
use crate::span::Span;
use crate::token::Token;
use crate::token_kind::TokenKind;
use anyhow::Result;
use tracing::instrument;

// for making sure we've pushed to the location stack
// it's not copyable so we always need to have one before calling add_expr
pub struct LocToken;

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
enum FuncOrFuncSignature {
    Func(Func),
    FuncSignature(FuncSignature),
}

#[derive(PartialEq, Clone, Copy, Debug, Eq, PartialOrd, Ord, Hash)]
pub enum BlockContext {
    Struct,
    Protocol,
    Enum,
    Func,
    If,
    Loop,
    MatchArmBody,
    Extend,
    None,
}

/// Tracks parsing context to determine if trailing blocks are allowed
#[derive(PartialEq, Clone, Copy, Debug)]
pub enum ParseContext {
    TopLevel,
    Match, // inside match scrutinee
    If,    // inside if condition
    Loop,  // inside loop condition
    For,   // inside for iterable
}

impl ParseContext {
    /// Returns true if trailing blocks should be parsed in this context
    fn allows_trailing_blocks(&self) -> bool {
        matches!(self, ParseContext::TopLevel)
    }
}

impl BlockContext {
    pub fn allows_conformances(&self) -> bool {
        matches!(self, BlockContext::Extend | BlockContext::Protocol)
    }
}

// for tracking begin/end tokens
pub struct SourceLocationStart {
    token: Token,
    identifiers: Vec<Token>,
}
pub type SourceLocationStack = Vec<SourceLocationStart>;

pub struct Parser<'a> {
    source: &'a str,
    lexer: Lexer<'a>,
    source_location_stack: SourceLocationStack,
    next: Option<Token>,
    current: Option<Token>,
    previous: Option<Token>,
    previous_before_newline: Option<Token>,
    ast: AST,
    file_id: FileID,
    diagnostics: Vec<AnyDiagnostic>,
    context_stack: Vec<ParseContext>,
}

#[allow(clippy::expect_used)]
impl<'a> Parser<'a> {
    pub fn new(path: impl Into<String>, file_id: FileID, lexer: Lexer<'a>) -> Self {
        let source = lexer.code;
        Self {
            source,
            lexer,
            next: None,
            current: None,
            previous: None,
            previous_before_newline: None,
            source_location_stack: Default::default(),
            file_id,
            diagnostics: Default::default(),
            context_stack: vec![ParseContext::TopLevel],
            ast: AST::<NewAST> {
                path: path.into(),
                roots: Default::default(),
                meta: Default::default(),
                phase: (),
                node_ids: Default::default(),
                synthsized_ids: Default::default(),
                file_id,
                skip_core_prelude: false,
            },
        }
    }

    /// Extract lexeme from a token
    fn lexeme(&self, token: &Token) -> &'a str {
        token.lexeme(self.source)
    }

    pub fn parse(self) -> Result<(AST<Parsed>, Vec<AnyDiagnostic>), ParserError> {
        let (ast, diagnostics, _comments) = self.parse_with_comments()?;
        Ok((ast, diagnostics))
    }

    #[allow(clippy::type_complexity)]
    pub fn parse_with_comments(
        mut self,
    ) -> Result<(AST<Parsed>, Vec<AnyDiagnostic>, Vec<Token>), ParserError> {
        self.advance();
        self.advance();
        self.skip_semicolons_and_newlines();

        let mut last_start = u32::MAX;

        while let Some(current) = self.current.clone() {
            self.skip_semicolons_and_newlines();

            if current.start == last_start {
                return Err(ParserError::InfiniteLoop(Some(current)));
            }

            last_start = current.start;

            if current.kind == TokenKind::EOF {
                break;
            }

            let root = self.next_root(&current.kind)?;
            self.ast.roots.push(root);

            self.skip_semicolons_and_newlines();
        }

        let ast = AST::<Parsed> {
            path: self.ast.path,
            roots: self.ast.roots,
            meta: self.ast.meta,
            phase: Parsed,
            node_ids: self.ast.node_ids,
            file_id: self.file_id,
            synthsized_ids: self.ast.synthsized_ids,
            skip_core_prelude: self.ast.skip_core_prelude,
        };

        Ok((ast, self.diagnostics, self.lexer.comments))
    }

    fn record_diagnostic(&mut self, kind: ParserError) {
        self.diagnostics.push(
            Diagnostic {
                id: NodeID(self.file_id, 0),
                severity: Severity::Error,
                kind,
            }
            .into(),
        );
    }

    fn next_root(&mut self, kind: &TokenKind) -> Result<Node, ParserError> {
        use TokenKind::*;
        if matches!(
            kind,
            Protocol
                | Struct
                | Enum
                | Let
                | Func
                | Case
                | Extend
                | Typealias
                | Effect
                | Import
                | Public
        ) {
            self.decl(BlockContext::None, false)
        } else {
            Ok(Node::Stmt(self.stmt()?))
        }
    }

    // MARK: Decls

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn decl(&mut self, context: BlockContext, is_static: bool) -> Result<Node, ParserError> {
        self.skip_semicolons_and_newlines();

        let Some(current) = self.current.clone() else {
            unreachable!()
        };

        // Make sure to update next_root if adding a case here.
        use TokenKind::*;
        let node: Node = match &current.kind {
            Public => {
                self.consume(TokenKind::Public)?;
                let mut node = self.decl(context, is_static)?;
                // Set visibility to Public on the declaration
                if let Node::Decl(ref mut decl) = node {
                    decl.visibility = Visibility::Public;
                }
                node
            }
            Static => {
                self.consume(TokenKind::Static)?;
                self.decl(context, true)?
            }
            Import => self.import_decl()?.into(),
            Effect => self.effect()?.into(),
            Typealias => self.typealias()?.into(),
            Protocol => self
                .nominal_decl(TokenKind::Protocol, BlockContext::Protocol)?
                .into(),
            Enum => self
                .nominal_decl(TokenKind::Enum, BlockContext::Enum)?
                .into(),
            Extend => self
                .nominal_decl(TokenKind::Extend, BlockContext::Extend)?
                .into(),
            Struct => self
                .nominal_decl(TokenKind::Struct, BlockContext::Struct)?
                .into(),
            Init => match context {
                BlockContext::Extend | BlockContext::Struct => self.init_decl()?.into(),
                _ => return Err(ParserError::InitNotAllowed(context)),
            },

            Case => self.variant_decl(true)?.into(),
            Let => match context {
                BlockContext::Extend | BlockContext::Struct => {
                    self.property_decl(is_static)?.into()
                }
                BlockContext::None => self.let_decl()?.into(),
                BlockContext::Enum => return Err(ParserError::LetNotAllowed(context)),
                _ => self.let_decl()?.into(),
            },
            Func => match context {
                BlockContext::Extend
                | BlockContext::Struct
                | BlockContext::Enum
                | BlockContext::Protocol => self.method_decl(context, is_static)?.into(),
                _ => self.func_decl(context, true)?.into(),
            },
            _ => self.stmt()?.into(),
        };

        Ok(node)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn effect(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Effect)?;

        let (effect_name, name_span) = self.effect_name()?;
        let generics = self.generics()?;

        self.consume(TokenKind::LeftParen)?;
        let params = self.parameters()?;
        self.consume(TokenKind::RightParen)?;

        self.consume(TokenKind::Arrow)?;
        let ret = self.type_annotation()?;

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::Effect {
                name: effect_name.clone().into(),
                name_span,
                generics,
                params,
                ret,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn import_decl(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Import)?;

        // Parse imported symbols: either { a, b } or _
        let symbols = if self.did_match(TokenKind::Underscore)? {
            ImportedSymbols::All
        } else {
            self.consume(TokenKind::LeftBrace)?;
            let mut imported = vec![];

            loop {
                if matches!(
                    self.current.as_ref().map(|t| &t.kind),
                    Some(TokenKind::RightBrace)
                ) {
                    break;
                }

                let (name, name_span) = self.identifier()?;

                // Check for alias: { Point: Pt }
                let alias = if self.did_match(TokenKind::Colon)? {
                    let (alias_name, _) = self.identifier()?;
                    Some(alias_name)
                } else {
                    None
                };

                imported.push(ImportedSymbol {
                    name,
                    alias,
                    span: name_span,
                });

                if !self.did_match(TokenKind::Comma)? {
                    break;
                }
            }

            self.consume(TokenKind::RightBrace)?;
            ImportedSymbols::Named(imported)
        };

        // Expect 'from' keyword (as contextual keyword)
        match &self.current {
            Some(tok) if tok.kind == TokenKind::Identifier && self.lexeme(tok) == "from" => {
                self.advance();
            }
            _ => {
                return Err(ParserError::UnexpectedToken {
                    expected: "from".into(),
                    actual: format!("{:?}", self.current),
                    token: self.current.clone(),
                });
            }
        }

        // Parse import path
        let path_start = self.current.as_ref().map(|t| t.start).unwrap_or(0);

        let path = if matches!(self.current.as_ref().map(|t| &t.kind), Some(TokenKind::Dot)) {
            // Relative path: ./foo.tlk or ../foo.tlk
            let mut path_str = String::new();

            while let Some(ref current) = self.current.clone() {
                match &current.kind {
                    TokenKind::Dot => {
                        path_str.push('.');
                        self.advance();
                    }
                    TokenKind::Slash => {
                        path_str.push('/');
                        self.advance();
                    }
                    TokenKind::Identifier => {
                        path_str.push_str(self.lexeme(current));
                        self.advance();
                    }
                    _ => break,
                }
            }

            ImportPath::Relative(path_str)
        } else {
            // Package name: collections
            let (pkg_name, _) = self.identifier()?;
            ImportPath::Package(pkg_name)
        };

        let path_end = self.current.as_ref().map(|t| t.start).unwrap_or(path_start);
        let path_span = Span {
            start: path_start,
            end: path_end,
            file_id: self.file_id,
        };

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::Import(Import {
                symbols,
                path,
                path_span,
            }),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn typealias(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Typealias)?;
        let (lhs, lhs_span) = self.identifier()?;
        self.consume(TokenKind::Equals)?;
        let rhs = self.type_annotation()?;
        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::TypeAlias(lhs.into(), lhs_span, rhs),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn init_decl(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Init)?;
        self.consume(TokenKind::LeftParen)?;
        let params = self.parameters()?;
        self.consume(TokenKind::RightParen)?;

        let body = self.block(BlockContext::Func, true)?;
        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::Init {
                name: Name::Raw("init".into()),
                params,
                body,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn method_decl(&mut self, context: BlockContext, is_static: bool) -> Result<Decl, ParserError> {
        let func_decl = self.func_decl(context, true)?;
        match func_decl.kind {
            DeclKind::Func(func) => Ok(Decl {
                id: func.id,
                span: func_decl.span,
                visibility: func_decl.visibility,
                kind: DeclKind::Method {
                    func: Box::new(func),
                    is_static,
                },
            }),
            DeclKind::FuncSignature(func_sig) => Ok(Decl {
                id: func_decl.id,
                span: func_decl.span,
                visibility: func_decl.visibility,
                kind: DeclKind::MethodRequirement(func_sig),
            }),
            _ => unreachable!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn property_decl(&mut self, is_static: bool) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Let)?;
        let (name, name_span) = self.identifier()?;
        let type_annotation = if self.did_match(TokenKind::Colon)? {
            Some(self.type_annotation()?)
        } else {
            None
        };
        let default_value = if self.did_match(TokenKind::Equals)? {
            Some(self.expr()?.as_expr())
        } else {
            None
        };

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::Property {
                name: name.into(),
                name_span,
                is_static,
                type_annotation,
                default_value,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn variant_decl(&mut self, expect_case: bool) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        if expect_case {
            self.consume(TokenKind::Case)?;
        }
        let (name, name_span) = self.identifier()?;
        let values = if self.did_match(TokenKind::LeftParen)? {
            self.type_annotations(TokenKind::RightParen)?
        } else {
            vec![]
        };

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::EnumVariant(name.into(), name_span, values),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn nominal_decl(
        &mut self,
        entry: TokenKind,
        context: BlockContext,
    ) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(entry)?;
        let (name, name_span) = self.identifier()?;
        let generics = self.generics()?;

        let conformances = if context.allows_conformances() && self.did_match(TokenKind::Colon)? {
            self.conformances()?
        } else {
            vec![]
        };

        let body = self.body_block(context)?;

        let kind = match context {
            BlockContext::Enum => DeclKind::Enum {
                name: name.into(),
                name_span,
                generics,
                body,
            },
            BlockContext::Struct => DeclKind::Struct {
                name: name.into(),
                name_span,
                generics,
                body,
            },
            BlockContext::Extend => DeclKind::Extend {
                name: name.into(),
                name_span,
                conformances,
                generics,
                body,
            },
            BlockContext::Protocol => DeclKind::Protocol {
                name: name.into(),
                name_span,
                conformances,
                generics,
                body,
            },
            _ => {
                return Err(ParserError::UnexpectedToken {
                    expected: "Wrong context".into(),
                    actual: format!("{context:?}"),
                    token: self.current.clone(),
                });
            }
        };

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind,
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn let_decl(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Let)?;
        let lhs = self.parse_pattern()?;

        let type_annotation = if self.did_match(TokenKind::Colon)? {
            Some(self.type_annotation()?)
        } else {
            None
        };
        let rhs = if self.did_match(TokenKind::Equals)? {
            Some(self.expr()?.as_expr())
        } else {
            None
        };

        if self.did_match(TokenKind::Else)? {
            let else_body = self.block(BlockContext::If, true)?;
            return self.desugar_let_else(tok, lhs, rhs, else_body);
        }

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn func_decl(
        &mut self,
        context: BlockContext,
        consume_func_keyword: bool,
    ) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();

        let kind = match self.func(context, consume_func_keyword)? {
            FuncOrFuncSignature::Func(func) => DeclKind::Func(func),
            FuncOrFuncSignature::FuncSignature(func_sig) => DeclKind::FuncSignature(func_sig),
        };

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind,
        })
    }

    fn func(
        &mut self,
        context: BlockContext,
        consume_func_keyword: bool,
    ) -> Result<FuncOrFuncSignature, ParserError> {
        let tok = self.push_source_location();

        if consume_func_keyword {
            self.consume(TokenKind::Func)?;
        }

        let (name, name_span) = self.identifier().unwrap_or_else(|_| {
            (
                format!("#fn_{:?}", self.current),
                #[allow(clippy::panic)]
                self.current
                    .as_ref()
                    .unwrap_or_else(|| unreachable!("no current token"))
                    .span(self.file_id),
            )
        });

        let generics = self.generics()?;

        self.consume(TokenKind::LeftParen)?;
        let params = self.parameters()?;
        self.consume(TokenKind::RightParen)?;

        let mut names = vec![];
        let mut spans = vec![];
        let mut is_open = false;
        if self.peek_is(TokenKind::SingleQuote) {
            self.advance();
            // It's an effect list
            self.consume(TokenKind::LeftBracket)?;
            while !self.did_match(TokenKind::RightBracket)? && !self.did_match(TokenKind::EOF)? {
                if let Ok((name, span)) = self.identifier() {
                    names.push(Name::Raw(name));
                    spans.push(span);
                    self.consume(TokenKind::Comma).ok();
                } else if self.did_match(TokenKind::DotDot)? {
                    is_open = true;
                } else {
                    return Err(ParserError::UnexpectedToken {
                        expected: "effect name".to_string(),
                        actual: format!("{:?}", self.current),
                        token: None,
                    });
                }
            }
        } else if let Some(tok) = self.current.clone()
            && tok.kind == TokenKind::EffectName
        {
            self.advance();
            names.push(Name::Raw(self.lexeme(&tok).to_string()));
            spans.push(Span {
                file_id: self.file_id,
                start: tok.start,
                end: tok.end,
            });
        } else {
            is_open = true;
        }

        let ret = if self.consume(TokenKind::Arrow).is_ok() {
            Some(self.type_annotation()?)
        } else {
            None
        };

        if context == BlockContext::Protocol && !self.peek_is(TokenKind::LeftBrace) {
            let ret = ret.map(Box::new);

            return self.save_meta(tok, |id, span| {
                FuncOrFuncSignature::FuncSignature(FuncSignature {
                    id,
                    span,
                    name: name.into(),
                    generics,
                    params,
                    effects: EffectSet {
                        names,
                        spans,
                        is_open,
                    },
                    ret,
                })
            });
        }

        let body = self.block(BlockContext::Func, true)?;
        self.save_meta(tok, |id, _span| {
            FuncOrFuncSignature::Func(Func {
                id,
                name: name.into(),
                name_span,
                effects: EffectSet {
                    names,
                    spans,
                    is_open,
                },
                generics,
                params,
                body,
                ret,
                attributes: vec![],
            })
        })
    }

    // MARK: Statements

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn stmt(&mut self) -> Result<Stmt, ParserError> {
        self.skip_semicolons_and_newlines();

        let Some(current) = &self.current else {
            return Err(ParserError::UnexpectedEndOfInput(None));
        };

        match &current.kind {
            TokenKind::If => self.if_stmt(),
            TokenKind::Loop => self.loop_stmt(),
            TokenKind::For => self.for_stmt(),
            TokenKind::Return => self.return_stmt(),
            TokenKind::Attribute if self.lexeme(current) == "handle" => self.effect_handler(),
            TokenKind::Continue => {
                let tok = self.push_source_location();
                self.consume(TokenKind::Continue)?;
                let expr = if self.peek_is(TokenKind::Newline)
                    || self.peek_is(TokenKind::Semicolon)
                    || self.peek_is(TokenKind::EOF)
                {
                    None
                } else {
                    Some(self.expr()?.as_expr())
                };
                self.save_meta(tok, |id, span| Stmt {
                    id,
                    span,
                    kind: StmtKind::Continue(expr),
                })
            }
            TokenKind::Break => {
                let tok = self.push_source_location();
                self.consume(TokenKind::Break)?;
                self.save_meta(tok, |id, span| Stmt {
                    id,
                    span,
                    kind: StmtKind::Break,
                })
            }
            _ => match self.expr()? {
                Node::Expr(expr) => Ok(Stmt {
                    id: expr.id,
                    span: expr.span,
                    kind: StmtKind::Expr(expr),
                }),
                Node::Stmt(stmt) => Ok(stmt),
                Node::InlineIRInstruction(ir) => Ok(Stmt {
                    id: ir.id,
                    span: ir.span,
                    kind: StmtKind::Expr(Expr {
                        id: ir.id,
                        span: ir.span,
                        kind: ExprKind::InlineIR(ir),
                    }),
                }),
                e => unreachable!("{e:?}"),
            },
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn if_expr(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::If)?;

        if self.peek_is(TokenKind::Let) {
            return self.if_let_match(tok, true);
        }

        let cond = self.expr_with_precedence(Precedence::Or)?;
        let body = self.block(BlockContext::If, true)?;
        self.consume(TokenKind::Else)?;
        let alt = self.block(BlockContext::If, true)?;

        self.save_meta(tok, |id, span| {
            Expr {
                id,
                span,
                kind: ExprKind::If(Box::new(cond.as_expr()), body, alt),
            }
            .into()
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn func_expr(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let FuncOrFuncSignature::Func(func) = self.func(BlockContext::None, true)? else {
            return Err(ParserError::IncompleteFuncSignature(
                "func must have a body".into(),
            ));
        };

        self.save_meta(tok, |id, span| {
            Expr {
                id,
                span,
                kind: ExprKind::Func(func),
            }
            .into()
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn if_stmt(&mut self) -> Result<Stmt, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::If)?;

        if self.peek_is(TokenKind::Let) {
            let match_node = self.if_let_match(tok, false)?;
            let expr = match_node.as_expr();
            return Ok(Stmt {
                id: expr.id,
                span: expr.span,
                kind: StmtKind::Expr(expr),
            });
        }

        self.push_context(ParseContext::If);
        let cond = self.expr_with_precedence(Precedence::Or)?;
        self.pop_context();
        let body = self.block(BlockContext::If, true)?;

        if self.did_match(TokenKind::Else)? {
            let alt = self.block(BlockContext::If, true)?;
            self.save_meta(tok, |id, span| Stmt {
                id,
                span,
                kind: StmtKind::If(cond.as_expr(), body, Some(alt)),
            })
        } else {
            self.save_meta(tok, |id, span| Stmt {
                id,
                span,
                kind: StmtKind::If(cond.as_expr(), body, None),
            })
        }
    }

    /// Shared helper for `if let` in both expression and statement position.
    /// Desugars `if let PAT = EXPR { BODY } [else { ALT }]` into a `match` with two arms.
    /// When `require_else` is true (expression position), the else block is required.
    fn if_let_match(&mut self, tok: LocToken, require_else: bool) -> Result<Node, ParserError> {
        self.consume(TokenKind::Let)?;
        let pattern = self.parse_pattern()?;
        self.consume(TokenKind::Equals)?;
        self.push_context(ParseContext::If);
        let scrutinee = self.expr()?;
        self.pop_context();
        let body = self.block(BlockContext::If, true)?;

        let alt = if require_else {
            self.consume(TokenKind::Else)?;
            self.block(BlockContext::If, true)?
        } else if self.did_match(TokenKind::Else)? {
            self.block(BlockContext::If, true)?
        } else {
            Block {
                id: self.next_id(),
                args: vec![],
                body: vec![],
                span: Span::SYNTHESIZED,
            }
        };

        let pattern_arm = MatchArm {
            id: self.next_id(),
            pattern,
            body,
            span: Span::SYNTHESIZED,
        };

        let wildcard_arm = MatchArm {
            id: self.next_id(),
            pattern: Pattern {
                id: self.next_id(),
                kind: PatternKind::Wildcard,
                span: Span::SYNTHESIZED,
            },
            body: alt,
            span: Span::SYNTHESIZED,
        };

        self.save_meta(tok, |id, span| {
            Expr {
                id,
                span,
                kind: ExprKind::Match(
                    Box::new(scrutinee.as_expr()),
                    vec![pattern_arm, wildcard_arm],
                ),
            }
            .into()
        })
    }

    /// Desugars `let PAT = EXPR else { BODY }` into:
    /// - 0 binders: `let _ = match EXPR { PAT -> (), _ -> BODY }`
    /// - 1 binder:  `let x = match EXPR { PAT -> x, _ -> BODY }`
    /// - N binders: `let (a, b) = match EXPR { PAT -> (a, b), _ -> BODY }`
    fn desugar_let_else(
        &mut self,
        tok: LocToken,
        pattern: Pattern,
        rhs: Option<Expr>,
        else_body: Block,
    ) -> Result<Decl, ParserError> {
        let scrutinee = rhs.unwrap_or(Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Tuple(vec![]),
        });

        let binder_names = collect_pattern_binder_names(&pattern);

        // Build the success arm body expression
        let success_body_expr: Expr = match binder_names.len() {
            0 => Expr {
                id: self.next_id(),
                span: Span::SYNTHESIZED,
                kind: ExprKind::Tuple(vec![]),
            },
            1 => Expr {
                id: self.next_id(),
                span: Span::SYNTHESIZED,
                kind: ExprKind::Variable(binder_names[0].clone()),
            },
            _ => {
                let items = binder_names
                    .iter()
                    .map(|name| Expr {
                        id: self.next_id(),
                        span: Span::SYNTHESIZED,
                        kind: ExprKind::Variable(name.clone()),
                    })
                    .collect();
                Expr {
                    id: self.next_id(),
                    span: Span::SYNTHESIZED,
                    kind: ExprKind::Tuple(items),
                }
            }
        };

        let success_block = Block {
            id: self.next_id(),
            args: vec![],
            body: vec![Node::Expr(success_body_expr)],
            span: Span::SYNTHESIZED,
        };

        let pattern_arm = MatchArm {
            id: self.next_id(),
            pattern,
            body: success_block,
            span: Span::SYNTHESIZED,
        };

        let wildcard_pat_id = self.next_id();
        let wildcard_arm = MatchArm {
            id: self.next_id(),
            pattern: Pattern {
                id: wildcard_pat_id,
                kind: PatternKind::Wildcard,
                span: Span::SYNTHESIZED,
            },
            body: else_body,
            span: Span::SYNTHESIZED,
        };

        let match_expr = Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Match(Box::new(scrutinee), vec![pattern_arm, wildcard_arm]),
        };

        // Build the outer let pattern for the binders
        let outer_pattern = match binder_names.len() {
            0 => Pattern {
                id: self.next_id(),
                kind: PatternKind::Wildcard,
                span: Span::SYNTHESIZED,
            },
            1 => Pattern {
                id: self.next_id(),
                kind: PatternKind::Bind(binder_names[0].clone()),
                span: Span::SYNTHESIZED,
            },
            _ => {
                let items = binder_names
                    .iter()
                    .map(|name| Pattern {
                        id: self.next_id(),
                        kind: PatternKind::Bind(name.clone()),
                        span: Span::SYNTHESIZED,
                    })
                    .collect();
                Pattern {
                    id: self.next_id(),
                    kind: PatternKind::Tuple(items),
                    span: Span::SYNTHESIZED,
                }
            }
        };

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::Let {
                lhs: outer_pattern,
                type_annotation: None,
                rhs: Some(match_expr),
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn loop_stmt(&mut self) -> Result<Stmt, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Loop)?;

        let cond = if !self.peek_is(TokenKind::LeftBrace) {
            self.push_context(ParseContext::Loop);
            let result = Some(self.expr_with_precedence(Precedence::Or)?);
            self.pop_context();
            result
        } else {
            None
        };

        let body = self.block(BlockContext::Loop, true)?;
        self.save_meta(tok, |id, span| Stmt {
            id,
            span,
            kind: StmtKind::Loop(cond.map(|c| c.as_expr()), body),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn for_stmt(&mut self) -> Result<Stmt, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::For)?;
        let pattern = self.parse_pattern()?;
        self.consume(TokenKind::In)?;
        self.push_context(ParseContext::For);
        let iterable = self.expr()?.as_expr();
        self.pop_context();
        let body = self.block(BlockContext::Loop, true)?;

        self.save_meta(tok, |id, span| Stmt {
            id,
            span,
            kind: StmtKind::For {
                pattern,
                iterable: Box::new(iterable),
                body,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn return_stmt(&mut self) -> Result<Stmt, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Return)?;

        if self.peek_is(TokenKind::Newline) || self.peek_is(TokenKind::RightBrace) {
            return self.save_meta(tok, |id, span| Stmt {
                id,
                span,
                kind: StmtKind::Return(None),
            });
        }

        let rhs = Box::new(self.expr_with_precedence(Precedence::None)?);
        self.save_meta(tok, |id, span| Stmt {
            id,
            span,
            kind: StmtKind::Return(Some(rhs.as_expr())),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn attribute(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let Some(attr_tok) = self.advance() else {
            unreachable!()
        };

        let attr = self.lexeme(&attr_tok);
        if attr == "_ir" {
            return self.inline_ir(tok);
        }

        Err(ParserError::CannotAssign) //TODO
    }

    fn consume_register(&mut self) -> Result<Register, ParserError> {
        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEndOfInput(Some(
                "IR Register".into(),
            )));
        };

        if current.kind != TokenKind::IRRegister {
            return Err(ParserError::UnexpectedToken {
                expected: "IR Register".into(),
                actual: current.kind.as_str().to_string(),
                token: Some(current),
            });
        }

        let reg = self.lexeme(&current);
        self.advance();

        Ok(Register(reg.to_string()))
    }

    fn inline_ir(&mut self, tok: LocToken) -> Result<Node, ParserError> {
        let mut binds = vec![];

        if self.did_match(TokenKind::LeftParen)? {
            while !(self.did_match(TokenKind::RightParen)? || self.did_match(TokenKind::EOF)?) {
                binds.push(self.expr()?.as_expr());
                self.consume(TokenKind::Comma).ok();
            }
        }

        self.consume(TokenKind::LeftBrace)?;

        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEndOfInput(None));
        };

        let ir_instr = if current.kind == TokenKind::IRRegister {
            let dest = Register(self.lexeme(&current).to_string());
            self.advance();
            self.consume(TokenKind::Equals)?;
            let (instr, instr_span) = self.identifier()?;
            match instr.as_str() {
                "const" => {
                    let ty = self.type_annotation()?;
                    let val = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Constant { dest, ty, val },
                    })
                }
                "cmp" => {
                    let ty = self.type_annotation()?;
                    let lhs = self.ir_value()?;
                    let op = self
                        .consume_any(vec![
                            TokenKind::Plus,
                            TokenKind::Minus,
                            TokenKind::Star,
                            TokenKind::Slash,
                            TokenKind::Less,
                            TokenKind::BangEquals,
                            TokenKind::EqualsEquals,
                            TokenKind::LessEquals,
                            TokenKind::Greater,
                            TokenKind::GreaterEquals,
                            TokenKind::Caret,
                            TokenKind::Pipe,
                            TokenKind::PipePipe,
                            TokenKind::AmpAmp,
                        ])?
                        .kind;
                    let rhs = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Cmp {
                            dest,
                            lhs,
                            op,
                            rhs,
                            ty,
                        },
                    })
                }
                op @ ("add" | "sub" | "mul" | "div") => {
                    let ty = self.type_annotation()?;
                    let a = self.ir_value()?;
                    let b = self.ir_value()?;
                    let kind = match op {
                        "add" => InlineIRInstructionKind::Add { dest, ty, a, b },
                        "sub" => InlineIRInstructionKind::Sub { dest, ty, a, b },
                        "mul" => InlineIRInstructionKind::Mul { dest, ty, a, b },
                        "div" => InlineIRInstructionKind::Div { dest, ty, a, b },
                        _ => unreachable!(),
                    };
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind,
                    })
                }
                "ref" => {
                    let ty = self.type_annotation()?;
                    let val = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Ref { dest, ty, val },
                    })
                }
                "call" => {
                    let ty = self.type_annotation()?;
                    let callee = self.ir_value()?;
                    let args = self.ir_values()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Call {
                            dest,
                            ty,
                            callee,
                            args,
                        },
                    })
                }
                "record" => {
                    let ty = self.type_annotation()?;
                    let record = self.ir_values()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Record { dest, ty, record },
                    })
                }
                "getfield" => {
                    let ty = self.type_annotation()?;
                    let record = self.consume_register()?;
                    let field = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::GetField {
                            dest,
                            ty,
                            record,
                            field,
                        },
                    })
                }
                "setfield" => {
                    let ty = self.type_annotation()?;
                    let record = self.consume_register()?;
                    let field = self.ir_value()?;
                    let val = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::SetField {
                            dest,
                            ty,
                            record,
                            field,
                            val,
                        },
                    })
                }
                "alloc" => {
                    let ty = self.type_annotation()?;
                    let count = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Alloc { dest, ty, count },
                    })
                }
                "load" => {
                    let ty = self.type_annotation()?;
                    let addr = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Load { dest, ty, addr },
                    })
                }
                "gep" => {
                    let ty = self.type_annotation()?;
                    let addr = self.ir_value()?;
                    let offset_index = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Gep {
                            dest,
                            ty,
                            addr,
                            offset_index,
                        },
                    })
                }
                // I/O Instructions
                "io_open" => {
                    let path = self.ir_value()?;
                    let flags = self.ir_value()?;
                    let mode = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoOpen {
                            dest,
                            path,
                            flags,
                            mode,
                        },
                    })
                }
                "io_read" => {
                    let fd = self.ir_value()?;
                    let buf = self.ir_value()?;
                    let count = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoRead {
                            dest,
                            fd,
                            buf,
                            count,
                        },
                    })
                }
                "io_write" => {
                    let fd = self.ir_value()?;
                    let buf = self.ir_value()?;
                    let count = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoWrite {
                            dest,
                            fd,
                            buf,
                            count,
                        },
                    })
                }
                "io_close" => {
                    let fd = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoClose { dest, fd },
                    })
                }
                "io_ctl" => {
                    let fd = self.ir_value()?;
                    let op = self.ir_value()?;
                    let arg = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoCtl { dest, fd, op, arg },
                    })
                }
                "io_poll" => {
                    let fds = self.ir_value()?;
                    let count = self.ir_value()?;
                    let timeout = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoPoll {
                            dest,
                            fds,
                            count,
                            timeout,
                        },
                    })
                }
                "io_socket" => {
                    let domain = self.ir_value()?;
                    let socktype = self.ir_value()?;
                    let protocol = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoSocket {
                            dest,
                            domain,
                            socktype,
                            protocol,
                        },
                    })
                }
                "io_bind" => {
                    let fd = self.ir_value()?;
                    let addr = self.ir_value()?;
                    let port = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoBind {
                            dest,
                            fd,
                            addr,
                            port,
                        },
                    })
                }
                "io_listen" => {
                    let fd = self.ir_value()?;
                    let backlog = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoListen { dest, fd, backlog },
                    })
                }
                "io_connect" => {
                    let fd = self.ir_value()?;
                    let addr = self.ir_value()?;
                    let port = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoConnect {
                            dest,
                            fd,
                            addr,
                            port,
                        },
                    })
                }
                "io_accept" => {
                    let fd = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoAccept { dest, fd },
                    })
                }
                "io_sleep" => {
                    let ms = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IoSleep { dest, ms },
                    })
                }
                "trunc" => {
                    let val = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Trunc { dest, val },
                    })
                }
                "itof" => {
                    let val = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IntToFloat { dest, val },
                    })
                }
                _ => {
                    return Err(ParserError::UnexpectedToken {
                        expected: "ir instr".into(),
                        actual: instr,
                        token: self.previous.clone(),
                    });
                }
            }
        } else {
            let (instr, instr_span) = self.identifier()?;
            match instr.as_str() {
                "_print" => {
                    let val = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::_Print { val },
                    })
                }
                "store" => {
                    let ty = self.type_annotation()?;
                    let value = self.ir_value()?;
                    let addr = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Store { value, ty, addr },
                    })
                }
                "move" => {
                    let ty = self.type_annotation()?;
                    let from = self.ir_value()?;
                    let to = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Move { ty, from, to },
                    })
                }
                "copy" => {
                    let ty = self.type_annotation()?;
                    let from = self.ir_value()?;
                    let to = self.ir_value()?;
                    let length = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Copy {
                            ty,
                            from,
                            to,
                            length,
                        },
                    })
                }

                "free" => {
                    let addr = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Free { addr },
                    })
                }
                _ => {
                    return Err(ParserError::UnexpectedToken {
                        expected: "ir instr".into(),
                        actual: instr,
                        token: self.previous.clone(),
                    });
                }
            }
            // It's one of the instructions that doesn't start with a register
        }?;

        self.consume(TokenKind::RightBrace)?;

        Ok(Node::Expr(Expr {
            id: ir_instr.id,
            span: ir_instr.span,
            kind: ExprKind::InlineIR(ir_instr),
        }))
    }

    fn ir_values(&mut self) -> Result<Vec<Value>, ParserError> {
        self.consume(TokenKind::LeftParen)?;
        let mut args = vec![];
        while !(self.did_match(TokenKind::RightParen)? || self.did_match(TokenKind::EOF)?) {
            args.push(self.ir_value()?);
            self.consume(TokenKind::Comma).ok();
        }
        Ok(args)
    }

    fn ir_value(&mut self) -> Result<Value, ParserError> {
        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEndOfInput(Some("IR value".into())));
        };

        let val = match current.kind {
            TokenKind::IRRegister => Value::Reg(parse_lexed(self.lexeme(&current))),
            TokenKind::Int => Value::Int(parse_lexed(self.lexeme(&current))),
            TokenKind::Float => Value::Float(parse_lexed(self.lexeme(&current))),
            TokenKind::True => Value::Bool(true),
            TokenKind::False => Value::Bool(false),
            TokenKind::BoundVar => {
                let v = self.lexeme(&current);
                if !v.chars().all(|c| c.is_numeric()) {
                    return Err(ParserError::UnexpectedToken {
                        expected: "Numeric bound var".into(),
                        actual: v.into(),
                        token: self.current.clone(),
                    });
                }

                let i = v
                    .parse()
                    .map_err(|e| ParserError::BadLabel(format!("{e}")))?;
                Value::Bind(i)
            }
            TokenKind::Identifier if self.lexeme(&current) == "void" => Value::Void,
            _ => {
                return Err(ParserError::UnexpectedToken {
                    expected: "IR".to_string(),
                    actual: format!("{current:?}"),
                    token: self.current.clone(),
                });
            }
        };

        self.advance();

        Ok(val)
    }

    // MARK: Exprs

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn array(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::LeftBracket)?;
        let mut items = vec![];
        while !self.did_match(TokenKind::RightBracket)? {
            items.push(self.expr()?.as_expr());
            self.consume(TokenKind::Comma).ok();
        }
        self.save_meta(tok, |id, span| {
            Expr {
                id,
                span,
                kind: ExprKind::LiteralArray(items),
            }
            .into()
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn match_expr(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Match)?;
        self.push_context(ParseContext::Match);
        let scrutinee = self.expr()?;
        self.pop_context();

        self.consume(TokenKind::LeftBrace)?;

        let mut arms = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_newlines();
            let arm_tok = self.push_source_location();
            let pattern = self.parse_pattern()?;
            self.consume(TokenKind::Arrow)?;

            let body = self.block(BlockContext::MatchArmBody, true)?;
            arms.push(self.save_meta(arm_tok, |id, span| MatchArm {
                id,
                span,
                pattern,
                body,
            })?);

            self.consume(TokenKind::Comma).ok();
            self.skip_newlines();
        }

        self.save_meta(tok, |id, span| {
            Node::Expr(Expr {
                id,
                span,
                kind: ExprKind::Match(Box::new(scrutinee.as_expr()), arms),
            })
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn parse_pattern(&mut self) -> Result<Pattern, ParserError> {
        let tok = self.push_source_location();
        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEndOfInput(Some(
                "Expected match arm pattern".into(),
            )));
        };

        let kind = match current.kind {
            TokenKind::Int => {
                let val = self.lexeme(&current).to_string();
                self.advance();
                PatternKind::LiteralInt(val)
            }
            TokenKind::Float => {
                let val = self.lexeme(&current).to_string();
                self.advance();
                PatternKind::LiteralFloat(val)
            }
            TokenKind::True => {
                self.advance();
                PatternKind::LiteralTrue
            }
            TokenKind::False => {
                self.advance();
                PatternKind::LiteralFalse
            }
            TokenKind::Identifier => {
                let name = self.lexeme(&current).to_string();
                self.advance();
                if self.did_match(TokenKind::Dot)? {
                    let (member_name, member_name_span) = self.identifier()?;
                    let fields = self.pattern_fields()?;
                    PatternKind::Variant {
                        enum_name: Some(name.into()),
                        variant_name: member_name.to_string(),
                        variant_name_span: member_name_span,
                        fields,
                    }
                } else {
                    PatternKind::Bind(name.into())
                }
            }
            TokenKind::Underscore => {
                self.advance();
                PatternKind::Wildcard
            }
            TokenKind::Dot => {
                self.advance();
                let (member_name, member_name_span) = self.identifier()?;
                let fields = self.pattern_fields()?;

                PatternKind::Variant {
                    enum_name: None,
                    variant_name: member_name.to_string(),
                    variant_name_span: member_name_span,
                    fields,
                }
            }
            TokenKind::LeftParen => {
                self.advance();
                let mut items = vec![];
                while !self.did_match(TokenKind::RightParen)? {
                    items.push(self.parse_pattern()?);
                    self.consume(TokenKind::Comma).ok();
                }

                PatternKind::Tuple(items)
            }
            TokenKind::LeftBrace => {
                self.advance();
                self.parse_record_pattern()?
            }

            _ => {
                return Err(ParserError::UnexpectedToken {
                    expected: "Pattern".into(),
                    actual: format!("{:?}", current.kind),
                    token: Some(current),
                });
            }
        };

        if self.peek_is(TokenKind::Pipe) {
            let first_pattern = self.save_meta(tok, |id, span| Pattern { id, span, kind })?;
            let mut patterns = vec![first_pattern];

            while self.did_match(TokenKind::Pipe)? {
                patterns.push(self.parse_pattern()?);
            }

            let loc = self.push_lhs_location(patterns[0].id);
            return self.save_meta(loc, |id, span| Pattern {
                id,
                span,
                kind: PatternKind::Or(patterns),
            });
        }

        self.save_meta(tok, |id, span| Pattern { id, span, kind })
    }

    fn parse_record_pattern(&mut self) -> Result<PatternKind, ParserError> {
        self.skip_newlines();
        let mut fields: Vec<RecordFieldPattern> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            let Some(current) = &self.current.clone() else {
                return Err(ParserError::UnexpectedEndOfInput(Some(
                    "Expected record pattern".into(),
                )));
            };

            let tok = self.push_source_location();
            match &current.kind {
                TokenKind::DotDot => {
                    self.consume(TokenKind::DotDot).ok();

                    // "rest" must be the last item
                    if !self.peek_is(TokenKind::RightBrace) {
                        return Err(ParserError::UnexpectedToken {
                            expected: "}".into(),
                            actual: format!(
                                "got {:?}. Rest pattern must be at the end of record pattern",
                                self.current
                            ),
                            token: self.current.clone(),
                        });
                    }

                    let field = self.save_meta(tok, |id, span| RecordFieldPattern {
                        id,
                        span,
                        kind: RecordFieldPatternKind::Rest,
                    })?;
                    fields.push(field);
                    self.consume(TokenKind::RightBrace).ok();

                    break;
                }
                TokenKind::Identifier => {
                    let (name, name_span) = self.identifier()?;
                    let name = Name::Raw(name);
                    let kind = if self.peek_is(TokenKind::Colon) {
                        self.consume(TokenKind::Colon).ok();
                        let value = self.parse_pattern()?;
                        RecordFieldPatternKind::Equals {
                            name,
                            name_span,
                            value,
                        }
                    } else {
                        RecordFieldPatternKind::Bind(name)
                    };

                    let field =
                        self.save_meta(tok, |id, span| RecordFieldPattern { id, span, kind })?;
                    fields.push(field);
                }
                pat => {
                    return Err(ParserError::BadLabel(format!(
                        "Patter not handled: {pat:?}"
                    )));
                }
            }
            self.consume(TokenKind::Comma).ok();
        }

        Ok(PatternKind::Record { fields })
    }

    fn pattern_fields(&mut self) -> Result<Vec<Pattern>, ParserError> {
        let mut fields = vec![];
        if self.did_match(TokenKind::LeftParen)? {
            while !self.did_match(TokenKind::RightParen)? {
                fields.push(self.parse_pattern()?);
                self.consume(TokenKind::Comma).ok();
            }
        };
        Ok(fields)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn member_prefix(&mut self, can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Dot)?;

        let (name, name_span) = match self.current.clone() {
            Some(cur) if cur.kind == TokenKind::Identifier => match self.identifier() {
                Ok((name, span)) => (Label::Named(name), span),
                Err(err) => {
                    self.record_diagnostic(err);
                    let incomplete_member = ExprKind::Incomplete(IncompleteExpr::Member(None));
                    return Ok(Node::Expr(self.add_expr(incomplete_member, tok)?));
                }
            },
            Some(cur) if cur.kind == TokenKind::Int => {
                let val = self.lexeme(&cur).to_string();
                self.advance();
                (
                    Label::Positional(str::parse(&val).map_err(|_| ParserError::BadLabel(val))?),
                    self.current
                        .as_ref()
                        .unwrap_or_else(|| unreachable!("no current token"))
                        .span(self.file_id),
                )
            }
            Some(_) | None => {
                self.record_diagnostic(ParserError::ExpectedIdentifier(self.current.clone()));
                let incomplete_member = ExprKind::Incomplete(IncompleteExpr::Member(None));
                return Ok(Node::Expr(self.add_expr(incomplete_member, tok)?));
            }
        };

        let member = self.add_expr(ExprKind::Member(None, name, name_span), tok)?;

        self.skip_semicolons_and_newlines();

        let expr = if let Some(call_expr) = self.check_call(&member, can_assign)? {
            call_expr
        } else {
            member
        };

        if self.did_match(TokenKind::Equals)? {
            if can_assign {
                let loc = self.push_source_location();
                let rhs = self.expr_with_precedence(Precedence::Assignment)?;
                return self.save_meta(loc, |id, span| {
                    Stmt {
                        id,
                        span,
                        kind: StmtKind::Assignment(expr.into(), rhs.as_expr().into()),
                    }
                    .into()
                });
            } else {
                return Err(ParserError::CannotAssign);
            }
        }

        Ok(Node::Expr(expr))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn member_infix(
        &mut self,
        can_assign: bool,
        lhs: Expr,
    ) -> Result<Node, ParserError> {
        let tok = self.push_lhs_location(lhs.id);
        self.consume(TokenKind::Dot)?;

        let (name, name_span) = match self.current.clone() {
            Some(cur) if cur.kind == TokenKind::Identifier => match self.identifier() {
                Ok((name, span)) => (Label::Named(name), span),
                Err(err) => {
                    self.record_diagnostic(err);
                    let incomplete_member =
                        ExprKind::Incomplete(IncompleteExpr::Member(Some(Box::new(lhs))));
                    return Ok(Node::Expr(self.add_expr(incomplete_member, tok)?));
                }
            },
            Some(cur) if cur.kind == TokenKind::Int => {
                let val = self.lexeme(&cur).to_string();
                self.advance();
                (
                    Label::Positional(str::parse(&val).map_err(|_| ParserError::BadLabel(val))?),
                    self.current
                        .as_ref()
                        .expect("no current token")
                        .span(self.file_id),
                )
            }
            Some(_) | None => {
                self.record_diagnostic(ParserError::ExpectedIdentifier(self.current.clone()));
                let incomplete_member =
                    ExprKind::Incomplete(IncompleteExpr::Member(Some(Box::new(lhs))));
                return Ok(Node::Expr(self.add_expr(incomplete_member, tok)?));
            }
        };

        let member = self.add_expr(ExprKind::Member(Some(Box::new(lhs)), name, name_span), tok)?;

        self.skip_semicolons_and_newlines();

        let expr = if let Some(call_expr) = self.check_call(&member, can_assign)? {
            call_expr
        } else {
            member
        };

        if self.did_match(TokenKind::Equals)? {
            if can_assign {
                let loc = self.push_source_location();
                let rhs = self.expr_with_precedence(Precedence::Assignment)?;
                return self.save_meta(loc, |id, span| {
                    Node::Stmt(Stmt {
                        id,
                        span,
                        kind: StmtKind::Assignment(expr.into(), rhs.as_expr().into()),
                    })
                });
            } else {
                return Err(ParserError::CannotAssign);
            }
        }

        Ok(Node::Expr(expr))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn unary(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let op = self.consume_any(vec![TokenKind::Minus, TokenKind::Bang])?;
        let current_precedence = Precedence::handler(&Some(op.clone()))?.precedence;
        let rhs = Box::new(self.expr_with_precedence(current_precedence)?);

        Ok(self
            .add_expr(ExprKind::Unary(op.kind, Box::new(rhs.as_expr())), tok)?
            .into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub fn binary(&mut self, _can_assign: bool, lhs: Expr) -> Result<Node, ParserError> {
        let tok = self.push_lhs_location(lhs.id);

        let op = self.consume_any(vec![
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Star,
            TokenKind::Slash,
            TokenKind::Less,
            TokenKind::BangEquals,
            TokenKind::EqualsEquals,
            TokenKind::LessEquals,
            TokenKind::Greater,
            TokenKind::GreaterEquals,
            TokenKind::Caret,
            TokenKind::Pipe,
            TokenKind::PipePipe,
            TokenKind::AmpAmp,
        ])?;

        let current_precedence = Precedence::handler(&Some(op.clone()))?.precedence;
        let rhs = Box::new(self.expr_with_precedence(current_precedence)?);

        Ok(self
            .add_expr(
                ExprKind::Binary(Box::new(lhs), op.kind, Box::new(rhs.as_expr())),
                tok,
            )?
            .into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn block_expr(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::LeftBrace)?;

        let kind = if self.peek_is_record_literal() {
            self.record_literal_body()?
        } else {
            ExprKind::Block(self.block(BlockContext::None, false)?)
        };

        self.save_meta(tok, |id, span| Node::Expr(Expr { id, span, kind }))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub fn literal(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let current = self.advance().expect("unreachable");
        let lexeme = self.lexeme(&current);
        let expr = match current.kind {
            TokenKind::Int => self.add_expr(ExprKind::LiteralInt(lexeme.to_string()), tok),
            TokenKind::Float => self.add_expr(ExprKind::LiteralFloat(lexeme.to_string()), tok),
            TokenKind::True => self.add_expr(ExprKind::LiteralTrue, tok),
            TokenKind::False => self.add_expr(ExprKind::LiteralFalse, tok),
            TokenKind::StringLiteral => {
                // Strip surrounding quotes but keep escape sequences intact
                let inner = &lexeme[1..lexeme.len() - 1];
                self.add_expr(ExprKind::LiteralString(inner.to_string()), tok)
            }
            _ => unreachable!(),
        };

        Ok(expr?.into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn variable(&mut self, can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let (name, _span) = self.identifier()?;
        let variable = self.add_expr(ExprKind::Variable(Name::Raw(name.to_string())), tok)?;

        self.skip_newlines();

        if let Some(call_expr) = self.check_call(&variable, can_assign)? {
            Ok(call_expr.into())
        } else if can_assign && self.did_match(TokenKind::Equals)? {
            let tok = self.push_lhs_location(variable.id);
            let rhs = self.expr()?;
            self.save_meta(tok, |id, span| {
                Stmt {
                    id,
                    span,
                    kind: StmtKind::Assignment(variable.into(), rhs.as_expr().into()),
                }
                .into()
            })
        } else {
            Ok(variable.into())
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn tuple(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();

        self.consume(TokenKind::LeftParen)?;

        if self.did_match(TokenKind::RightParen)? {
            return Ok(self.add_expr(ExprKind::Tuple(vec![]), tok)?.into());
        }

        let child = self.expr_with_precedence(Precedence::Assignment)?.as_expr();

        if self.did_match(TokenKind::RightParen)? {
            return Ok(self.add_expr(ExprKind::Tuple(vec![child]), tok)?.into());
        }

        self.consume(TokenKind::Comma)?;

        let mut items = vec![child];
        while {
            items.push(self.expr_with_precedence(Precedence::Assignment)?.as_expr());
            self.did_match(TokenKind::Comma)?
        } {}

        self.consume(TokenKind::RightParen)?;

        Ok(self.add_expr(ExprKind::Tuple(items), tok)?.into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn expr(&mut self) -> Result<Node, ParserError> {
        self.expr_with_precedence(Precedence::Assignment)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn expr_with_precedence(&mut self, precedence: Precedence) -> Result<Node, ParserError> {
        tracing::trace!(
            "Parsing {:?} with precedence: {:?}",
            self.current,
            precedence
        );

        self.skip_newlines();

        let mut lhs: Option<Node> = None;
        let mut handler = Precedence::handler(&self.current)?;

        if let Some(prefix) = handler.prefix {
            lhs = Some(prefix(self, precedence.can_assign())?);
        }

        let mut i = 0;

        while {
            self.skip_newlines();
            handler = Precedence::handler(&self.current)?;
            precedence < handler.precedence
        } {
            i += 1;

            if let Some(infix) = handler.infix {
                if let Some(previous_lhs) = lhs {
                    lhs = Some(infix(
                        self,
                        precedence.can_assign(),
                        previous_lhs.as_expr(),
                    )?);
                }
            } else {
                break;
            }

            if self.did_match(TokenKind::Newline)? {
                break;
            }

            if i > 100 {
                self.advance();
                return Err(ParserError::InfiniteLoop(self.current.clone()));
            }
        }

        #[allow(clippy::expect_fun_call)]
        if let Some(lhs) = lhs {
            self.check_as(lhs)
        } else {
            self.advance();
            Err(ParserError::UnexpectedEndOfInput(Some(format!(
                "expected lhs. {:?}",
                self.ast
            ))))
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn check_as(&mut self, lhs: Node) -> Result<Node, ParserError> {
        if self.did_match(TokenKind::As)? {
            let tok = self.push_lhs_location(lhs.node_id());
            let rhs = self.type_annotation()?;
            self.save_meta(tok, |id, span| {
                Expr {
                    id,
                    span,
                    kind: ExprKind::As(lhs.as_expr().into(), rhs),
                }
                .into()
            })
        } else {
            Ok(lhs)
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn effect_callee(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let (effect_name, effect_name_span) = self.effect_name()?;

        // Parse optional type arguments: 'effect<Type>(...)
        let type_args = if self.peek_is(TokenKind::Less) {
            self.consume(TokenKind::Less)?;
            self.type_annotations(TokenKind::Greater)?
        } else {
            vec![]
        };

        self.consume(TokenKind::LeftParen)?;
        let args = if self.did_match(TokenKind::RightParen)? {
            vec![]
        } else {
            let args = self.arguments()?;
            self.consume(TokenKind::RightParen)?;
            args
        };
        self.save_meta(tok, |id, span| {
            Expr {
                id,
                span,
                kind: ExprKind::CallEffect {
                    effect_name: effect_name.into(),
                    effect_name_span,
                    type_args,
                    args,
                },
            }
            .into()
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn effect_handler(&mut self) -> Result<Stmt, ParserError> {
        let tok = self.push_source_location();
        self.advance(); // Eat the @handle
        let (effect_name, effect_name_span) = self.effect_name()?;
        let body = self.block(BlockContext::None, true)?;
        self.save_meta(tok, |id, span| Stmt {
            id,
            span,
            kind: StmtKind::Handling {
                effect_name: effect_name.into(),
                effect_name_span,
                body,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn check_call(
        &mut self,
        callee: &Expr,
        can_assign: bool,
    ) -> Result<Option<Expr>, ParserError> {
        let prev = self
            .previous
            .as_ref()
            .ok_or(ParserError::UnexpectedEndOfInput(None))?;
        let cur = self
            .current
            .as_ref()
            .ok_or(ParserError::UnexpectedEndOfInput(None))?;

        if self.peek_is(TokenKind::Less) && prev.end == cur.start {
            self.consume(TokenKind::Less)?;
            let type_args = self.type_annotations(TokenKind::Greater)?;
            self.consume(TokenKind::LeftParen)?;
            return Ok(Some(self.call(can_assign, type_args, callee.clone())?));
        }

        if self.did_match(TokenKind::LeftParen)? {
            self.skip_newlines();
            return Ok(Some(self.call(can_assign, vec![], callee.clone())?));
        }

        // Check for trailing-block-only call: `foo { block }` without parens
        if self.current_context().allows_trailing_blocks() && self.peek_is(TokenKind::LeftBrace) {
            return Ok(Some(self.call_with_trailing_block_only(callee.clone())?));
        }

        Ok(None)
    }

    /// Parse a call with only a trailing block (no parens): `foo { block }`
    fn call_with_trailing_block_only(&mut self, callee: Expr) -> Result<Expr, ParserError> {
        let tok = self.push_lhs_location(callee.id);
        let trailing_block = self.block(BlockContext::None, true)?;

        self.add_expr(
            ExprKind::Call {
                callee: Box::new(callee),
                type_args: vec![],
                args: vec![],
                trailing_block: Some(trailing_block),
            },
            tok,
        )
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn call(
        &mut self,
        can_assign: bool,
        type_args: Vec<TypeAnnotation>,
        callee: Expr,
    ) -> Result<Expr, ParserError> {
        let tok = self.push_lhs_location(callee.id);
        self.skip_newlines();

        let args = if self.did_match(TokenKind::RightParen)? {
            vec![]
        } else {
            let args = self.arguments()?;
            self.consume(TokenKind::RightParen)?;
            args
        };

        // Check for trailing block after the closing paren.
        // We only allow trailing blocks at the top level context, not inside
        // match/if/loop/for scrutinees where { starts the body.
        let trailing_block = if self.current_context().allows_trailing_blocks()
            && self.peek_is(TokenKind::LeftBrace)
        {
            Some(self.block(BlockContext::None, true)?)
        } else {
            None
        };

        let call = self.add_expr(
            ExprKind::Call {
                callee: Box::new(callee),
                type_args,
                args,
                trailing_block,
            },
            tok,
        )?;

        if self.peek_is(TokenKind::LeftParen)
            && let Some(next_call) = self.check_call(&call, can_assign)?
        {
            Ok(next_call)
        } else {
            Ok(call)
        }
    }

    // MARK: Helpers

    fn arguments(&mut self) -> Result<Vec<CallArg>, ParserError> {
        let mut args: Vec<CallArg> = vec![];
        let mut i = 0;
        while {
            let tok = self.push_source_location();

            if matches!(
                &self.current,
                Some(Token {
                    kind: TokenKind::Identifier,
                    ..
                })
            ) && matches!(
                &self.next,
                Some(Token {
                    kind: TokenKind::Colon,
                    ..
                })
            ) {
                // we've got an argument label
                let Some((label, label_span)) = self.identifier().ok() else {
                    return Err(ParserError::ExpectedIdentifier(self.current.clone()));
                };
                let tok = self.push_source_location();
                self.consume(TokenKind::Colon)?;
                let value = self.expr_with_precedence(Precedence::Assignment)?;
                args.push(self.save_meta(tok, |id, span| CallArg {
                    id,
                    span,
                    label: label.into(),
                    label_span,
                    value: value.as_expr(),
                })?);
            } else {
                let value = self.expr_with_precedence(Precedence::Assignment)?;
                args.push(self.save_meta(tok, |id, span| CallArg {
                    id,
                    span,
                    label: Label::Positional(i),
                    label_span: span,
                    value: value.as_expr(),
                })?);
            }

            i += 1;
            self.did_match(TokenKind::Comma)?
        } {}

        Ok(args)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn type_annotation(&mut self) -> Result<TypeAnnotation, ParserError> {
        let mut base = self.type_annotation_base()?;

        while self.did_match(TokenKind::QuestionMark)? {
            let tok = self.push_lhs_location(base.id);
            base = self.save_meta(tok, |id, span| TypeAnnotation {
                id,
                span,
                kind: TypeAnnotationKind::Nominal {
                    name: "Optional".into(),
                    name_span: span,
                    generics: vec![base],
                },
            })?;
        }

        Ok(base)
    }

    fn type_annotation_base(&mut self) -> Result<TypeAnnotation, ParserError> {
        let tok = self.push_source_location();

        if self.did_match(TokenKind::LeftParen)? {
            // it's a func type or tuple repr
            let mut sig_args = vec![];
            while !self.did_match(TokenKind::RightParen)? {
                sig_args.push(self.type_annotation()?);
                self.consume(TokenKind::Comma).ok();
            }
            if self.did_match(TokenKind::Arrow)? {
                let ret = self.type_annotation()?;
                return self.save_meta(tok, |id, span| TypeAnnotation {
                    id,
                    span,
                    kind: TypeAnnotationKind::Func {
                        params: sig_args,
                        returns: Box::new(ret),
                    },
                });
            } else {
                return self.save_meta(tok, |id, span| TypeAnnotation {
                    id,
                    span,
                    kind: TypeAnnotationKind::Tuple(sig_args),
                });
            }
        }

        // // Check for record type: {x: Int, y: Int, ..R}
        if self.did_match(TokenKind::LeftBrace)? {
            let mut fields: Vec<RecordFieldTypeAnnotation> = vec![];

            while !self.did_match(TokenKind::RightBrace)? {
                let tok = self.push_source_location();
                let (label, label_span) = self.identifier()?;
                let label = Name::Raw(label);
                self.consume(TokenKind::Colon)?;
                let value = self.type_annotation()?;
                fields.push(self.save_meta(tok, |id, span| RecordFieldTypeAnnotation {
                    id,
                    label,
                    label_span,
                    value,
                    span,
                })?);
                self.consume(TokenKind::Comma).ok();
            }

            return self.save_meta(tok, |id, span| TypeAnnotation {
                id,
                span,
                kind: TypeAnnotationKind::Record { fields },
            });
        }

        // It's a nominal.
        let (name, name_span) = self.identifier()?;
        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                let generic = self.type_annotation()?;
                generics.push(generic);
                self.consume(TokenKind::Comma).ok();
            }
        }

        let mut base = self.save_meta(tok, |id, span| TypeAnnotation {
            id,
            span,
            kind: TypeAnnotationKind::Nominal {
                name: name.into(),
                name_span,
                generics,
            },
        })?;

        if !self.did_match(TokenKind::Dot)? {
            return Ok(base);
        }

        loop {
            let tok = self.push_source_location();
            let (member_name, member_span) = self.identifier()?;
            let member: Label = member_name.into();
            let member_generics = if self.did_match(TokenKind::Less)? {
                self.type_annotations(TokenKind::Greater)?
            } else {
                vec![]
            };

            base = self.save_meta(tok, |id, span| TypeAnnotation {
                id,
                span,
                kind: TypeAnnotationKind::NominalPath {
                    base: Box::new(base),
                    member,
                    member_span,
                    member_generics,
                },
            })?;

            if self.did_match(TokenKind::Dot)? {
                continue;
            }

            break;
        }

        Ok(base)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn conformances(&mut self) -> Result<Vec<TypeAnnotation>, ParserError> {
        let mut conformances: Vec<TypeAnnotation> = vec![];

        while {
            conformances.push(self.type_annotation()?);
            self.did_match(TokenKind::Comma)?
        } {}

        Ok(conformances)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn type_annotations(&mut self, closer: TokenKind) -> Result<Vec<TypeAnnotation>, ParserError> {
        let mut annotations: Vec<TypeAnnotation> = vec![];

        while !self.did_match(closer)? {
            annotations.push(self.type_annotation()?);
            self.consume(TokenKind::Comma).ok();
        }

        Ok(annotations)
    }

    fn body_block(&mut self, context: BlockContext) -> Result<Body, ParserError> {
        self.body(context, true)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn block(
        &mut self,
        context: BlockContext,
        consumes_left_brace: bool,
    ) -> Result<Block, ParserError> {
        self.skip_newlines();
        let tok = self.push_source_location();

        if context == BlockContext::MatchArmBody && !self.peek_is(TokenKind::LeftBrace) {
            let stmt = self.stmt()?;
            return self.save_meta(tok, |id, span| Block {
                id,
                span,
                args: vec![],
                body: vec![stmt.into()],
            });
        };

        if consumes_left_brace {
            self.consume(TokenKind::LeftBrace)?;
        }

        let args = self.block_args()?;

        self.skip_semicolons_and_newlines();
        let mut body = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            if context == BlockContext::Enum {
                // Special handling for multiple cases on one line
                if self.peek_is(TokenKind::Case) {
                    body.push(self.variant_decl(true)?.into());

                    while self.did_match(TokenKind::Comma)? {
                        body.push(self.variant_decl(false)?.into());
                    }

                    continue;
                }
            }

            if context == BlockContext::Protocol && self.peek_is(TokenKind::Associated) {
                body.push(self.associated_type()?.into());
                continue;
            }

            body.push(self.decl(context, false)?);

            self.skip_semicolons_and_newlines();
        }

        self.save_meta(tok, |id, span| Block {
            id,
            span,
            args,
            body,
        })
    }

    fn block_args(&mut self) -> Result<Vec<Parameter>, ParserError> {
        if self.peek_is(TokenKind::In) {
            self.consume(TokenKind::In)?;
            return Ok(vec![]);
        }

        // So we can rollback if we're not actually parsing block args
        let lexer = self.lexer.clone();
        let next = self.next.clone();
        let checkpoint = self.current.clone();
        let checkpoint_prev = self.previous.clone();
        let checkpoint_prev_before_newline = self.previous_before_newline.clone();
        let loc_stack_len = self.source_location_stack.len();
        let rollback = |parser: &mut Parser<'a>| {
            parser.lexer = lexer;
            parser.next = next;
            parser.current = checkpoint;
            parser.previous = checkpoint_prev;
            parser.previous_before_newline = checkpoint_prev_before_newline;
            parser.source_location_stack.truncate(loc_stack_len);
        };

        let mut params = vec![];

        loop {
            // Must be identifier
            let Ok((name, name_span)) = self.identifier() else {
                rollback(self);
                return Ok(vec![]);
            };

            let tok = self.push_source_location();

            let type_annotation = if self.did_match(TokenKind::Colon)? {
                Some(self.type_annotation()?)
            } else {
                None
            };

            let param = self.save_meta(tok, |id, span| Parameter {
                id,
                span,
                name: name.into(),
                name_span,
                type_annotation,
            })?;

            params.push(param);

            // Either `,` or `in`
            if self.did_match(TokenKind::Comma)? {
                continue;
            }

            if self.did_match(TokenKind::In)? {
                return Ok(params);
            }

            // Anything else → not a block-arg list

            rollback(self);
            return Ok(vec![]);
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn body(
        &mut self,
        context: BlockContext,
        consumes_left_brace: bool,
    ) -> Result<Body, ParserError> {
        self.skip_newlines();
        let tok = self.push_source_location();

        if consumes_left_brace {
            self.consume(TokenKind::LeftBrace)?;
        }

        self.skip_semicolons_and_newlines();
        let mut body = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            if context == BlockContext::Enum {
                // Special handling for multiple cases on one line
                if self.peek_is(TokenKind::Case) {
                    body.push(self.variant_decl(true)?);

                    while self.did_match(TokenKind::Comma)? {
                        body.push(self.variant_decl(false)?);
                    }

                    continue;
                }
            }

            if context == BlockContext::Protocol && self.peek_is(TokenKind::Associated) {
                body.push(self.associated_type()?);
                continue;
            }

            body.push(self.decl(context, false)?.try_into()?);

            self.skip_semicolons_and_newlines();
        }

        self.save_meta(tok, |id, span| Body {
            id,
            span,
            decls: body,
        })
    }

    fn peek_is_record_literal(&mut self) -> bool {
        // Record literals have the pattern: { identifier: expr, ... }
        // or { ...expr, ... }
        // Look for identifier followed by colon, or DotDotDot
        // Empty braces {} are always blocks, not records
        self.skip_newlines();

        match &self.current {
            Some(Token {
                kind: TokenKind::Identifier,
                ..
            }) => {
                matches!(
                    &self.next,
                    Some(Token {
                        kind: TokenKind::Colon,
                        ..
                    })
                )
            }
            Some(Token {
                kind: TokenKind::DotDotDot,
                ..
            }) => true,
            Some(Token {
                kind: TokenKind::RightBrace,
                ..
            }) => false, // Empty braces are blocks
            _ => false,
        }
    }

    fn record_literal_body(&mut self) -> Result<ExprKind, ParserError> {
        let mut fields: Vec<RecordField> = vec![];
        let mut spread = None;

        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_newlines();

            if self.peek_is(TokenKind::DotDotDot) {
                // Spread syntax: ...expr
                self.consume(TokenKind::DotDotDot)?;
                let expr = self.expr_with_precedence(Precedence::Assignment)?;

                spread = Some(Box::new(expr.try_into()?));

                // Spread must be the last thing in the record
                self.consume(TokenKind::RightBrace)?;
                break;
            } else {
                // Regular field: label: expr
                let field_tok = self.push_source_location();
                let (label, label_span) = self.identifier()?;
                self.consume(TokenKind::Colon)?;
                let value = self
                    .expr_with_precedence(Precedence::Assignment)?
                    .try_into()?;
                fields.push(self.save_meta(field_tok, |id, span| RecordField {
                    id,
                    span,
                    label: Name::Raw(label),
                    label_span,
                    value,
                })?);
            }

            // Handle comma
            if !self.peek_is(TokenKind::RightBrace) {
                self.consume(TokenKind::Comma)?;
            } else {
                self.consume(TokenKind::Comma).ok(); // Optional trailing comma
            }
            self.skip_newlines();
        }

        Ok(ExprKind::RecordLiteral { fields, spread })
    }

    fn associated_type(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Associated)?;
        let generic = self.generic()?;
        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::Associated { generic },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn generic(&mut self) -> Result<GenericDecl, ParserError> {
        let tok = self.push_source_location();
        let (name, name_span) = self.identifier()?;
        let generics = self.generics()?;

        let conformances = if self.did_match(TokenKind::Colon)? {
            self.conformances()?
        } else {
            vec![]
        };

        self.save_meta(tok, |id, span| GenericDecl {
            id,
            span,
            name: name.into(),
            name_span,
            generics,
            conformances,
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn generics(&mut self) -> Result<Vec<GenericDecl>, ParserError> {
        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? && !self.did_match(TokenKind::EOF)? {
                generics.push(self.generic()?);
                self.consume(TokenKind::Comma).ok();
            }
        }
        Ok(generics)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn parameters(&mut self) -> Result<Vec<Parameter>, ParserError> {
        let mut params: Vec<Parameter> = vec![];
        while let Ok((name, name_span)) = self.identifier() {
            let tok = self.push_source_location();
            let type_annotation = if self.did_match(TokenKind::Colon)? {
                Some(self.type_annotation()?)
            } else {
                None
            };

            let param = self.save_meta(tok, |id, span| Parameter {
                id,
                span,
                name: name.into(),
                name_span,
                type_annotation,
            })?;
            params.push(param);

            if self.did_match(TokenKind::Comma)? {
                continue;
            }

            break;
        }

        Ok(params)
    }

    fn effect_name(&mut self) -> Result<(String, Span), ParserError> {
        let Some(tok) = self.advance() else {
            return Err(ParserError::UnexpectedToken {
                expected: "effect name (must start with ')".into(),
                actual: format!("{:?}", self.current),
                token: self.current.clone(),
            });
        };

        if tok.kind != TokenKind::EffectName {
            return Err(ParserError::UnexpectedToken {
                expected: "effect name (must start with ')".into(),
                actual: format!("{:?}", tok),
                token: Some(tok),
            });
        }

        let effect_name = self.lexeme(&tok).to_string();
        let name_span = Span {
            file_id: self.file_id,
            start: tok.start,
            end: tok.end,
        };

        Ok((effect_name, name_span))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn identifier(&mut self) -> Result<(String, Span), ParserError> {
        self.skip_semicolons_and_newlines();
        if let Some(current) = self.current.clone()
            && current.kind == TokenKind::Identifier
        {
            let name = self.lexeme(&current).to_string();
            self.push_identifier(current.clone());
            self.advance();
            return Ok((
                name,
                Span {
                    start: current.start,
                    end: current.end,
                    file_id: self.file_id,
                },
            ));
        };

        Err(ParserError::ExpectedIdentifier(self.current.clone()))
    }

    // Try to get a specific token. If it's a match, return true.
    pub(super) fn did_match(&mut self, expected: TokenKind) -> Result<bool, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current.clone()
            && current.kind == expected
        {
            self.advance();
            return Ok(true);
        };

        Ok(false)
    }

    pub(super) fn peek_is(&self, expected: TokenKind) -> bool {
        if let Some(Token { kind: actual, .. }) = &self.current {
            *actual == expected
        } else {
            false
        }
    }

    fn push_context(&mut self, ctx: ParseContext) {
        self.context_stack.push(ctx);
    }

    fn pop_context(&mut self) {
        self.context_stack.pop();
    }

    fn current_context(&self) -> ParseContext {
        self.context_stack
            .last()
            .copied()
            .unwrap_or(ParseContext::TopLevel)
    }

    fn skip_newlines(&mut self) {
        while self.peek_is(TokenKind::Newline) {
            self.advance();
        }
    }

    fn skip_semicolons_and_newlines(&mut self) {
        while self.peek_is(TokenKind::Semicolon) || self.peek_is(TokenKind::Newline) {
            tracing::trace!("Skipping {:?}", self.current);
            self.advance();
        }
    }

    pub(crate) fn advance(&mut self) -> Option<Token> {
        self.previous = self.current.take();

        if let Some(prev) = &self.previous
            && prev.kind != TokenKind::Newline
        {
            self.previous_before_newline = Some(prev.clone());
        }

        tracing::trace!("advance {:?}", self.next);
        self.current = self.next.take();
        self.next = self.lexer.next().ok();
        self.previous.clone()
    }

    fn add_expr(&mut self, expr_kind: ExprKind, loc: LocToken) -> Result<Expr, ParserError> {
        self.save_meta(loc, |id, span| Expr {
            id,
            span,
            kind: expr_kind,
        })
    }

    pub(super) fn save_meta<T: std::fmt::Debug>(
        &mut self,
        _loc: LocToken,
        f: impl FnOnce(NodeID, Span) -> T,
    ) -> Result<T, ParserError> {
        let token = self
            .previous_before_newline
            .clone()
            .or_else(|| self.previous.clone())
            .ok_or(ParserError::UnbalancedLocationStack)?;
        let start = self
            .source_location_stack
            .pop()
            .ok_or(ParserError::UnbalancedLocationStack)?;

        let meta = NodeMeta {
            start: start.token.clone(),
            end: token.clone(),
            identifiers: start.identifiers,
        };

        let next_id = self.next_id();
        self.ast.meta.insert(next_id, meta);

        let node = f(
            next_id,
            Span {
                file_id: self.file_id,
                start: start.token.start,
                end: token.end,
            },
        );

        tracing::trace!("Parsed {:?}", node);

        Ok(node)
    }

    fn next_id(&mut self) -> NodeID {
        NodeID(self.file_id, self.ast.node_ids.next_id())
    }

    #[must_use]
    fn push_lhs_location(&mut self, lhs: NodeID) -> LocToken {
        let Some(meta) = self.ast.meta.get(&lhs) else {
            return LocToken;
        };
        let start = SourceLocationStart {
            token: meta.start.clone(),
            identifiers: vec![],
        };
        self.source_location_stack.push(start);
        LocToken
    }

    #[must_use]
    fn push_source_location(&mut self) -> LocToken {
        let Some(current) = &self.current else {
            return LocToken;
        };

        let start = SourceLocationStart {
            token: current.clone(),
            identifiers: vec![],
        };
        self.source_location_stack.push(start);
        LocToken
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn consume(&mut self, expected: TokenKind) -> Result<Token, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current.clone()
            && current.kind == expected
        {
            if current.kind == TokenKind::Identifier {
                self.push_identifier(current.clone());
            }

            self.advance();
            return Ok(current);
        };

        Err(ParserError::UnexpectedToken {
            expected: format!("{expected:?}"),
            actual: format!("{:?}", self.current),
            token: self.current.clone(),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn consume_any(&mut self, possible_tokens: Vec<TokenKind>) -> Result<Token, ParserError> {
        self.skip_semicolons_and_newlines();

        match self.current.clone() {
            Some(current) => {
                if current.kind == TokenKind::Identifier {
                    self.push_identifier(current.clone());
                }

                if possible_tokens.contains(&current.kind) {
                    self.advance();
                    Ok(current)
                } else {
                    Err(ParserError::UnexpectedToken {
                        expected: format!("{possible_tokens:?}"),
                        actual: format!("{current:?}"),
                        token: Some(current),
                    })
                }
            }
            None => Err(ParserError::UnexpectedEndOfInput(Some(
                possible_tokens
                    .iter()
                    .map(|v| v.as_str().to_string())
                    .collect::<Vec<String>>()
                    .join(", "),
            ))),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_identifier(&mut self, identifier: Token) {
        if let Some(loc) = self.source_location_stack.last_mut() {
            loc.identifiers.push(identifier);
        }
    }
}

fn parse_lexed<T: FromStr>(string: &str) -> T {
    string
        .parse::<T>()
        .unwrap_or_else(|_| unreachable!("lexer guarantees this is a number"))
}

/// Collects raw binder names from a parsed pattern (pre-name-resolution).
fn collect_pattern_binder_names(pattern: &Pattern) -> Vec<Name> {
    let mut names = vec![];
    collect_pattern_binder_names_inner(pattern, &mut names);
    names
}

fn collect_pattern_binder_names_inner(pattern: &Pattern, names: &mut Vec<Name>) {
    match &pattern.kind {
        PatternKind::Bind(name) => names.push(name.clone()),
        PatternKind::Tuple(patterns) => {
            for p in patterns {
                collect_pattern_binder_names_inner(p, names);
            }
        }
        PatternKind::Variant { fields, .. } => {
            for p in fields {
                collect_pattern_binder_names_inner(p, names);
            }
        }
        PatternKind::Or(patterns) => {
            // Take binders from the first alternative only
            if let Some(first) = patterns.first() {
                collect_pattern_binder_names_inner(first, names);
            }
        }
        PatternKind::Record { fields } => {
            for field in fields {
                match &field.kind {
                    RecordFieldPatternKind::Bind(name) => names.push(name.clone()),
                    RecordFieldPatternKind::Equals { value, .. } => {
                        collect_pattern_binder_names_inner(value, names);
                    }
                    RecordFieldPatternKind::Rest => {}
                }
            }
        }
        PatternKind::LiteralInt(_)
        | PatternKind::LiteralFloat(_)
        | PatternKind::LiteralTrue
        | PatternKind::LiteralFalse
        | PatternKind::Wildcard
        | PatternKind::Struct { .. } => {}
    }
}
