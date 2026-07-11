use std::str::FromStr;

use crate::ast::{AST, NewAST, Parsed};
use crate::diagnostic::{AnyDiagnostic, Diagnostic, Severity};
use crate::label::Label;
use crate::lexer::{Lexer, LexerError};
use crate::name::Name;
use crate::node::Node;
use crate::node_id::{FileID, NodeID};
use crate::node_kinds::block::Block;
use crate::node_kinds::body::Body;
use crate::node_kinds::call_arg::{ArgMode, CallArg};
use crate::node_kinds::decl::{
    Decl, DeclKind, Import, ImportPath, ImportedSymbol, ImportedSymbols, ReceiverMode, Visibility,
};
use crate::node_kinds::expr::{Expr, ExprKind};
use crate::node_kinds::func::{CaptureMode, CaptureSpec, EffectSet, Func};
use crate::node_kinds::func_signature::FuncSignature;
use crate::node_kinds::generic_decl::GenericDecl;
use crate::node_kinds::incomplete_expr::IncompleteExpr;
use crate::node_kinds::inline_ir_instruction::{
    InlineIRInstruction, InlineIRInstructionKind, Register, Value,
};
use crate::node_kinds::match_arm::MatchArm;
use crate::node_kinds::parameter::{ParamMode, Parameter};
use crate::node_kinds::pattern::{
    Pattern, PatternKind, RecordFieldPattern, RecordFieldPatternKind,
};
use crate::node_kinds::record_field::{RecordField, RecordFieldTypeAnnotation};
use crate::node_kinds::stmt::{Stmt, StmtKind};
use crate::node_kinds::type_annotation::{AnyAssocBinding, TypeAnnotation, TypeAnnotationKind};
use crate::node_kinds::where_clause::{WhereClause, WherePredicate, WherePredicateKind};
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
    lexer_error: Option<(LexerError, u32, u32)>,
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
            lexer_error: None,
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

            let root = match self.next_root(&current.kind) {
                Ok(root) => root,
                // Errors caused by a failed lex report the lex failure,
                // not the downstream missing-token symptom.
                Err(error) => return Err(self.take_lexer_error().unwrap_or(error)),
            };
            self.ast.roots.push(root);

            self.skip_semicolons_and_newlines();
        }

        // A lexer error can end the token stream between roots; without
        // this check the parse would silently truncate the file.
        if let Some(error) = self.take_lexer_error() {
            return Err(error);
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
                | Mut
                | Consuming
                | Case
                | Extend
                | Typealias
                | Effect
                | Use
                | Public
                | Linear
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
            Linear => {
                // The prefix form moved to a tick-suffix attribute.
                return Err(ParserError::UnexpectedToken {
                    expected: "`struct Name 'linear { ... }` (the `linear struct` prefix moved to a declaration attribute)".into(),
                    actual: "linear".into(),
                    token: Some(current),
                });
            }
            Static => {
                self.consume(TokenKind::Static)?;
                self.decl(context, true)?
            }
            Mut => {
                self.consume(TokenKind::Mut)?;
                self.method_decl_with_mode(context, is_static, ReceiverMode::Ref)?
                    .into()
            }
            Consuming => {
                self.consume(TokenKind::Consuming)?;
                self.method_decl_with_mode(context, is_static, ReceiverMode::Consuming)?
                    .into()
            }
            Use => self.import_decl()?.into(),
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
                | BlockContext::Protocol => self
                    .method_decl(context, is_static, ReceiverMode::None)?
                    .into(),
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
        let where_clause = self.where_clause()?;

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::Effect {
                name: effect_name.clone().into(),
                name_span,
                generics,
                where_clause,
                params,
                ret,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn import_decl(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Use)?;

        let path_start = self.current.as_ref().map(|token| token.start).unwrap_or(0);
        let path = self.module_path()?;
        let path_end = self
            .current
            .as_ref()
            .map(|token| token.start)
            .unwrap_or(path_start);
        let symbols = if self.peek_is(TokenKind::DoubleColon)
            && self
                .next
                .as_ref()
                .is_some_and(|token| token.kind == TokenKind::LeftBrace)
        {
            self.consume_double_colon()?;
            self.consume(TokenKind::LeftBrace)?;
            let mut imported = vec![];

            while !self.peek_is(TokenKind::RightBrace) {
                let (name, span) = self.identifier()?;
                let alias = if self.did_match(TokenKind::As)? {
                    Some(self.identifier()?.0)
                } else {
                    None
                };
                imported.push(ImportedSymbol { name, alias, span });

                if !self.did_match(TokenKind::Comma)? {
                    break;
                }
            }
            self.consume(TokenKind::RightBrace)?;
            ImportedSymbols::Named(imported)
        } else {
            ImportedSymbols::All
        };
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

    fn module_path(&mut self) -> Result<ImportPath, ParserError> {
        let (mut path, _) = self.identifier()?;
        while self.peek_is(TokenKind::DoubleColon)
            && !self
                .next
                .as_ref()
                .is_some_and(|token| token.kind == TokenKind::LeftBrace)
        {
            self.consume_double_colon()?;
            let (segment, _) = self.identifier()?;
            path.push_str("::");
            path.push_str(&segment);
        }

        if matches!(path.split("::").next(), Some("package" | "self" | "super")) {
            Ok(ImportPath::Local(path))
        } else {
            Ok(ImportPath::Package(path))
        }
    }

    fn did_match_double_colon(&mut self) -> Result<bool, ParserError> {
        self.did_match(TokenKind::DoubleColon)
    }

    fn consume_double_colon(&mut self) -> Result<(), ParserError> {
        self.consume(TokenKind::DoubleColon)?;
        Ok(())
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
    fn method_decl_with_mode(
        &mut self,
        context: BlockContext,
        is_static: bool,
        receiver_mode: ReceiverMode,
    ) -> Result<Decl, ParserError> {
        match context {
            BlockContext::Extend
            | BlockContext::Struct
            | BlockContext::Enum
            | BlockContext::Protocol => {}
            _ => {
                return Err(ParserError::UnexpectedToken {
                    expected: "method declaration".into(),
                    actual: format!("{:?}", self.current),
                    token: self.current.clone(),
                });
            }
        }
        if is_static {
            return Err(ParserError::UnexpectedToken {
                expected: "instance method receiver modifier".into(),
                actual: "static method".into(),
                token: self.current.clone(),
            });
        }
        self.method_decl(context, is_static, receiver_mode)
    }

    fn method_decl(
        &mut self,
        context: BlockContext,
        is_static: bool,
        receiver_mode: ReceiverMode,
    ) -> Result<Decl, ParserError> {
        let func_decl = self.func_decl(context, true)?;
        match func_decl.kind {
            DeclKind::Func(func) => Ok(Decl {
                id: func.id,
                span: func_decl.span,
                visibility: func_decl.visibility,
                kind: DeclKind::Method {
                    func: Box::new(self.reject_explicit_self_param(func, is_static)?),
                    is_static,
                    receiver_mode,
                },
            }),
            DeclKind::FuncSignature(func_sig) => Ok(Decl {
                id: func_decl.id,
                span: func_decl.span,
                visibility: func_decl.visibility,
                kind: DeclKind::MethodRequirement {
                    signature: self.reject_explicit_self_signature(func_sig, is_static)?,
                    receiver_mode,
                },
            }),
            _ => unreachable!(),
        }
    }

    fn reject_explicit_self_param(&self, func: Func, is_static: bool) -> Result<Func, ParserError> {
        self.reject_explicit_self_params(&func.params, is_static)?;
        Ok(func)
    }

    fn reject_explicit_self_signature(
        &self,
        sig: FuncSignature,
        is_static: bool,
    ) -> Result<FuncSignature, ParserError> {
        self.reject_explicit_self_params(&sig.params, is_static)?;
        Ok(sig)
    }

    fn reject_explicit_self_params(
        &self,
        params: &[Parameter],
        is_static: bool,
    ) -> Result<(), ParserError> {
        if !is_static && first_param_is_self(params) {
            return Err(ParserError::ExplicitSelfParameterNotAllowed);
        }
        Ok(())
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
        let generics = self.generics()?;
        let (payloads, payload_labels) = if self.did_match(TokenKind::LeftParen)? {
            self.variant_payloads()?
        } else {
            (vec![], vec![])
        };
        let result = if self.did_match(TokenKind::Arrow)? {
            Some(self.type_annotation()?)
        } else {
            None
        };

        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::EnumVariant {
                name: name.into(),
                name_span,
                generics,
                payloads,
                payload_labels,
                result,
            },
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
        let row_generics = if context == BlockContext::Extend && self.peek_is(TokenKind::Less) {
            self.generics()?
        } else {
            vec![]
        };
        let (name, name_span) = self.identifier()?;
        let generics = self.generics()?;

        // Tick-suffix declaration attributes: `struct Node 'heap { ... }`,
        // `struct Token 'linear { ... }`. One extensible modifier position.
        let mut linear = false;
        let mut heap = false;
        while self.peek_is(TokenKind::EffectName) {
            let Some(tok) = self.advance() else { break };
            let attribute = self.lexeme(&tok).to_string();
            match attribute.as_str() {
                "linear" => linear = true,
                "heap" if context == BlockContext::Struct => heap = true,
                "heap" => {
                    return Err(ParserError::UnexpectedToken {
                        expected: "'heap applies to struct declarations only".into(),
                        actual: format!("{context:?}"),
                        token: Some(tok),
                    });
                }
                other => {
                    return Err(ParserError::UnexpectedToken {
                        expected: "a declaration attribute ('heap or 'linear)".into(),
                        actual: format!("'{other}"),
                        token: Some(tok),
                    });
                }
            }
        }
        if linear && heap {
            return Err(ParserError::UnexpectedToken {
                expected: "at most one of 'heap and 'linear (aliased references cannot be consumed exactly once)".into(),
                actual: "'heap 'linear".into(),
                token: self.current.clone(),
            });
        }

        let conformance_colon = self.current.clone();
        let conformances = if self.did_match(TokenKind::Colon)? {
            if context.allows_conformances() {
                self.conformances()?
            } else {
                return Err(ParserError::ConformanceListNotAllowed {
                    context,
                    token: conformance_colon,
                });
            }
        } else {
            vec![]
        };

        let where_clause = self.where_clause()?;

        let body = self.body_block(context)?;

        let kind = match context {
            BlockContext::Enum => DeclKind::Enum {
                name: name.into(),
                name_span,
                generics,
                where_clause,
                body,
                linear,
            },
            BlockContext::Struct => DeclKind::Struct {
                name: name.into(),
                name_span,
                generics,
                where_clause,
                body,
                linear,
                heap,
            },
            BlockContext::Extend => DeclKind::Extend {
                name: name.into(),
                name_span,
                row_generics,
                conformances,
                generics,
                where_clause,
                body,
            },
            BlockContext::Protocol => DeclKind::Protocol {
                name: name.into(),
                name_span,
                conformances,
                generics,
                where_clause,
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
            return self.desugar_let_else(tok, lhs, type_annotation, rhs, Some(else_body));
        }
        // An or-pattern let takes the same desugaring road (a single-arm
        // match, no else): alternatives bind the same names, and a miss
        // is the match machinery's miss.
        if pattern_contains_or(&lhs) {
            return self.desugar_let_else(tok, lhs, type_annotation, rhs, None);
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
        let captures = self.capture_specs()?;

        self.consume(TokenKind::LeftParen)?;
        let params = self.parameters()?;
        self.consume(TokenKind::RightParen)?;

        let effects = self.effect_set()?;

        let ret = if self.consume(TokenKind::Arrow).is_ok() {
            Some(self.type_annotation()?)
        } else {
            None
        };

        let where_clause = self.where_clause()?;

        if context == BlockContext::Protocol && !self.peek_is(TokenKind::LeftBrace) {
            let ret = ret.map(Box::new);

            return self.save_meta(tok, |id, span| {
                FuncOrFuncSignature::FuncSignature(FuncSignature {
                    id,
                    span,
                    name: name.into(),
                    generics,
                    where_clause,
                    params,
                    effects: effects.clone(),
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
                effects,
                generics,
                captures,
                where_clause,
                params,
                body,
                ret,
                attributes: vec![],
            })
        })
    }

    fn effect_set(&mut self) -> Result<EffectSet, ParserError> {
        let mut names = vec![];
        let mut spans = vec![];
        let mut is_open = false;
        if self.peek_is(TokenKind::SingleQuote) {
            self.advance();
            // It's an effect list.
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

        Ok(EffectSet {
            names,
            spans,
            is_open,
        })
    }

    fn capture_specs(&mut self) -> Result<Vec<CaptureSpec>, ParserError> {
        let mut captures = vec![];
        if !self.did_match(TokenKind::LeftBracket)? {
            return Ok(captures);
        }

        while !self.did_match(TokenKind::RightBracket)? && !self.did_match(TokenKind::EOF)? {
            let mode = if self.did_match(TokenKind::Amp)? {
                if self.did_match(TokenKind::Mut)? {
                    CaptureMode::BorrowMut
                } else {
                    CaptureMode::BorrowShared
                }
            } else if self.did_match(TokenKind::Consuming)? {
                CaptureMode::Move
            } else if self.peek_identifier("copy") {
                self.advance();
                CaptureMode::Copy
            } else {
                CaptureMode::Copy
            };

            let (name, span) = self.identifier()?;
            captures.push(CaptureSpec {
                mode,
                name: name.into(),
                span,
            });
            if self.did_match(TokenKind::RightBracket)? {
                return Ok(captures);
            }
            self.consume(TokenKind::Comma)?;
        }

        Ok(captures)
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
        let alt = if self.did_match(TokenKind::Else)? {
            self.block(BlockContext::If, true)?
        } else {
            self.record_diagnostic(self.expected_token_error(TokenKind::Else));
            self.empty_recovered_block()
        };

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
        type_annotation: Option<TypeAnnotation>,
        rhs: Option<Expr>,
        else_body: Option<Block>,
    ) -> Result<Decl, ParserError> {
        let scrutinee = rhs.unwrap_or(Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Tuple(vec![]),
        });
        // A `let pattern: T = …` annotation pins the scrutinee.
        let scrutinee = match type_annotation {
            Some(annotation) => Expr {
                id: self.next_id(),
                span: Span::SYNTHESIZED,
                kind: ExprKind::As(Box::new(scrutinee), annotation),
            },
            None => scrutinee,
        };

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

        // With an else, a miss runs it (let-else); without one (or-pattern
        // lets), a miss is the match machinery's miss.
        let mut arms = vec![pattern_arm];
        if let Some(else_body) = else_body {
            let wildcard_pat_id = self.next_id();
            arms.push(MatchArm {
                id: self.next_id(),
                pattern: Pattern {
                    id: wildcard_pat_id,
                    kind: PatternKind::Wildcard,
                    span: Span::SYNTHESIZED,
                },
                body: else_body,
                span: Span::SYNTHESIZED,
            });
        }

        let match_expr = Expr {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            kind: ExprKind::Match(Box::new(scrutinee), arms),
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
        let mut pattern = self.parse_pattern()?;
        self.consume(TokenKind::In)?;
        self.push_context(ParseContext::For);
        let source_mode = self.arg_mode();
        let iterable = self.expr()?.as_expr();
        self.pop_context();
        let mut body = self.block(BlockContext::Loop, true)?;
        if let Some(arg) = body.args.first() {
            pattern = Pattern {
                id: arg.id,
                span: arg.name_span,
                kind: PatternKind::Bind(arg.name.clone()),
            };
            body.args.clear();
        }

        self.save_meta(tok, |id, span| Stmt {
            id,
            span,
            kind: StmtKind::For {
                iterable: Box::new(iterable),
                source_mode: source_mode.map(|(mode, _)| mode),
                pattern,
                body,
                hidden_source: format!("__for_src_{}", id.1).into(),
                hidden_iter: format!("__for_iter_{}", id.1).into(),
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
                "cmp" => {
                    let ty = self.type_annotation()?;
                    let lhs = self.ir_value()?;
                    let op = self
                        .consume_any(vec![
                            TokenKind::Less,
                            TokenKind::BangEquals,
                            TokenKind::EqualsEquals,
                            TokenKind::LessEquals,
                            TokenKind::Greater,
                            TokenKind::GreaterEquals,
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
                "is_unique" => {
                    let ptr = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::IsUnique { dest, ptr },
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
                "btoi" => {
                    let val = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::ByteToInt { dest, val },
                    })
                }
                _ => {
                    return Err(ParserError::UnexpectedToken {
                        expected: "supported @_ir instr".into(),
                        actual: instr,
                        token: self.previous.clone(),
                    });
                }
            }
        } else {
            let (instr, instr_span) = self.identifier()?;
            match instr.as_str() {
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
                "free" => {
                    let ptr = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Free { ptr },
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
                "swap" => {
                    let ty = self.type_annotation()?;
                    let a = self.ir_value()?;
                    let b = self.ir_value()?;
                    self.save_meta(tok, |id, span| InlineIRInstruction {
                        id,
                        span,
                        binds,
                        instr_name_span: instr_span,
                        kind: InlineIRInstructionKind::Swap { ty, a, b },
                    })
                }
                _ => {
                    return Err(ParserError::UnexpectedToken {
                        expected: "supported @_ir instr".into(),
                        actual: instr,
                        token: self.previous.clone(),
                    });
                }
            }
        }?;

        self.consume(TokenKind::RightBrace)?;

        Ok(Node::Expr(Expr {
            id: ir_instr.id,
            span: ir_instr.span,
            kind: ExprKind::InlineIR(ir_instr),
        }))
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
        loop {
            self.skip_newlines();
            if self.did_match(TokenKind::RightBracket)? {
                break;
            }
            if self.at_delimiter_recovery_boundary() {
                self.record_diagnostic(self.expected_token_error(TokenKind::RightBracket));
                break;
            }
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

        if let Err(err) = self.consume(TokenKind::LeftBrace) {
            self.record_diagnostic(err);
            return self.save_meta(tok, |id, span| {
                Node::Expr(Expr {
                    id,
                    span,
                    kind: ExprKind::Match(Box::new(scrutinee.as_expr()), vec![]),
                })
            });
        }

        let mut arms = vec![];
        loop {
            self.skip_newlines();
            if self.did_match(TokenKind::RightBrace)? {
                break;
            }
            if self.peek_is(TokenKind::EOF) {
                self.record_diagnostic(self.expected_token_error(TokenKind::RightBrace));
                break;
            }
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
                    let (fields, field_labels) = self.pattern_fields()?;
                    PatternKind::Variant {
                        enum_name: Some(name.into()),
                        variant_name: member_name.to_string(),
                        variant_name_span: member_name_span,
                        fields,
                        field_labels,
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
                let (fields, field_labels) = self.pattern_fields()?;

                PatternKind::Variant {
                    enum_name: None,
                    variant_name: member_name.to_string(),
                    variant_name_span: member_name_span,
                    fields,
                    field_labels,
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

    fn pattern_fields(&mut self) -> Result<(Vec<Pattern>, Vec<Option<Name>>), ParserError> {
        let mut fields = vec![];
        let mut labels = vec![];
        if self.did_match(TokenKind::LeftParen)? {
            while !self.did_match(TokenKind::RightParen)? {
                if self.peek_is(TokenKind::Identifier)
                    && matches!(
                        self.next.as_ref().map(|token| token.kind),
                        Some(TokenKind::Colon)
                    )
                {
                    let (label, _) = self.identifier()?;
                    self.consume(TokenKind::Colon)?;
                    fields.push(self.parse_pattern()?);
                    labels.push(Some(label.into()));
                } else {
                    fields.push(self.parse_pattern()?);
                    labels.push(None);
                }
                self.consume(TokenKind::Comma).ok();
            }
        };
        Ok((fields, labels))
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
            TokenKind::CharacterLiteral => {
                // Strip surrounding quotes but keep escape sequences intact
                let inner = &lexeme[1..lexeme.len() - 1];
                self.add_expr(ExprKind::LiteralCharacter(inner.to_string()), tok)
            }
            _ => unreachable!(),
        };

        Ok(expr?.into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn variable(&mut self, can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let (mut name, _span) = self.identifier()?;
        while self.did_match_double_colon()? {
            let (segment, _) = self.identifier()?;
            name.push_str("::");
            name.push_str(&segment);
        }
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
    pub(crate) fn bound_var(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let current = self.advance().expect("peeked bound var");
        let name = format!("${}", self.lexeme(&current));
        Ok(self
            .add_expr(ExprKind::Variable(Name::Raw(name)), tok)?
            .into())
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

        if self.at_delimiter_recovery_boundary() {
            self.record_diagnostic(self.expected_token_error(TokenKind::RightParen));
            return Ok(self.add_expr(ExprKind::Tuple(vec![child]), tok)?.into());
        }

        self.consume(TokenKind::Comma)?;

        let mut items = vec![child];
        let mut recovered_closer = false;
        loop {
            self.skip_newlines();
            if self.did_match(TokenKind::RightParen)? {
                return Ok(self.add_expr(ExprKind::Tuple(items), tok)?.into());
            }
            if self.at_delimiter_recovery_boundary() {
                self.record_diagnostic(self.expected_token_error(TokenKind::RightParen));
                recovered_closer = true;
                break;
            }
            items.push(self.expr_with_precedence(Precedence::Assignment)?.as_expr());
            if !self.did_match(TokenKind::Comma)? {
                break;
            }
        }

        if !recovered_closer {
            self.consume_or_recover_closer(TokenKind::RightParen)?;
        }

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
        } else if self.at_delimiter_recovery_boundary() {
            self.record_diagnostic(self.expected_token_error(TokenKind::RightParen));
            vec![]
        } else {
            let args = self.arguments()?;
            self.consume_or_recover_closer_after_newline(TokenKind::RightParen)?;
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

        // Call parens may be omitted when the first argument starts with a
        // string literal: `foo "sup"` and `foo "sup" { ... }`.
        if self.peek_is(TokenKind::StringLiteral) && !self.previous_token_was_newline() {
            return Ok(Some(
                self.call_with_leading_string_arg(can_assign, callee.clone())?,
            ));
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
        let trailing_block = self.closure_block(BlockContext::None, true)?;

        self.add_expr(
            ExprKind::Call {
                callee: Box::new(callee),
                type_args: vec![],
                args: vec![],
                trailing_block: Some(trailing_block),
                desugared_operator: None,
            },
            tok,
        )
    }

    fn call_with_leading_string_arg(
        &mut self,
        can_assign: bool,
        callee: Expr,
    ) -> Result<Expr, ParserError> {
        let tok = self.push_lhs_location(callee.id);
        let mut args = vec![self.argument(0)?];
        let mut i = 1;
        while self.did_match(TokenKind::Comma)? {
            args.push(self.argument(i)?);
            i += 1;
        }

        let trailing_block = if self.current_context().allows_trailing_blocks()
            && self.peek_is(TokenKind::LeftBrace)
        {
            Some(self.closure_block(BlockContext::None, true)?)
        } else {
            None
        };

        let call = self.add_expr(
            ExprKind::Call {
                callee: Box::new(callee),
                type_args: vec![],
                args,
                trailing_block,
                desugared_operator: None,
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

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(crate) fn call(
        &mut self,
        can_assign: bool,
        type_args: Vec<TypeAnnotation>,
        callee: Expr,
    ) -> Result<Expr, ParserError> {
        let tok = self.push_lhs_location(callee.id);
        self.skip_newlines();

        let mut args = if self.did_match(TokenKind::RightParen)? {
            vec![]
        } else if self.at_delimiter_recovery_boundary() {
            self.record_diagnostic(self.expected_token_error(TokenKind::RightParen));
            vec![]
        } else {
            let args = self.arguments()?;
            self.consume_or_recover_closer_after_newline(TokenKind::RightParen)?;
            args
        };

        // Check for trailing block after the closing paren.
        // We only allow trailing blocks at the top level context, not inside
        // match/if/loop/for scrutinees where { starts the body.
        let trailing_block = if self.current_context().allows_trailing_blocks()
            && self.peek_is(TokenKind::LeftBrace)
        {
            Some(self.closure_block(BlockContext::None, true)?)
        } else {
            self.take_parenthesized_trailing_block_arg(&mut args)
        };

        let call = self.add_expr(
            ExprKind::Call {
                callee: Box::new(callee),
                type_args,
                args,
                trailing_block,
                desugared_operator: None,
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

    /// An optional call-site ownership marker on an argument (ADR 0018):
    /// `consume x`, `copy x`, `borrow x`, or `mut x`. `mut` is a hard
    /// keyword; the rest are contextual and only read as markers when a
    /// variable-rooted expression follows.
    fn arg_mode(&mut self) -> Option<(ArgMode, Span)> {
        if self.peek_is(TokenKind::Mut) {
            let tok = self.advance().expect("peeked Mut");
            return Some((ArgMode::Mut, self.token_span(&tok)));
        }
        let mode = if self.peek_identifier("consume") {
            ArgMode::Consume
        } else if self.peek_identifier("copy") {
            ArgMode::Copy
        } else if self.peek_identifier("borrow") {
            ArgMode::Borrow
        } else {
            return None;
        };
        if !matches!(
            self.next.as_ref().map(|token| &token.kind),
            Some(TokenKind::Identifier)
        ) {
            return None;
        }
        let tok = self.advance().expect("peeked marker");
        Some((mode, self.token_span(&tok)))
    }

    fn arguments(&mut self) -> Result<Vec<CallArg>, ParserError> {
        let mut args: Vec<CallArg> = vec![];
        let mut i = 0;
        while {
            // Arguments may sit one per line (the formatter wraps long
            // calls that way); newlines inside an argument list are
            // insignificant, and a trailing comma before `)` is fine.
            self.skip_newlines();
            if self.peek_is(TokenKind::RightParen) || self.at_delimiter_recovery_boundary() {
                return Ok(args);
            }
            args.push(self.argument(i)?);

            i += 1;
            let more = self.did_match(TokenKind::Comma)?;
            if !more {
                self.skip_newlines();
            }
            more
        } {}

        Ok(args)
    }

    fn argument(&mut self, positional_index: usize) -> Result<CallArg, ParserError> {
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
            let mode = self.arg_mode();
            let value = self.expr_with_precedence(Precedence::Assignment)?;
            self.save_meta(tok, |id, span| CallArg {
                id,
                span,
                label: label.into(),
                label_span,
                value: value.as_expr(),
                mode: mode.map(|(mode, _)| mode),
                mode_span: mode.map(|(_, span)| span),
            })
        } else {
            let mode = self.arg_mode();
            let value = self.expr_with_precedence(Precedence::Assignment)?;
            self.save_meta(tok, |id, span| CallArg {
                id,
                span,
                label: Label::Positional(positional_index),
                label_span: span,
                value: value.as_expr(),
                mode: mode.map(|(mode, _)| mode),
                mode_span: mode.map(|(_, span)| span),
            })
        }
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

    /// A parameter of a function TYPE annotation (ADR 0018): an optional
    /// ownership-mode prefix ahead of the type. The caller wraps once it
    /// knows the parenthesized list is a function type and not a tuple.
    fn func_type_param(
        &mut self,
        saw_param_mode: &mut bool,
    ) -> Result<(Option<ParamMode>, TypeAnnotation), ParserError> {
        self.skip_semicolons_and_newlines();

        if self.peek_is(TokenKind::Mut) {
            self.consume(TokenKind::Mut)?;
            *saw_param_mode = true;
            return Ok((Some(ParamMode::Mut), self.type_annotation()?));
        }

        if self.peek_identifier("consume") && self.next_starts_type_annotation() {
            self.advance();
            let mode = if self.did_match(TokenKind::Mut)? {
                ParamMode::ConsumeMut
            } else {
                ParamMode::Consume
            };
            *saw_param_mode = true;
            return Ok((Some(mode), self.type_annotation()?));
        }

        Ok((None, self.type_annotation()?))
    }

    /// Resolve a function-type parameter's mode onto the annotation
    /// (ADR 0018, borrow-by-default): unadorned parameters become shared
    /// borrows, `mut` becomes an exclusive borrow, `consume` (and
    /// `consume mut`, which only differs callee-locally) stays the bare
    /// owned type. Explicit `&`/`&mut` spellings are left as written.
    fn apply_func_type_param_mode(
        &mut self,
        mode: Option<ParamMode>,
        annotation: TypeAnnotation,
    ) -> TypeAnnotation {
        let mutable = match mode {
            Some(ParamMode::Consume | ParamMode::ConsumeMut) => return annotation,
            Some(ParamMode::Mut) => true,
            None | Some(ParamMode::Borrow) => false,
        };
        if matches!(annotation.kind, TypeAnnotationKind::Borrow { .. }) {
            return annotation;
        }
        TypeAnnotation {
            id: self.next_id(),
            span: annotation.span,
            kind: TypeAnnotationKind::Borrow {
                mutable,
                inner: Box::new(annotation),
            },
        }
    }

    fn next_starts_type_annotation(&self) -> bool {
        matches!(
            self.next.as_ref().map(|token| &token.kind),
            Some(
                TokenKind::Identifier
                    | TokenKind::Mut
                    | TokenKind::Amp
                    | TokenKind::Star
                    | TokenKind::LeftParen
                    | TokenKind::LeftBrace
                    | TokenKind::LeftBracket
                    | TokenKind::Any
            )
        )
    }

    fn type_annotation_base(&mut self) -> Result<TypeAnnotation, ParserError> {
        let tok = self.push_source_location();

        if self.did_match(TokenKind::Amp)? {
            let mutable = self.did_match(TokenKind::Mut)?;
            let inner = self.type_annotation()?;
            return self.save_meta(tok, |id, span| TypeAnnotation {
                id,
                span,
                kind: TypeAnnotationKind::Borrow {
                    mutable,
                    inner: Box::new(inner),
                },
            });
        }

        if self.did_match(TokenKind::Star)? {
            let inner = self.type_annotation()?;
            return self.save_meta(tok, |id, span| TypeAnnotation {
                id,
                span,
                kind: TypeAnnotationKind::Unique {
                    inner: Box::new(inner),
                },
            });
        }

        if self.did_match(TokenKind::LeftParen)? {
            // it's a func type or tuple repr
            let mut sig_args = vec![];
            let mut saw_param_mode = false;
            while !self.did_match(TokenKind::RightParen)? {
                sig_args.push(self.func_type_param(&mut saw_param_mode)?);
                self.consume(TokenKind::Comma).ok();
            }
            let has_effects = self.peek_is(TokenKind::SingleQuote)
                || matches!(
                    self.current.as_ref().map(|t| &t.kind),
                    Some(TokenKind::EffectName)
                );
            let effects = self.effect_set()?;
            if self.did_match(TokenKind::Arrow)? {
                let ret = self.type_annotation()?;
                let params = sig_args
                    .into_iter()
                    .map(|(mode, annotation)| self.apply_func_type_param_mode(mode, annotation))
                    .collect();
                return self.save_meta(tok, |id, span| TypeAnnotation {
                    id,
                    span,
                    kind: TypeAnnotationKind::Func {
                        params,
                        effects,
                        returns: Box::new(ret),
                    },
                });
            } else {
                if has_effects || saw_param_mode {
                    return Err(ParserError::UnexpectedToken {
                        expected: "->".to_string(),
                        actual: format!("{:?}", self.current),
                        token: self.current.clone(),
                    });
                }
                let items = sig_args
                    .into_iter()
                    .map(|(_, annotation)| annotation)
                    .collect();
                return self.save_meta(tok, |id, span| TypeAnnotation {
                    id,
                    span,
                    kind: TypeAnnotationKind::Tuple(items),
                });
            }
        }

        if self.did_match(TokenKind::Any)? {
            return self.any_type_annotation(tok);
        }

        if self.did_match(TokenKind::LeftBracket)? {
            let element = self.type_annotation()?;
            self.consume(TokenKind::RightBracket)?;
            let base = self.save_meta(tok, |id, span| TypeAnnotation {
                id,
                span,
                kind: TypeAnnotationKind::Nominal {
                    name: "Array".into(),
                    // Array is implied by the brackets, so it has no source name.
                    name_span: Span::SYNTHESIZED,
                    generics: vec![element],
                },
            })?;
            return self.nominal_type_path(base);
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
        let (mut name, name_span) = self.identifier()?;
        while self.did_match_double_colon()? {
            let (segment, _) = self.identifier()?;
            name.push_str("::");
            name.push_str(&segment);
        }
        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                let generic = self.type_annotation()?;
                generics.push(generic);
                self.consume(TokenKind::Comma).ok();
            }
        }

        let base = self.save_meta(tok, |id, span| TypeAnnotation {
            id,
            span,
            kind: TypeAnnotationKind::Nominal {
                name: name.into(),
                name_span,
                generics,
            },
        })?;

        self.nominal_type_path(base)
    }

    fn nominal_type_path(
        &mut self,
        mut base: TypeAnnotation,
    ) -> Result<TypeAnnotation, ParserError> {
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

            return Ok(base);
        }
    }

    fn any_type_annotation(&mut self, tok: LocToken) -> Result<TypeAnnotation, ParserError> {
        let protocol = self.any_protocol_head()?;
        let mut assoc_bindings = vec![];

        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                let binding_tok = self.push_source_location();
                let (name, name_span) = self.identifier()?;
                self.consume(TokenKind::Equals)?;
                let value = self.type_annotation()?;
                assoc_bindings.push(self.save_meta(binding_tok, |id, span| AnyAssocBinding {
                    id,
                    span,
                    name: name.into(),
                    name_span,
                    value,
                })?);
                self.consume(TokenKind::Comma).ok();
            }
        }

        self.save_meta(tok, |id, span| TypeAnnotation {
            id,
            span,
            kind: TypeAnnotationKind::Any {
                protocol: Box::new(protocol),
                assoc_bindings,
            },
        })
    }

    fn any_protocol_head(&mut self) -> Result<TypeAnnotation, ParserError> {
        let tok = self.push_source_location();
        let (name, name_span) = self.identifier()?;
        let mut base = self.save_meta(tok, |id, span| TypeAnnotation {
            id,
            span,
            kind: TypeAnnotationKind::Nominal {
                name: name.into(),
                name_span,
                generics: vec![],
            },
        })?;

        while self.did_match(TokenKind::Dot)? {
            let tok = self.push_source_location();
            let (member_name, member_span) = self.identifier()?;
            base = self.save_meta(tok, |id, span| TypeAnnotation {
                id,
                span,
                kind: TypeAnnotationKind::NominalPath {
                    base: Box::new(base),
                    member: member_name.into(),
                    member_span,
                    member_generics: vec![],
                },
            })?;
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
    fn where_clause(&mut self) -> Result<Option<WhereClause>, ParserError> {
        self.skip_newlines();
        let Some(current) = self.current.clone() else {
            return Ok(None);
        };
        if current.kind != TokenKind::Identifier || self.lexeme(&current) != "where" {
            return Ok(None);
        }

        let tok = self.push_source_location();
        self.advance();
        let mut predicates = vec![];
        loop {
            predicates.push(self.where_predicate()?);
            if !self.did_match(TokenKind::AmpAmp)? {
                break;
            }
        }

        self.save_meta(tok, |id, span| {
            Some(WhereClause {
                id,
                span,
                predicates,
            })
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn where_predicate(&mut self) -> Result<WherePredicate, ParserError> {
        let tok = self.push_source_location();
        let lhs = self.type_annotation()?;
        let kind = if self.did_match(TokenKind::EqualsEquals)? {
            WherePredicateKind::TypeEq {
                lhs,
                rhs: self.type_annotation()?,
            }
        } else {
            self.consume(TokenKind::Colon)?;
            let mut protocols = vec![self.type_annotation()?];
            while self.did_match(TokenKind::Amp)? {
                protocols.push(self.type_annotation()?);
            }
            WherePredicateKind::Conforms { ty: lhs, protocols }
        };

        self.save_meta(tok, |id, span| WherePredicate { id, span, kind })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn variant_payloads(
        &mut self,
    ) -> Result<(Vec<TypeAnnotation>, Vec<Option<Name>>), ParserError> {
        let mut payloads = vec![];
        let mut labels = vec![];

        while !self.did_match(TokenKind::RightParen)? {
            if self.peek_is(TokenKind::Identifier)
                && matches!(
                    self.next.as_ref().map(|token| token.kind),
                    Some(TokenKind::Colon)
                )
            {
                let (label, _) = self.identifier()?;
                self.consume(TokenKind::Colon)?;
                payloads.push(self.type_annotation()?);
                labels.push(Some(label.into()));
            } else {
                payloads.push(self.type_annotation()?);
                labels.push(None);
            }
            self.consume(TokenKind::Comma).ok();
        }

        Ok((payloads, labels))
    }

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

    fn closure_block(
        &mut self,
        context: BlockContext,
        consumes_left_brace: bool,
    ) -> Result<Block, ParserError> {
        let block = self.block(context, consumes_left_brace)?;
        Ok(self.prepare_closure_block(block))
    }

    fn prepare_closure_block(&mut self, mut block: Block) -> Block {
        if block.args.is_empty()
            && let Some(max_index) = Self::max_positional_block_arg(&block)
        {
            block.args = (0..=max_index)
                .map(|index| Parameter {
                    id: self.next_id(),
                    span: Span::SYNTHESIZED,
                    name: Name::Raw(format!("${index}")),
                    name_span: Span::SYNTHESIZED,
                    type_annotation: None,
                    mode: None,
                    mode_span: None,
                })
                .collect();
        }
        block
    }

    fn take_parenthesized_trailing_block_arg(&mut self, args: &mut Vec<CallArg>) -> Option<Block> {
        let arg = args.pop()?;
        if !matches!(arg.label, Label::Positional(_)) || arg.mode.is_some() {
            args.push(arg);
            return None;
        }
        match arg.value.kind {
            ExprKind::Block(block) => Some(self.prepare_closure_block(block)),
            _ => {
                args.push(arg);
                None
            }
        }
    }

    fn max_positional_block_arg(block: &Block) -> Option<usize> {
        block
            .body
            .iter()
            .filter_map(Self::max_positional_block_arg_in_node)
            .max()
    }

    fn max_positional_block_arg_in_node(node: &Node) -> Option<usize> {
        match node {
            Node::Stmt(stmt) => Self::max_positional_block_arg_in_stmt(stmt),
            Node::Expr(expr) => Self::max_positional_block_arg_in_expr(expr),
            Node::Decl(decl) => Self::max_positional_block_arg_in_decl(decl),
            _ => None,
        }
    }

    fn max_positional_block_arg_in_stmt(stmt: &Stmt) -> Option<usize> {
        match &stmt.kind {
            StmtKind::Expr(expr)
            | StmtKind::Return(Some(expr))
            | StmtKind::Continue(Some(expr)) => Self::max_positional_block_arg_in_expr(expr),
            StmtKind::If(condition, then_block, else_block) => [
                Self::max_positional_block_arg_in_expr(condition),
                Self::max_positional_block_arg(then_block),
                else_block.as_ref().and_then(Self::max_positional_block_arg),
            ]
            .into_iter()
            .flatten()
            .max(),
            StmtKind::Assignment(lhs, rhs) => [
                Self::max_positional_block_arg_in_expr(lhs),
                Self::max_positional_block_arg_in_expr(rhs),
            ]
            .into_iter()
            .flatten()
            .max(),
            StmtKind::Loop(condition, body) => [
                condition
                    .as_ref()
                    .and_then(Self::max_positional_block_arg_in_expr),
                Self::max_positional_block_arg(body),
            ]
            .into_iter()
            .flatten()
            .max(),
            StmtKind::For { iterable, body, .. } => [
                Self::max_positional_block_arg_in_expr(iterable),
                Self::max_positional_block_arg(body),
            ]
            .into_iter()
            .flatten()
            .max(),
            StmtKind::Handling { body, .. } => Self::max_positional_block_arg(body),
            StmtKind::Return(None) | StmtKind::Continue(None) | StmtKind::Break => None,
        }
    }

    fn max_positional_block_arg_in_decl(decl: &Decl) -> Option<usize> {
        match &decl.kind {
            DeclKind::Let { rhs, .. } => rhs
                .as_ref()
                .and_then(Self::max_positional_block_arg_in_expr),
            DeclKind::Property { default_value, .. } => default_value
                .as_ref()
                .and_then(Self::max_positional_block_arg_in_expr),
            _ => None,
        }
    }

    fn max_positional_block_arg_in_expr(expr: &Expr) -> Option<usize> {
        match &expr.kind {
            ExprKind::Variable(name) => {
                let name = name.name_str();
                name.strip_prefix('$')
                    .and_then(|index| index.parse::<usize>().ok())
            }
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => items
                .iter()
                .filter_map(Self::max_positional_block_arg_in_expr)
                .max(),
            ExprKind::Unary(_, inner) | ExprKind::As(inner, _) => {
                Self::max_positional_block_arg_in_expr(inner)
            }
            ExprKind::Binary(lhs, _, rhs) => [
                Self::max_positional_block_arg_in_expr(lhs),
                Self::max_positional_block_arg_in_expr(rhs),
            ]
            .into_iter()
            .flatten()
            .max(),
            ExprKind::Block(block) => Self::max_positional_block_arg(block),
            ExprKind::Call { callee, args, .. } => {
                std::iter::once(Self::max_positional_block_arg_in_expr(callee))
                    .chain(
                        args.iter()
                            .map(|arg| Self::max_positional_block_arg_in_expr(&arg.value)),
                    )
                    .flatten()
                    .max()
            }
            ExprKind::Member(receiver, ..) => receiver
                .as_ref()
                .and_then(|receiver| Self::max_positional_block_arg_in_expr(receiver)),
            ExprKind::If(condition, then_block, else_block) => [
                Self::max_positional_block_arg_in_expr(condition),
                Self::max_positional_block_arg(then_block),
                Self::max_positional_block_arg(else_block),
            ]
            .into_iter()
            .flatten()
            .max(),
            ExprKind::Match(scrutinee, arms) => {
                std::iter::once(Self::max_positional_block_arg_in_expr(scrutinee))
                    .chain(
                        arms.iter()
                            .map(|arm| Self::max_positional_block_arg(&arm.body)),
                    )
                    .flatten()
                    .max()
            }
            ExprKind::RecordLiteral { fields, spread } => fields
                .iter()
                .map(|field| Self::max_positional_block_arg_in_expr(&field.value))
                .chain(std::iter::once(spread.as_ref().and_then(|spread| {
                    Self::max_positional_block_arg_in_expr(spread)
                })))
                .flatten()
                .max(),
            ExprKind::CallEffect { args, .. } => args
                .iter()
                .filter_map(|arg| Self::max_positional_block_arg_in_expr(&arg.value))
                .max(),
            ExprKind::Func(_)
            | ExprKind::Incomplete(_)
            | ExprKind::InlineIR(_)
            | ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_)
            | ExprKind::LiteralCharacter(_)
            | ExprKind::Constructor(_) => None,
        }
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

        if consumes_left_brace && let Err(err) = self.consume(TokenKind::LeftBrace) {
            if matches!(context, BlockContext::If | BlockContext::Loop) {
                self.record_diagnostic(err);
                return self.save_meta(tok, |id, span| Block {
                    id,
                    span,
                    args: vec![],
                    body: vec![],
                });
            }
            return Err(err);
        }

        let args = self.block_args()?;

        self.skip_semicolons_and_newlines();
        let mut body = vec![];
        loop {
            if self.did_match(TokenKind::RightBrace)? {
                break;
            }
            if self.peek_is(TokenKind::EOF) {
                self.record_diagnostic(self.expected_token_error(TokenKind::RightBrace));
                break;
            }
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
            let Ok(mode) = self.param_mode() else {
                rollback(self);
                return Ok(vec![]);
            };

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
                mode: mode.map(|(mode, _)| mode),
                mode_span: mode.map(|(_, span)| span),
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

        loop {
            if self.did_match(TokenKind::RightBrace)? {
                break;
            }
            self.skip_newlines();
            if self.at_delimiter_recovery_boundary() {
                self.record_diagnostic(self.expected_token_error(TokenKind::RightBrace));
                break;
            }

            if self.peek_is(TokenKind::DotDotDot) {
                // Spread syntax: ...expr
                self.consume(TokenKind::DotDotDot)?;
                let expr = self.expr_with_precedence(Precedence::Assignment)?;

                spread = Some(Box::new(expr.try_into()?));

                // Spread must be the last thing in the record
                self.consume_or_recover_closer_after_newline(TokenKind::RightBrace)?;
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

            self.skip_newlines();
            if self.peek_is(TokenKind::RightBrace) {
                self.consume(TokenKind::Comma).ok();
            } else if self.at_delimiter_recovery_boundary() || self.previous_token_was_newline() {
                self.record_diagnostic(self.expected_token_error(TokenKind::RightBrace));
                break;
            } else {
                self.consume(TokenKind::Comma)?;
            }
            self.skip_newlines();
        }

        Ok(ExprKind::RecordLiteral { fields, spread })
    }

    fn associated_type(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Associated)?;
        let generic = self.generic()?;
        let where_clause = self.where_clause()?;
        self.save_meta(tok, |id, span| Decl {
            id,
            span,
            visibility: Visibility::default(),
            kind: DeclKind::Associated {
                generic,
                where_clause,
            },
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
        let default = if self.did_match(TokenKind::Equals)? {
            Some(self.type_annotation()?)
        } else {
            None
        };

        self.save_meta(tok, |id, span| GenericDecl {
            id,
            span,
            name: name.into(),
            name_span,
            generics,
            conformances,
            default,
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
        loop {
            let mode = self.param_mode()?;
            let (name, name_span) = match self.identifier() {
                Ok(name) => name,
                // A mode keyword must be followed by a parameter name.
                Err(err) if mode.is_some() => return Err(err),
                Err(_) => break,
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
                mode: mode.map(|(mode, _)| mode),
                mode_span: mode.map(|(_, span)| span),
            })?;
            params.push(param);

            if self.did_match(TokenKind::Comma)? {
                continue;
            }

            break;
        }

        Ok(params)
    }

    /// An optional ownership-mode prefix on a parameter (ADR 0018):
    /// `mut x`, `consume x`, `consume mut x`, or `borrow x`. `mut` is a
    /// hard keyword; `consume`/`borrow` are contextual and only read as
    /// modes when the parameter name follows.
    fn param_mode(&mut self) -> Result<Option<(ParamMode, Span)>, ParserError> {
        self.skip_semicolons_and_newlines();

        if self.peek_is(TokenKind::Mut) {
            let tok = self.advance().expect("peeked Mut");
            return Ok(Some((ParamMode::Mut, self.token_span(&tok))));
        }

        if self.peek_identifier("consume") && self.next_is_parameter_name(true) {
            let tok = self.advance().expect("peeked consume");
            let mut span = self.token_span(&tok);
            let mode = if self.peek_is(TokenKind::Mut) {
                let mut_tok = self.advance().expect("peeked Mut");
                span.end = mut_tok.end;
                ParamMode::ConsumeMut
            } else {
                ParamMode::Consume
            };
            return Ok(Some((mode, span)));
        }

        if self.peek_identifier("borrow") && self.next_is_parameter_name(false) {
            let tok = self.advance().expect("peeked borrow");
            return Ok(Some((ParamMode::Borrow, self.token_span(&tok))));
        }

        Ok(None)
    }

    fn token_span(&self, token: &Token) -> Span {
        Span {
            file_id: self.file_id,
            start: token.start,
            end: token.end,
        }
    }

    fn next_is_parameter_name(&self, allow_mut: bool) -> bool {
        match self.next.as_ref().map(|token| &token.kind) {
            Some(TokenKind::Identifier) => true,
            Some(TokenKind::Mut) => allow_mut,
            _ => false,
        }
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
            && matches!(current.kind, TokenKind::Identifier | TokenKind::Use)
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

    fn consume_or_recover_closer(&mut self, expected: TokenKind) -> Result<bool, ParserError> {
        self.skip_newlines();
        if self.peek_is(expected) {
            self.advance();
            return Ok(true);
        }

        let err = self.expected_token_error(expected);
        if self.at_delimiter_recovery_boundary() {
            self.record_diagnostic(err);
            Ok(false)
        } else {
            Err(err)
        }
    }

    fn consume_or_recover_closer_after_newline(
        &mut self,
        expected: TokenKind,
    ) -> Result<bool, ParserError> {
        self.skip_newlines();
        if self.peek_is(expected) {
            self.advance();
            return Ok(true);
        }

        let err = self.expected_token_error(expected);
        if self.at_delimiter_recovery_boundary() || self.previous_token_was_newline() {
            self.record_diagnostic(err);
            Ok(false)
        } else {
            Err(err)
        }
    }

    fn expected_token_error(&self, expected: TokenKind) -> ParserError {
        ParserError::UnexpectedToken {
            expected: format!("{expected:?}"),
            actual: format!("{:?}", self.current),
            token: self.current.clone(),
        }
    }

    fn at_delimiter_recovery_boundary(&self) -> bool {
        matches!(
            self.current.as_ref().map(|token| token.kind),
            Some(TokenKind::RightBrace)
                | Some(TokenKind::RightParen)
                | Some(TokenKind::RightBracket)
                | Some(TokenKind::EOF)
        )
    }

    fn previous_token_was_newline(&self) -> bool {
        self.previous
            .as_ref()
            .is_some_and(|token| token.kind == TokenKind::Newline)
    }

    fn empty_recovered_block(&mut self) -> Block {
        Block {
            id: self.next_id(),
            span: Span::SYNTHESIZED,
            args: vec![],
            body: vec![],
        }
    }

    pub(super) fn peek_is(&self, expected: TokenKind) -> bool {
        if let Some(Token { kind: actual, .. }) = &self.current {
            *actual == expected
        } else {
            false
        }
    }

    fn peek_identifier(&self, expected: &str) -> bool {
        self.current.as_ref().is_some_and(|token| {
            token.kind == TokenKind::Identifier && self.lexeme(token) == expected
        })
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
        // A lexer error ends the token stream; the stored error is
        // surfaced by parse_with_comments instead of being swallowed.
        self.next = if self.lexer_error.is_some() {
            None
        } else {
            match self.lexer.next() {
                Ok(token) => Some(token),
                Err(error) => {
                    let (line, col) = self.lexer.line_col();
                    self.lexer_error = Some((error, line, col));
                    None
                }
            }
        };
        self.previous.clone()
    }

    fn take_lexer_error(&mut self) -> Option<ParserError> {
        self.lexer_error
            .take()
            .map(|(error, line, col)| ParserError::Lexer { error, line, col })
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

fn first_param_is_self(params: &[Parameter]) -> bool {
    params
        .first()
        .is_some_and(|param| param.name.name_str() == "self")
}

/// Does the pattern contain alternatives anywhere? Or-pattern lets
/// desugar to a single-arm match (see `desugar_let_else`).
fn pattern_contains_or(pattern: &Pattern) -> bool {
    match &pattern.kind {
        PatternKind::Or(_) => true,
        PatternKind::Tuple(patterns)
        | PatternKind::Variant {
            fields: patterns, ..
        } => patterns.iter().any(pattern_contains_or),
        PatternKind::Record { fields } => fields.iter().any(|field| match &field.kind {
            RecordFieldPatternKind::Equals { value, .. } => pattern_contains_or(value),
            _ => false,
        }),
        _ => false,
    }
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
