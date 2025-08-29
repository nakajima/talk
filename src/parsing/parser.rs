use crate::ast::{AST, NewAST, Parsed};
use crate::id_generator::IDGenerator;
use crate::label::Label;
use crate::lexer::Lexer;
use crate::name::Name;
use crate::node::Node;
use crate::node_id::NodeID;
use crate::node_kinds::block::Block;
use crate::node_kinds::call_arg::CallArg;
use crate::node_kinds::decl::{Decl, DeclKind};
use crate::node_kinds::expr::{Expr, ExprKind};
use crate::node_kinds::func::Func;
use crate::node_kinds::generic_decl::GenericDecl;
use crate::node_kinds::incomplete_expr::IncompleteExpr;
use crate::node_kinds::match_arm::MatchArm;
use crate::node_kinds::parameter::Parameter;
use crate::node_kinds::pattern::{Pattern, PatternKind};
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

#[derive(PartialEq, Clone, Copy, Debug, Eq, PartialOrd, Ord)]
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

// for tracking begin/end tokens
pub struct SourceLocationStart {
    token: Token,
    identifiers: Vec<Token>,
}
pub type SourceLocationStack = Vec<SourceLocationStart>;

pub struct Parser<'a> {
    ids: &'a mut IDGenerator,
    lexer: Lexer<'a>,
    source_location_stack: SourceLocationStack,
    next: Option<Token>,
    current: Option<Token>,
    previous: Option<Token>,
    previous_before_newline: Option<Token>,
    ast: AST,
}

impl<'a> Parser<'a> {
    pub fn new(path: impl Into<String>, ids: &'a mut IDGenerator, lexer: Lexer<'a>) -> Self {
        Self {
            ids,
            lexer,
            next: None,
            current: None,
            previous: None,
            previous_before_newline: None,
            source_location_stack: Default::default(),
            ast: AST::<NewAST> {
                path: path.into(),
                roots: Default::default(),
                diagnostics: Default::default(),
                meta: Default::default(),
                phase: (),
            },
        }
    }

    pub fn parse(mut self) -> Result<AST<Parsed>> {
        self.advance();
        self.advance();
        self.skip_semicolons_and_newlines();

        let mut last_start = u32::MAX;

        while let Some(current) = self.current.clone() {
            self.skip_semicolons_and_newlines();

            if current.start == last_start {
                return Err(ParserError::InfiniteLoop(Some(current)).into());
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
            diagnostics: self.ast.diagnostics,
            meta: self.ast.meta,
            phase: Parsed,
        };

        Ok(ast)
    }

    fn next_root(&mut self, kind: &TokenKind) -> Result<Node, ParserError> {
        use TokenKind::*;
        if matches!(kind, Protocol | Struct | Enum | Let | Func | Case | Extend) {
            self.decl(BlockContext::None, false)
        } else {
            Ok(Node::Stmt(self.stmt()?))
        }
    }

    // MARK: Decls

    #[instrument(skip(self))]
    fn decl(&mut self, context: BlockContext, is_static: bool) -> Result<Node, ParserError> {
        self.skip_semicolons_and_newlines();

        let Some(current) = self.current.clone() else {
            unreachable!()
        };

        use TokenKind::*;
        let node: Node = match &current.kind {
            Static => {
                self.consume(TokenKind::Static)?;
                self.decl(context, true)?
            }
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
                _ => return Err(ParserError::LetNotAllowed(context)),
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

    #[instrument(skip(self))]
    fn init_decl(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Init)?;
        self.consume(TokenKind::LeftParen)?;
        let params = self.parameters()?;
        self.consume(TokenKind::RightParen)?;

        let body = self.block(BlockContext::Func)?;
        let (id, span) = self.save_meta(tok)?;

        Ok(Decl {
            id,
            span,
            kind: DeclKind::Init { params, body },
        })
    }

    #[instrument(skip(self))]
    fn method_decl(&mut self, context: BlockContext, is_static: bool) -> Result<Decl, ParserError> {
        let func_decl = self.func_decl(context, true)?;
        Ok(Decl {
            id: func_decl.id,
            span: func_decl.span,
            kind: DeclKind::Method {
                func: Box::new(func_decl),
                is_static,
            },
        })
    }

    #[instrument(skip(self))]
    fn property_decl(&mut self, is_static: bool) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Let)?;
        let name = self.identifier()?;
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

        let (id, span) = self.save_meta(tok)?;
        Ok(Decl {
            id,
            span,
            kind: DeclKind::Property {
                name: name.into(),
                is_static,
                type_annotation,
                default_value,
            },
        })
    }

    #[instrument(skip(self))]
    fn variant_decl(&mut self, expect_case: bool) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        if expect_case {
            self.consume(TokenKind::Case)?;
        }
        let name = self.identifier()?;
        let values = if self.did_match(TokenKind::LeftParen)? {
            self.type_annotations(TokenKind::RightParen)?
        } else {
            vec![]
        };
        let (id, span) = self.save_meta(tok)?;
        Ok(Decl {
            id,
            span,
            kind: DeclKind::EnumVariant(name.into(), values),
        })
    }

    #[instrument(skip(self))]
    pub(crate) fn nominal_decl(
        &mut self,
        entry: TokenKind,
        context: BlockContext,
    ) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(entry)?;
        let name = self.identifier()?;
        let generics = self.generics()?;

        let conformances = if self.did_match(TokenKind::Colon)? {
            self.conformances()?
        } else {
            vec![]
        };

        let body = self.block(context)?;
        let (id, span) = self.save_meta(tok)?;

        let kind = match context {
            BlockContext::Enum => DeclKind::Enum {
                name: name.into(),
                conformances,
                generics,
                body,
            },
            BlockContext::Struct => DeclKind::Struct {
                name: name.into(),
                conformances,
                generics,
                body,
            },
            BlockContext::Extend => DeclKind::Extend {
                name: name.into(),
                conformances,
                generics,
                body,
            },
            BlockContext::Protocol => DeclKind::Protocol {
                name: name.into(),
                conformances,
                generics,
                body,
            },
            _ => unreachable!("tried to call nominal_decl with wrong context: {context:?}"),
        };
        Ok(Decl { id, span, kind })
    }

    #[instrument(skip(self))]
    pub(crate) fn let_decl(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Let)?;
        let lhs = self.parse_pattern()?;

        let type_annotation = if self.did_match(TokenKind::Colon)? {
            Some(self.type_annotation()?)
        } else {
            None
        };
        let value = if self.did_match(TokenKind::Equals)? {
            Some(self.expr()?.as_expr())
        } else {
            None
        };

        let (id, span) = self.save_meta(tok)?;

        Ok(Decl {
            id,
            span,
            kind: DeclKind::Let {
                lhs,
                type_annotation,
                value,
            },
        })
    }

    #[instrument(skip(self))]
    pub(crate) fn func_decl(
        &mut self,
        context: BlockContext,
        consume_func_keyword: bool,
    ) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();

        if consume_func_keyword {
            self.consume(TokenKind::Func)?;
        }

        let name = self.identifier()?;
        let generics = self.generics()?;

        self.consume(TokenKind::LeftParen)?;
        let params = self.parameters()?;
        self.consume(TokenKind::RightParen)?;

        let ret = if self.consume(TokenKind::Arrow).is_ok() {
            Some(self.type_annotation()?)
        } else {
            None
        };

        if context == BlockContext::Protocol && !self.peek_is(TokenKind::LeftBrace) {
            let (id, span) = self.save_meta(tok)?;

            let Some(ret) = ret else {
                return Err(ParserError::IncompleteFuncSignature(
                    "return value not specified".into(),
                ));
            };

            return Ok(Decl {
                id,
                span,
                kind: DeclKind::FuncSignature {
                    name: name.into(),
                    generics,
                    params,
                    ret: Box::new(ret),
                },
            });
        }

        let body = self.block(BlockContext::Func)?;
        let (id, span) = self.save_meta(tok)?;

        Ok(Decl {
            id,
            span,
            kind: DeclKind::Func(Func {
                id,
                name: name.into(),
                generics,
                params,
                body,
                ret,
                attributes: vec![],
            }),
        })
    }

    // MARK: Statements

    #[instrument(skip(self))]
    pub(crate) fn stmt(&mut self) -> Result<Stmt, ParserError> {
        self.skip_semicolons_and_newlines();

        let Some(current) = &self.current else {
            return Err(ParserError::UnexpectedEndOfInput(None));
        };

        match &current.kind {
            TokenKind::If => self.if_stmt(),
            TokenKind::Loop => self.loop_stmt(),
            TokenKind::Break => {
                let tok = self.push_source_location();
                self.consume(TokenKind::Break)?;
                let (id, span) = self.save_meta(tok)?;
                Ok(Stmt {
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
                e => unreachable!("{e:?}"),
            },
        }
    }

    #[instrument(skip(self))]
    fn if_stmt(&mut self) -> Result<Stmt, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::If)?;
        let cond = self.expr()?;
        let body = self.block(BlockContext::If)?;

        if self.did_match(TokenKind::Else)? {
            let alt = self.block(BlockContext::If)?;
            let (id, span) = self.save_meta(tok)?;
            Ok(Stmt {
                id,
                span,
                kind: StmtKind::Expr(Expr {
                    id,
                    span,
                    kind: ExprKind::If(Box::new(cond.as_expr()), body, alt),
                }),
            })
        } else {
            let (id, span) = self.save_meta(tok)?;
            Ok(Stmt {
                id,
                span,
                kind: StmtKind::If(cond.as_expr(), body),
            })
        }
    }

    #[instrument(skip(self))]
    fn loop_stmt(&mut self) -> Result<Stmt, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Loop)?;

        let cond = if !self.peek_is(TokenKind::LeftBrace) {
            Some(self.expr()?)
        } else {
            None
        };

        let body = self.block(BlockContext::Loop)?;
        let (id, span) = self.save_meta(tok)?;
        Ok(Stmt {
            id,
            span,
            kind: StmtKind::Loop(cond.map(|c| c.as_expr()), body),
        })
    }

    // MARK: Exprs

    #[instrument(skip(self))]
    pub(super) fn array(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::LeftBracket)?;
        let mut items = vec![];
        while !self.did_match(TokenKind::RightBracket)? {
            items.push(self.expr()?.as_expr());
            self.consume(TokenKind::Comma).ok();
        }
        let (id, span) = self.save_meta(tok)?;
        Ok(Expr {
            id,
            span,
            kind: ExprKind::LiteralArray(items),
        }
        .into())
    }

    #[instrument(skip(self))]
    pub(crate) fn match_expr(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Match)?;
        let scrutinee = self.expr()?;

        self.consume(TokenKind::LeftBrace)?;

        let mut arms = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_newlines();
            let arm_tok = self.push_source_location();
            let pattern = self.parse_pattern()?;
            self.consume(TokenKind::Arrow)?;

            let body = self.block(BlockContext::MatchArmBody)?;
            let (id, span) = self.save_meta(arm_tok)?;
            arms.push(MatchArm {
                id,
                span,
                pattern,
                body,
            });

            self.consume(TokenKind::Comma).ok();
            self.skip_newlines();
        }

        let (id, span) = self.save_meta(tok)?;

        Ok(Node::Expr(Expr {
            id,
            span,
            kind: ExprKind::Match(Box::new(scrutinee.as_expr()), arms),
        }))
    }

    #[instrument(skip(self))]
    pub(super) fn parse_pattern(&mut self) -> Result<Pattern, ParserError> {
        let tok = self.push_source_location();
        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEndOfInput(Some(
                "Expected match arm pattern".into(),
            )));
        };

        let kind = match current.kind {
            TokenKind::Int(val) => {
                self.advance();
                PatternKind::LiteralInt(val)
            }
            TokenKind::Float(val) => {
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
            TokenKind::Identifier(name) => {
                self.advance();
                if self.did_match(TokenKind::Dot)? {
                    let member_name = self.identifier()?;
                    let fields = self.pattern_fields()?;
                    PatternKind::Variant {
                        enum_name: Some(name.into()),
                        variant_name: member_name.to_string(),
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
                let member_name = self.identifier()?;
                let fields = self.pattern_fields()?;

                PatternKind::Variant {
                    enum_name: None,
                    variant_name: member_name.to_string(),
                    fields,
                }
            }

            _ => todo!("{:?}", current.kind),
        };

        let (id, span) = self.save_meta(tok)?;
        Ok(Pattern { id, span, kind })
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

    #[instrument(skip(self))]
    pub(crate) fn member_infix(
        &mut self,
        can_assign: bool,
        lhs: Expr,
    ) -> Result<Node, ParserError> {
        let tok = self.push_lhs_location(lhs.id);
        self.consume(TokenKind::Dot)?;

        let name = match self.current.clone().map(|c| c.kind) {
            Some(TokenKind::Identifier(_)) => match self.identifier() {
                Ok(name) => Label::Named(name),
                Err(_) => {
                    let incomplete_member =
                        ExprKind::Incomplete(IncompleteExpr::Member(Some(Box::new(lhs))));
                    return Ok(Node::Expr(self.add_expr(incomplete_member, tok)?));
                }
            },
            Some(TokenKind::Int(val)) => {
                self.advance();
                Label::Positional(str::parse(&val).map_err(|_| ParserError::BadLabel(val))?)
            }
            Some(_) | None => {
                return Err(ParserError::ExpectedIdentifier(self.current.clone()));
            }
        };

        let member = self.add_expr(ExprKind::Member(Some(Box::new(lhs)), name), tok)?;

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
                let (id, span) = self.save_meta(loc)?;
                return Ok(Node::Stmt(Stmt {
                    id,
                    span,
                    kind: StmtKind::Assignment(expr, rhs.as_expr()),
                }));
            } else {
                return Err(ParserError::CannotAssign);
            }
        }

        Ok(Node::Expr(expr))
    }

    #[instrument(skip(self))]
    pub(super) fn unary(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let op = self.consume_any(vec![TokenKind::Minus, TokenKind::Bang])?;
        let current_precedence = Precedence::handler(&Some(op.clone()))?.precedence;
        let rhs = Box::new(self.expr_with_precedence(current_precedence)?);

        Ok(self
            .add_expr(ExprKind::Unary(op.kind, Box::new(rhs.as_expr())), tok)?
            .into())
    }

    #[instrument(skip(self))]
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

    #[instrument(skip(self))]
    pub(crate) fn block_prefix(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let block = self.block(BlockContext::None)?;
        Ok(Node::Expr(Expr {
            id: block.id,
            span: block.span,
            kind: ExprKind::Block(block),
        }))
    }

    #[instrument(skip(self))]
    pub fn literal(&mut self, _can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let current = self.advance().expect("unreachable");
        let expr = match &current.kind {
            TokenKind::Int(val) => self.add_expr(ExprKind::LiteralInt(val.to_string()), tok),
            TokenKind::Float(val) => self.add_expr(ExprKind::LiteralFloat(val.to_string()), tok),
            TokenKind::True => self.add_expr(ExprKind::LiteralTrue, tok),
            TokenKind::False => self.add_expr(ExprKind::LiteralFalse, tok),
            TokenKind::StringLiteral(val) => {
                self.add_expr(ExprKind::LiteralString(val.into()), tok)
            }
            _ => unreachable!(),
        };

        Ok(expr?.into())
    }

    #[instrument(skip(self))]
    pub(crate) fn variable(&mut self, can_assign: bool) -> Result<Node, ParserError> {
        let tok = self.push_source_location();
        let name = self.identifier()?;
        let variable = self.add_expr(ExprKind::Variable(Name::Raw(name.to_string())), tok)?;

        self.skip_newlines();

        if let Some(call_expr) = self.check_call(&variable, can_assign)? {
            Ok(call_expr.into())
        } else if can_assign && self.did_match(TokenKind::Equals)? {
            let tok = self.push_lhs_location(variable.id);
            let rhs = self.expr()?;
            let (id, span) = self.save_meta(tok)?;
            Ok(Stmt {
                id,
                span,
                kind: StmtKind::Assignment(variable, rhs.as_expr()),
            }
            .into())
        } else {
            Ok(variable.into())
        }
    }

    #[instrument(skip(self))]
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

    #[instrument(skip(self))]
    fn expr(&mut self) -> Result<Node, ParserError> {
        self.expr_with_precedence(Precedence::Assignment)
    }

    #[instrument(skip(self))]
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
            Ok(lhs)
        } else {
            self.advance();
            Err(ParserError::UnexpectedEndOfInput(Some(format!(
                "expected lhs. {:?}",
                self.ast
            ))))
        }
    }

    #[instrument(skip(self))]
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

        Ok(None)
    }

    #[instrument(skip(self))]
    pub(crate) fn call(
        &mut self,
        _can_assign: bool,
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

        self.add_expr(
            ExprKind::Call {
                callee: Box::new(callee),
                type_args,
                args,
            },
            tok,
        )
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
                    kind: TokenKind::Identifier(_),
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
                let Some(label) = self.identifier().ok() else {
                    return Err(ParserError::ExpectedIdentifier(self.current.clone()));
                };
                let tok = self.push_source_location();
                self.consume(TokenKind::Colon)?;
                let value = self.expr_with_precedence(Precedence::Assignment)?;
                let (id, span) = self.save_meta(tok)?;
                args.push(CallArg {
                    id,
                    span,
                    label: label.into(),
                    value: value.as_expr(),
                })
            } else {
                let value = self.expr_with_precedence(Precedence::Assignment)?;
                let (id, span) = self.save_meta(tok)?;

                args.push(CallArg {
                    id,
                    span,
                    label: Label::Positional(i),
                    value: value.as_expr(),
                })
            }

            i += 1;
            self.did_match(TokenKind::Comma)?
        } {}

        Ok(args)
    }

    #[instrument(skip(self))]
    fn type_annotation(&mut self) -> Result<TypeAnnotation, ParserError> {
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
                let (id, span) = self.save_meta(tok)?;
                return Ok(TypeAnnotation {
                    id,
                    span,
                    kind: TypeAnnotationKind::Func {
                        params: sig_args,
                        returns: Box::new(ret),
                    },
                });
            } else {
                let (id, span) = self.save_meta(tok)?;
                return Ok(TypeAnnotation {
                    id,
                    span,
                    kind: TypeAnnotationKind::Tuple(sig_args),
                });
            }
        }

        // // Check for record type: {x: Int, y: Int, ..R}
        // if self.did_match(TokenKind::LeftBrace)? {
        //     return self.record_type_repr(is_type_parameter, tok);
        // }

        // // Check for row variable: ..R
        // if self.did_match(TokenKind::DotDot)? {
        //     let name = self.identifier()?;
        //     return self.add_expr(RowVariable(Name::Raw(name)), tok);
        // }

        let name = self.identifier()?;
        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                let generic = self.type_annotation()?;
                generics.push(generic);
                self.consume(TokenKind::Comma).ok();
            }
        }

        let (id, span) = self.save_meta(tok)?;

        Ok(TypeAnnotation {
            id,
            span,
            kind: TypeAnnotationKind::Nominal {
                name: name.into(),
                generics,
            },
        })
    }

    // fn record_type_repr(
    //     &mut self,
    //     is_type_parameter: bool,
    //     tok: LocToken,
    // ) -> Result<Expr, ParserError> {
    //     let mut fields: Vec<Expr> = vec![];
    //     let mut row_var: Option<Box<Expr>> = None;

    //     while !self.did_match(TokenKind::RightBrace)? {
    //         self.skip_newlines();

    //         // Check for row variable: ..R
    //         if self.did_match(TokenKind::DotDot)? {
    //             let row_tok = self.push_source_location();
    //             let name = self.identifier()?;
    //             row_var = Some(Box::new(
    //                 self.add_expr(RowVariable(Name::Raw(name)), row_tok)?,
    //             ));

    //             // Row variable should be the last element
    //             self.consume(TokenKind::Comma).ok();
    //             self.skip_newlines();
    //             self.consume(TokenKind::RightBrace)?;
    //             break;
    //         }

    //         // Regular field: label: Type
    //         let field_tok = self.push_source_location();
    //         let label = self.identifier()?;
    //         self.consume(TokenKind::Colon)?;
    //         let ty = self.type_repr(false)?; // Fields are not type parameters
    //         fields.push(self.add_expr(
    //             RecordTypeField {
    //                 label: Name::Raw(label),
    //                 ty: Box::new(ty),
    //             },
    //             field_tok,
    //         )?);

    //         // Handle comma
    //         if !self.peek_is(TokenKind::RightBrace) && !self.peek_is(TokenKind::DotDot) {
    //             self.consume(TokenKind::Comma)?;
    //         } else {
    //             self.consume(TokenKind::Comma).ok(); // Optional trailing comma
    //         }
    //         self.skip_newlines();
    //     }

    //     self.add_expr(
    //         RecordTypeRepr {
    //             fields,
    //             row_var,
    //             introduces_type: is_type_parameter,
    //         },
    //         tok,
    //     )
    // }

    #[instrument(skip(self))]
    fn conformances(&mut self) -> Result<Vec<TypeAnnotation>, ParserError> {
        let mut conformances: Vec<TypeAnnotation> = vec![];

        while {
            conformances.push(self.type_annotation()?);
            self.did_match(TokenKind::Comma)?
        } {}

        Ok(conformances)
    }

    #[instrument(skip(self))]
    fn type_annotations(&mut self, closer: TokenKind) -> Result<Vec<TypeAnnotation>, ParserError> {
        let mut annotations: Vec<TypeAnnotation> = vec![];

        while !self.did_match(closer.clone())? {
            annotations.push(self.type_annotation()?);
            self.consume(TokenKind::Comma).ok();
        }

        Ok(annotations)
    }

    #[instrument(skip(self))]
    fn block(&mut self, context: BlockContext) -> Result<Block, ParserError> {
        self.skip_semicolons_and_newlines();
        let tok = self.push_source_location();

        if context == BlockContext::MatchArmBody && !self.peek_is(TokenKind::LeftBrace) {
            let stmt = self.stmt()?;
            let (id, span) = self.save_meta(tok)?;
            return Ok(Block {
                id,
                span,
                args: vec![],
                body: vec![stmt.into()],
            });
        };

        self.consume(TokenKind::LeftBrace)?;

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

        let (id, span) = self.save_meta(tok)?;

        Ok(Block {
            id,
            span,
            args: vec![],
            body,
        })
    }

    fn associated_type(&mut self) -> Result<Decl, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Associated)?;
        let generic = self.generic()?;
        let (id, span) = self.save_meta(tok)?;
        Ok(Decl {
            id,
            span,
            kind: DeclKind::Associated { generic },
        })
    }

    #[instrument(skip(self))]
    fn generic(&mut self) -> Result<GenericDecl, ParserError> {
        let tok = self.push_source_location();
        let name = self.identifier()?;
        let generics = self.generics()?;

        let conformances = if self.did_match(TokenKind::Colon)? {
            self.generics()?
        } else {
            vec![]
        };

        let (id, span) = self.save_meta(tok)?;
        Ok(GenericDecl {
            id,
            span,
            name: name.into(),
            generics,
            conformances,
        })
    }

    #[instrument(skip(self))]
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

    #[instrument(skip(self))]
    fn parameters(&mut self) -> Result<Vec<Parameter>, ParserError> {
        let mut params: Vec<Parameter> = vec![];
        while let Ok(name) = self.identifier() {
            let tok = self.push_source_location();
            let type_annotation = if self.did_match(TokenKind::Colon)? {
                Some(self.type_annotation()?)
            } else {
                None
            };

            let (id, span) = self.save_meta(tok)?;
            let param = Parameter {
                id,
                span,
                name: name.into(),
                type_annotation,
            };
            params.push(param);

            if self.did_match(TokenKind::Comma)? {
                continue;
            }

            break;
        }

        Ok(params)
    }

    #[instrument(skip(self))]
    pub(super) fn identifier(&mut self) -> Result<String, ParserError> {
        self.skip_semicolons_and_newlines();
        if let Some(current) = self.current.clone()
            && let TokenKind::Identifier(ref name) = current.kind
        {
            self.push_identifier(current.clone());
            self.advance();
            return Ok(name.to_string());
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
        tracing::trace!("advance {:?}", self.current);
        self.previous = self.current.take();

        if let Some(prev) = &self.previous
            && prev.kind != TokenKind::Newline
        {
            self.previous_before_newline = Some(prev.clone());
        }

        self.current = self.next.take();
        self.next = self.lexer.next().ok();
        self.previous.clone()
    }

    #[instrument(skip(self, loc))]
    fn add_expr(&mut self, expr_kind: ExprKind, loc: LocToken) -> Result<Expr, ParserError> {
        let (id, span) = self.save_meta(loc)?;
        Ok(Expr {
            id,
            span,
            kind: expr_kind,
        })
    }

    pub(super) fn save_meta(&mut self, _loc: LocToken) -> Result<(NodeID, Span), ParserError> {
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

        let next_id = self.ids.next_id().into();
        self.ast.meta.insert(next_id, meta);

        Ok((
            next_id,
            Span {
                start: start.token.start,
                end: token.end,
            },
        ))
    }

    #[must_use]
    #[allow(clippy::unwrap_used)]
    fn push_lhs_location(&mut self, lhs: NodeID) -> LocToken {
        #[allow(clippy::unwrap_used)]
        let meta = self.ast.meta.get(&lhs).unwrap();
        let start = SourceLocationStart {
            token: meta.start.clone(),
            identifiers: vec![],
        };
        self.source_location_stack.push(start);
        LocToken
    }

    #[must_use]
    fn push_source_location(&mut self) -> LocToken {
        tracing::trace!("push_source_location: {:?}", self.current);
        #[allow(clippy::unwrap_used)]
        let start = SourceLocationStart {
            token: self.current.clone().unwrap(),
            identifiers: vec![],
        };
        self.source_location_stack.push(start);
        LocToken
    }

    #[instrument(skip(self))]
    pub(super) fn consume(&mut self, expected: TokenKind) -> Result<Token, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current.clone()
            && current.kind == expected
        {
            if matches!(current.kind, TokenKind::Identifier(_)) {
                self.push_identifier(current.clone());
            }

            self.advance();
            return Ok(current);
        };

        Err(ParserError::UnexpectedToken {
            expected: format!("{expected:?}"),
            actual: format!("{:?}", self.current),
        })
    }

    #[instrument(skip(self))]
    fn consume_any(&mut self, possible_tokens: Vec<TokenKind>) -> Result<Token, ParserError> {
        self.skip_semicolons_and_newlines();

        match self.current.clone() {
            Some(current) => {
                if matches!(current.kind, TokenKind::Identifier(_)) {
                    self.push_identifier(current.clone());
                }

                if possible_tokens.contains(&current.kind) {
                    self.advance();
                    Ok(current)
                } else {
                    Err(ParserError::UnexpectedToken {
                        expected: format!("{possible_tokens:?}"),
                        actual: format!("{current:?}"),
                    })
                }
            }
            None => Err(ParserError::UnexpectedEndOfInput(Some(
                possible_tokens
                    .iter()
                    .map(|v| v.as_str())
                    .collect::<Vec<String>>()
                    .join(", "),
            ))),
        }
    }

    #[instrument(skip(self))]
    fn push_identifier(&mut self, identifier: Token) {
        if let Some(loc) = self.source_location_stack.last_mut() {
            loc.identifiers.push(identifier);
        }
    }
}
