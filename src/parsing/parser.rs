use std::path::PathBuf;

#[cfg(test)]
use crate::filler::FullExpr;
use crate::{
    SourceFile, compiling::compilation_session::SharedCompilationSession, diagnostic::Diagnostic,
    environment::Environment, lexer::Lexer, token::Token, token_kind::TokenKind,
};

use super::{
    expr::{
        self,
        Expr::{self, *},
        ExprMeta,
    },
    name::Name,
    precedence::Precedence,
};

pub type ExprID = i32;
pub type VariableID = u32;

// for tracking begin/end tokens
pub struct SourceLocationStart {
    token: Token,
    identifiers: Vec<Token>,
}
pub type SourceLocationStack = Vec<SourceLocationStart>;

macro_rules! some_kind {
    ($name:ident) => {
        Some(Token {
            kind: TokenKind::$name,
            ..
        })
    };
    ($name:ident($binding:ident)) => {
        Some(Token {
            kind: TokenKind::$name($binding),
            ..
        })
    };
}
// for making sure we've pushed to the location stack
// it's not copyable so we always need to have one before calling add_expr
pub struct LocToken;

pub struct Parser<'a> {
    pub(crate) lexer: Lexer<'a>,
    pub(crate) previous: Option<Token>,
    pub(crate) current: Option<Token>,
    pub(crate) next: Option<Token>,
    pub(crate) parse_tree: SourceFile,
    pub(crate) source_location_stack: SourceLocationStack,
    session: SharedCompilationSession,
    env: &'a mut Environment,
    previous_before_newline: Option<Token>,
}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum ParserError {
    UnexpectedToken(String /* expected */, Option<Token> /* actual */),
    UnexpectedEndOfInput(Option<Vec<TokenKind>> /* expected */),
    UnknownError(String),
    ExpectedIdentifier(Option<Token>),
    CannotAssign,
}

impl ParserError {
    pub fn message(&self) -> String {
        match &self {
            Self::UnexpectedEndOfInput(token_kinds) => {
                if let Some(token_kinds) = token_kinds
                    && token_kinds.is_empty()
                {
                    format!(
                        "Unexpected end of input, expected: {}",
                        &token_kinds
                            .iter()
                            .map(|t| t.as_str())
                            .collect::<Vec<String>>()
                            .join(" ")
                    )
                } else {
                    "Unexpected end of input".to_string()
                }
            }
            Self::UnknownError(e) => e.to_string(),
            Self::ExpectedIdentifier(token) => format!(
                "Expected a name, got: {}",
                token.clone().unwrap_or(Token::GENERATED).as_str()
            ),
            Self::CannotAssign => "Cannot assign".to_string(),
            Self::UnexpectedToken(expected, actual) => {
                format!(
                    "Unexpected token: {}, expected: {}",
                    actual.clone().unwrap_or(Token::GENERATED).as_str(),
                    expected
                )
            }
        }
    }
}

#[cfg(test)]
pub fn parse(code: &str, file_path: PathBuf) -> SourceFile {
    let lexer = Lexer::new(code);
    let mut env = Environment::default();
    let mut parser = Parser::new(env.session.clone(), lexer, file_path, &mut env);

    parser.parse();
    parser.parse_tree
}

#[cfg(test)]
pub fn parse_fill(code: &str) -> Vec<FullExpr> {
    let lexer = Lexer::new(code);
    let mut env = Environment::default();
    let mut parser = Parser::new(env.session.clone(), lexer, PathBuf::from("-"), &mut env);

    parser.parse();

    use crate::filler::Filler;

    let filler = Filler::new(parser.parse_tree);

    filler.fill_root()
}

#[cfg(test)]
pub fn parse_with_comments(code: &str) -> SourceFile {
    let lexer = Lexer::preserving_comments(code);
    let mut env = Environment::default();
    let mut parser = Parser::new(env.session.clone(), lexer, PathBuf::from("-"), &mut env);

    parser.parse();
    parser.parse_tree
}

#[cfg(test)]
pub fn parse_with_session(
    code: &str,
    file_path: PathBuf,
) -> (SourceFile, SharedCompilationSession) {
    let lexer = Lexer::new(code);
    let mut env = Environment::default();
    let session = env.session.clone();
    let mut parser = Parser::new(session.clone(), lexer, file_path, &mut env);

    parser.parse();
    (parser.parse_tree, session)
}

impl<'a> Parser<'a> {
    pub fn new(
        session: SharedCompilationSession,
        lexer: Lexer<'a>,
        file_path: PathBuf,
        env: &'a mut Environment,
    ) -> Self {
        Self {
            lexer,
            previous: None,
            current: None,
            next: None,
            parse_tree: SourceFile::new(file_path),
            source_location_stack: Default::default(),
            session,
            previous_before_newline: None,
            env,
        }
    }

    pub fn parse(&mut self) {
        // Prime the pump
        self.advance();
        self.advance();
        self.skip_newlines();

        while let Some(current) = self.current.clone() {
            self.skip_semicolons_and_newlines();

            if current.kind == TokenKind::EOF {
                return;
            }

            log::trace!("{current:?}");

            match self.parse_with_precedence(Precedence::Assignment) {
                Ok(expr) => self.parse_tree.push_root(expr),
                Err(err) => {
                    log::error!("{}", err.message());
                    self.add_diagnostic(Diagnostic::parser(
                        self.parse_tree.path.clone(),
                        current,
                        err,
                    ));
                    self.recover();
                }
            }

            self.skip_newlines();
        }
    }

    fn add_diagnostic(&mut self, diagnostic: Diagnostic) {
        if let Ok(mut lock) = self.session.lock() {
            lock.add_diagnostic(diagnostic)
        }
    }

    fn recover(&mut self) {
        log::trace!("Recovering parser: {:?}", self.current);

        while let Some(current) = &self.current {
            use TokenKind::*;

            if matches!(self.previous, Some(Token { kind: Newline, .. })) {
                break;
            };

            match current.kind {
                EOF | Struct | Func | Enum | Let | If | Loop | Return => break,
                _ => {
                    self.advance();
                }
            }
        }
    }

    fn skip_newlines(&mut self) {
        while self.peek_is(TokenKind::Newline) {
            self.advance();
        }
    }

    fn skip_semicolons_and_newlines(&mut self) {
        while self.peek_is(TokenKind::Semicolon) || self.peek_is(TokenKind::Newline) {
            log::trace!("Skipping {:?}", self.current);
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

        self.current = self.next.take();
        self.next = self.lexer.next().ok();
        self.previous.clone()
    }

    pub(super) fn add_expr(&mut self, expr: Expr, _loc: LocToken) -> Result<ExprID, ParserError> {
        let token = self
            .previous_before_newline
            .clone()
            .or_else(|| self.previous.clone())
            .ok_or(ParserError::UnknownError(
                "unbalanced source location stack.".into(),
            ))?;
        let start = self
            .source_location_stack
            .pop()
            .ok_or(ParserError::UnknownError(format!(
                "unbalanced source location stack. current: {token:?}"
            )))?;

        let expr_meta = ExprMeta {
            start: start.token,
            end: token,
            identifiers: start.identifiers,
        };

        let next_id = self.env.next_id();

        log::trace!("Add [{next_id}] {expr:?}");

        Ok(self.parse_tree.add(next_id, expr, expr_meta))
    }

    fn push_identifier(&mut self, identifier: Token) {
        if let Some(loc) = self.source_location_stack.last_mut() {
            loc.identifiers.push(identifier);
        }
    }

    #[must_use]
    fn push_lhs_location(&mut self, lhs: ExprID) -> LocToken {
        #[allow(clippy::unwrap_used)]
        let meta = &self.parse_tree.meta.get(&lhs).unwrap();
        let start = SourceLocationStart {
            token: meta.start.clone(),
            identifiers: vec![],
        };
        self.source_location_stack.push(start);
        LocToken
    }

    #[must_use]
    fn push_source_location(&mut self) -> LocToken {
        log::trace!("push_source_location: {:?}", self.current);
        #[allow(clippy::unwrap_used)]
        let start = SourceLocationStart {
            token: self.current.clone().unwrap(),
            identifiers: vec![],
        };
        self.source_location_stack.push(start);
        LocToken
    }

    // MARK: Expr parsers

    pub(crate) fn protocol_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Protocol)?;
        let name = Name::Raw(self.identifier()?);
        let associated_types = self.type_reprs()?;
        let conformances = self.conformances()?;
        let body = self.protocol_body()?;

        self.add_expr(
            Expr::ProtocolDecl {
                name,
                associated_types,
                conformances,
                body,
            },
            tok,
        )
    }

    fn conformances(&mut self) -> Result<Vec<ExprID>, ParserError> {
        let mut conformances = vec![];

        if !self.did_match(TokenKind::Colon)? {
            return Ok(conformances);
        }

        while !(self.peek_is(TokenKind::LeftBrace)
            || self.peek_is(TokenKind::EOF)
            || self.peek_is(TokenKind::Greater))
        {
            conformances.push(self.type_repr(false)?);
            self.consume(TokenKind::Comma).ok();
        }

        Ok(conformances)
    }

    pub(crate) fn struct_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Struct)?;

        let Some((name_str, _)) = self.try_identifier() else {
            return Err(ParserError::ExpectedIdentifier(self.current.clone()));
        };

        let generics = self.type_reprs()?;
        let conformances = self.conformances()?;
        let body = self.struct_body()?;
        self.add_expr(
            Struct {
                name: Name::Raw(name_str),
                generics,
                conformances,
                body,
            },
            tok,
        )
    }

    pub(crate) fn extend_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Extend)?;

        let Some((name_str, _)) = self.try_identifier() else {
            return Err(ParserError::ExpectedIdentifier(self.current.clone()));
        };

        let generics = self.type_reprs()?;
        let conformances = self.conformances()?;
        let body = self.extend_body()?;
        self.add_expr(
            Extend {
                name: Name::Raw(name_str),
                generics,
                conformances,
                body,
            },
            tok,
        )
    }

    fn struct_body(&mut self) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();
        log::info!("in struct body: {:?}", self.current);
        self.consume(TokenKind::LeftBrace)?;
        self.skip_semicolons_and_newlines();

        let mut members: Vec<ExprID> = vec![];

        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_newlines();

            match self.current {
                some_kind!(Let) => {
                    members.push(self.property()?);
                }
                some_kind!(Init) => members.push(self.init()?),
                _ => {
                    members.push(self.parse_with_precedence(Precedence::Assignment)?);
                }
            }
        }

        self.add_expr(Expr::Block(members), tok)
    }

    fn extend_body(&mut self) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();
        self.consume(TokenKind::LeftBrace)?;
        self.skip_semicolons_and_newlines();

        let mut members: Vec<ExprID> = vec![];

        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_newlines();

            match self.current {
                some_kind!(Let) => {
                    return Err(ParserError::UnknownError(
                        "Extensions can't define properties".into(),
                    ));
                }
                some_kind!(Init) => members.push(self.init()?),
                _ => {
                    members.push(self.parse_with_precedence(Precedence::Assignment)?);
                }
            }
        }

        self.add_expr(Expr::Block(members), tok)
    }

    fn protocol_body(&mut self) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();
        self.consume(TokenKind::LeftBrace)?;

        let mut members: Vec<ExprID> = vec![];

        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_semicolons_and_newlines();
            log::info!("in struct body: {:?}", self.current);
            match self.current {
                some_kind!(Let) => {
                    members.push(self.property()?);
                }
                some_kind!(Init) => members.push(self.init()?),
                some_kind!(Func) => {
                    let tok = self.push_source_location();
                    let func_requirement = self.func_requirement()?;
                    let Expr::FuncSignature {
                        name,
                        params,
                        generics,
                        ret,
                    } = &func_requirement
                    else {
                        return Err(ParserError::UnknownError(format!(
                            "Did not get protocol func requirement: {:?}",
                            self.current.clone()
                        )));
                    };

                    // See if we have a default implementation
                    if self.peek_is(TokenKind::LeftBrace) {
                        let body = self.block(false)?;

                        let func = Expr::Func {
                            name: Some(name.clone()),
                            generics: generics.clone(),
                            params: params.clone(),
                            body,
                            ret: Some(*ret),
                            captures: vec![],
                        };

                        members.push(self.add_expr(func, tok)?);
                    } else {
                        members.push(self.add_expr(func_requirement.clone(), tok)?)
                    }
                }
                _ => {
                    members.push(self.parse_with_precedence(Precedence::Assignment)?);
                }
            }

            self.skip_semicolons_and_newlines();
        }

        self.add_expr(Expr::Block(members), tok)
    }

    pub(crate) fn init(&mut self) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        let func_id = self.func()?;
        self.add_expr(Expr::Init(None, func_id), tok)
    }

    pub(crate) fn property(&mut self) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Let)?;
        let name = self.identifier()?;
        let type_repr = if self.did_match(TokenKind::Colon)? {
            Some(self.type_repr(false)?)
        } else {
            None
        };
        let default_value = if self.did_match(TokenKind::Equals)? {
            Some(self.parse_with_precedence(Precedence::Assignment)?)
        } else {
            None
        };

        self.add_expr(
            Expr::Property {
                name: Name::Raw(name),
                type_repr,
                default_value,
            },
            tok,
        )
    }

    pub(crate) fn enum_decl(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Enum)?;
        self.skip_semicolons_and_newlines();

        let name = self.identifier()?;
        let generics = self.type_reprs()?;
        let conformances = self.conformances()?;

        // Consume the block
        let body = self.enum_body()?;

        self.add_expr(
            EnumDecl {
                name: Name::Raw(name),
                generics,
                conformances,
                body,
            },
            tok,
        )
    }

    pub(crate) fn break_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Break)?;
        self.add_expr(Expr::Break, tok)
    }

    pub(crate) fn return_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Return)?;

        if self.peek_is(TokenKind::Newline) || self.peek_is(TokenKind::RightBrace) {
            return self.add_expr(Return(None), tok);
        }

        let rhs = self.parse_with_precedence(Precedence::None)?;
        self.add_expr(Return(Some(rhs)), tok)
    }

    pub(crate) fn match_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Match)?;

        let target = self.parse_with_precedence(Precedence::Assignment)?;
        let body = self.match_block()?;

        self.add_expr(Match(target, body), tok)
    }

    fn match_block(&mut self) -> Result<Vec<ExprID>, ParserError> {
        self.skip_semicolons_and_newlines();
        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<ExprID> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            let tok = self.push_source_location();
            let pattern = self.parse_match_pattern()?;
            let pattern_id = self.add_expr(Pattern(pattern), tok)?;
            self.consume(TokenKind::Arrow)?;
            let tok = self.push_source_location();
            let body = self.parse_with_precedence(Precedence::Primary)?;
            items.push(self.add_expr(MatchArm(pattern_id, body), tok)?);
            self.consume(TokenKind::Comma).ok();
        }

        Ok(items)
    }

    pub(super) fn parse_match_pattern(&mut self) -> Result<expr::Pattern, ParserError> {
        self.skip_semicolons_and_newlines();

        if self.did_match(TokenKind::Underscore)? {
            return Ok(expr::Pattern::Wildcard);
        }

        if let Some(Token { kind, .. }) = self.current.clone() {
            match kind {
                TokenKind::Int(value) => {
                    self.advance();
                    return Ok(expr::Pattern::LiteralInt(value));
                }
                TokenKind::Float(value) => {
                    self.advance();
                    return Ok(expr::Pattern::LiteralFloat(value));
                }
                TokenKind::True => {
                    self.advance();
                    return Ok(expr::Pattern::LiteralTrue);
                }
                TokenKind::False => {
                    self.advance();
                    return Ok(expr::Pattern::LiteralFalse);
                }

                _ => (),
            }
        }

        if let Ok(name) = self.identifier() {
            // It's not an enum variant so it's a bind
            if !self.did_match(TokenKind::Dot)? {
                return Ok(expr::Pattern::Bind(Name::Raw(name)));
            }

            let variant_name = self.identifier()?;
            let mut fields: Vec<ExprID> = vec![];
            if self.did_match(TokenKind::LeftParen)? {
                while !self.did_match(TokenKind::RightParen)? {
                    let tok = self.push_source_location();
                    let pattern = self.parse_match_pattern()?;
                    fields.push(self.add_expr(Expr::Pattern(pattern), tok)?);
                }
            }

            return Ok(expr::Pattern::Variant {
                enum_name: Some(Name::Raw(name)),
                variant_name,
                fields,
            });
        }

        // Unqualified variant
        if self.did_match(TokenKind::Dot)? {
            let Some((variant_name, _)) = self.try_identifier() else {
                return Err(ParserError::ExpectedIdentifier(self.current.clone()));
            };

            log::debug!("unqualified variant");

            let mut fields: Vec<ExprID> = vec![];
            if self.did_match(TokenKind::LeftParen)? {
                while !self.did_match(TokenKind::RightParen)? {
                    log::trace!("adding arg: {:?}", self.current);
                    let tok = self.push_source_location();
                    let pattern = self.parse_match_pattern()?;
                    fields.push(self.add_expr(Expr::Pattern(pattern), tok)?);
                }
            }

            return Ok(expr::Pattern::Variant {
                enum_name: None,
                variant_name,
                fields,
            });
        }

        unreachable!("{:?}", self.current)
    }

    pub(crate) fn member_prefix(&mut self, can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Dot)?;
        let name = self.identifier()?;

        let member = self.add_expr(Member(None, name), tok)?;
        if let Some(call_id) = self.check_call(member, can_assign)? {
            Ok(call_id)
        } else {
            Ok(member)
        }
    }

    pub(crate) fn member_infix(
        &mut self,
        can_assign: bool,
        lhs: ExprID,
    ) -> Result<ExprID, ParserError> {
        let tok = self.push_lhs_location(lhs);
        self.consume(TokenKind::Dot)?;

        let name = match self.identifier() {
            Ok(name) => name,
            Err(e) => {
                // Add an empty member name so name resolution can  but still emit the error
                self.add_diagnostic(Diagnostic::parser(
                    self.parse_tree.path.clone(),
                    self.current.clone().unwrap_or(Token::EOF),
                    e,
                ));
                "".into()
            }
        };

        let member = self.add_expr(Member(Some(lhs), name), tok)?;

        self.skip_semicolons_and_newlines();

        let expr_id = if let Some(call_id) = self.check_call(member, can_assign)? {
            call_id
        } else {
            member
        };

        if self.did_match(TokenKind::Equals)? {
            if can_assign {
                let loc = self.push_source_location();
                let rhs = self.parse_with_precedence(Precedence::Assignment)?;
                return self.add_expr(Expr::Assignment(expr_id, rhs), loc);
            } else {
                return Err(ParserError::CannotAssign);
            }
        }

        Ok(expr_id)
    }

    pub(crate) fn boolean(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();

        if self.did_match(TokenKind::True)? {
            return self.add_expr(Expr::LiteralTrue, tok);
        }

        if self.did_match(TokenKind::False)? {
            return self.add_expr(Expr::LiteralFalse, tok);
        }

        unreachable!()
    }

    pub(crate) fn if_expr(&mut self, can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();

        self.consume(TokenKind::If)?;

        let condition = self.parse_with_precedence(Precedence::Assignment)?;
        let body = self.block(can_assign)?;

        if self.did_match(TokenKind::Else)? {
            let else_body = self.block(can_assign)?;
            self.add_expr(If(condition, body, Some(else_body)), tok)
        } else {
            self.add_expr(If(condition, body, None), tok)
        }
    }

    pub(crate) fn loop_expr(&mut self, can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();

        self.consume(TokenKind::Loop)?;

        let mut condition = None;
        if !self.peek_is(TokenKind::LeftBrace) {
            condition = Some(self.parse_with_precedence(Precedence::None)?)
        }

        let body = self.block(can_assign)?;

        self.add_expr(Loop(condition, body), tok)
    }

    pub(crate) fn tuple(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();

        self.consume(TokenKind::LeftParen)?;

        if self.did_match(TokenKind::RightParen)? {
            return self.add_expr(Tuple(vec![]), tok);
        }

        let child = self.parse_with_precedence(Precedence::Assignment)?;

        if self.did_match(TokenKind::RightParen)? {
            return self.add_expr(Tuple(vec![child]), tok);
        }

        self.consume(TokenKind::Comma)?;

        let mut items = vec![child];
        while {
            items.push(self.parse_with_precedence(Precedence::Assignment)?);
            self.did_match(TokenKind::Comma)?
        } {}

        self.consume(TokenKind::RightParen)?;

        self.add_expr(Tuple(items), tok)
    }

    pub(crate) fn let_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();

        // Consume the `let` keyword
        self.advance();
        let name = self.identifier()?;

        let type_repr = if self.did_match(TokenKind::Colon)? {
            Some(self.type_repr(false)?)
        } else {
            None
        };

        let let_expr = self.add_expr(Let(Name::Raw(name), type_repr), tok);

        if self.did_match(TokenKind::Equals)? {
            let tok = self.push_source_location();
            let rhs = self.parse_with_precedence(Precedence::Assignment)?;
            self.add_expr(Expr::Assignment(let_expr?, rhs), tok)
        } else {
            let_expr
        }
    }

    pub(crate) fn literal(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();

        self.advance();

        let prev = &self
            .previous
            .as_ref()
            .map(|p| p.kind.clone())
            .ok_or(ParserError::UnexpectedEndOfInput(None))?;

        match prev {
            TokenKind::Int(val) => self.add_expr(LiteralInt(val.clone()), tok),
            TokenKind::Float(val) => self.add_expr(LiteralFloat(val.clone()), tok),
            TokenKind::StringLiteral(val) => self.add_expr(LiteralString(val.to_string()), tok),
            TokenKind::Func => self.func(),
            _ => unreachable!("didn't get a literal"),
        }
    }

    pub(crate) fn func_requirement(&mut self) -> Result<Expr, ParserError> {
        self.consume(TokenKind::Func)?;

        let name_str = match self.current.clone() {
            some_kind!(Identifier(name)) => {
                self.advance();
                name
            }
            some_kind!(Init) => {
                self.advance();
                "init".to_string()
            }
            _ => return Err(ParserError::ExpectedIdentifier(self.current.clone())),
        };

        let name = Name::Raw(name_str);
        let generics = self.type_reprs()?;

        self.consume(TokenKind::LeftParen)?;
        let params = self.parameter_list()?;
        self.consume(TokenKind::RightParen)?;

        // We always want a return type for a func requirement
        self.consume(TokenKind::Arrow)?;

        let ret = self.type_repr(false)?;

        Ok(Expr::FuncSignature {
            name,
            params,
            generics,
            ret,
        })
    }

    pub(crate) fn func(&mut self) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();

        let current = self.current.clone();
        let name = match &current {
            some_kind!(Identifier(name)) => {
                self.advance();
                Some(name.as_str())
            }
            some_kind!(Init) => {
                self.advance();
                Some("init")
            }
            _ => None,
        };

        let generics = self.type_reprs()?;

        self.consume(TokenKind::LeftParen)?;
        let params = self.parameter_list()?;
        self.consume(TokenKind::RightParen)?;

        let ret = if self.did_match(TokenKind::Arrow)? {
            Some(self.type_repr(false))
        } else {
            None
        };

        let body = self.block(false)?;

        let func_id = self.add_expr(
            Expr::Func {
                name: name.map(|s| s.to_string()).map(Name::Raw),
                generics,
                params,
                body,
                ret: ret.transpose()?,
                captures: vec![],
            },
            tok,
        )?;

        if let Some(call_id) = self.check_call(func_id, false)? {
            Ok(call_id)
        } else {
            Ok(func_id)
        }
    }

    fn parameter_list(&mut self) -> Result<Vec<ExprID>, ParserError> {
        let mut params: Vec<ExprID> = vec![];
        while let Some((
            _,
            Token {
                kind: TokenKind::Identifier(name),
                ..
            },
        )) = self.try_identifier()
        {
            let tok = self.push_source_location();
            let ty_repr = if self.did_match(TokenKind::Colon)? {
                Some(self.type_repr(false)?)
            } else {
                None
            };

            params.push(self.add_expr(Parameter(name.into(), ty_repr), tok)?);

            if self.did_match(TokenKind::Comma)? {
                continue;
            }

            break;
        }

        Ok(params)
    }

    fn type_repr(&mut self, is_type_parameter: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();

        if self.did_match(TokenKind::LeftParen)? {
            // it's a func type or tuple repr
            let mut sig_args = vec![];
            while !self.did_match(TokenKind::RightParen)? {
                sig_args.push(self.type_repr(is_type_parameter)?);
                self.consume(TokenKind::Comma).ok();
            }
            if self.did_match(TokenKind::Arrow)? {
                let ret = self.type_repr(is_type_parameter)?;
                return self.add_expr(FuncTypeRepr(sig_args, ret, is_type_parameter), tok);
            } else {
                return self.add_expr(TupleTypeRepr(sig_args, is_type_parameter), tok);
            }
        }

        let name = self.identifier()?;
        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                let generic = self.type_repr(is_type_parameter)?;
                generics.push(generic);
                self.consume(TokenKind::Comma).ok();
            }
        }

        let conformances = self.conformances()?;

        let type_repr = TypeRepr {
            name: name.into(),
            generics,
            conformances,
            introduces_type: is_type_parameter,
        };
        let type_repr_id = self.add_expr(type_repr, tok)?;

        if self.did_match(TokenKind::QuestionMark)? {
            let tok = self.push_source_location();
            self.add_expr(
                TypeRepr {
                    name: Name::Raw("Optional".to_string()),
                    generics: vec![type_repr_id],
                    conformances: vec![],
                    introduces_type: is_type_parameter,
                },
                tok,
            )
        } else {
            Ok(type_repr_id)
        }
    }

    fn enum_body(&mut self) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();
        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<ExprID> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            if self.did_match(TokenKind::Case)? {
                while {
                    let tok = self.push_source_location();
                    let name = self.identifier()?;
                    let mut types = vec![];

                    if self.did_match(TokenKind::LeftParen)? {
                        while !self.did_match(TokenKind::RightParen)? {
                            types.push(self.type_repr(false)?);
                            self.consume(TokenKind::Comma).ok();
                        }
                    }

                    let item = self.add_expr(Expr::EnumVariant(Name::Raw(name), types), tok)?;
                    items.push(item);
                    self.did_match(TokenKind::Comma)?
                } {}
            } else {
                let item = self.parse_with_precedence(Precedence::Assignment)?;
                items.push(item);
            };
        }

        self.add_expr(Expr::Block(items), tok)
    }

    pub(crate) fn block(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();

        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<ExprID> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            items.push(self.parse_with_precedence(Precedence::Assignment)?)
        }

        self.add_expr(Expr::Block(items), tok)
    }

    pub(crate) fn array_literal(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::LeftBracket)?;
        self.skip_newlines();

        let mut items = vec![];
        while !self.did_match(TokenKind::RightBracket)? {
            items.push(self.parse_with_precedence(Precedence::None)?);
            self.consume(TokenKind::Comma).ok();
        }

        self.add_expr(Expr::LiteralArray(items), tok)
    }

    pub(crate) fn variable(&mut self, can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        let name = self.identifier()?;
        let variable = self.add_expr(Variable(Name::Raw(name.to_string()), None), tok)?;

        self.skip_newlines();

        let var = if let Some(call_id) = self.check_call(variable, can_assign)? {
            call_id
        } else {
            variable
        };

        if can_assign && self.did_match(TokenKind::Equals)? {
            let tok = self.push_source_location();
            let rhs = self.parse_with_precedence(Precedence::Assignment)?;
            self.add_expr(Expr::Assignment(var, rhs), tok)
        } else {
            Ok(var)
        }
    }

    pub(crate) fn call_infix(
        &mut self,
        can_assign: bool,
        callee: ExprID,
    ) -> Result<ExprID, ParserError> {
        self.call(can_assign, vec![], callee)
    }

    pub(crate) fn call(
        &mut self,
        _can_assign: bool,
        type_args: Vec<ExprID>,
        callee: ExprID,
    ) -> Result<ExprID, ParserError> {
        let tok = self.push_lhs_location(callee);
        self.skip_newlines();
        let mut args: Vec<ExprID> = vec![];

        if !self.did_match(TokenKind::RightParen)? {
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
                    self.consume(TokenKind::Colon)?;
                    let value = self.parse_with_precedence(Precedence::Assignment)?;
                    args.push(self.add_expr(
                        Expr::CallArg {
                            label: Some(Name::Raw(label)),
                            value,
                        },
                        tok,
                    )?)
                } else {
                    let value = self.parse_with_precedence(Precedence::Assignment)?;
                    args.push(self.add_expr(Expr::CallArg { label: None, value }, tok)?);
                }

                self.did_match(TokenKind::Comma)?
            } {}

            self.consume(TokenKind::RightParen)?;
        }

        self.add_expr(
            Expr::Call {
                callee,
                type_args,
                args,
            },
            tok,
        )
    }

    pub(crate) fn unary(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        let op = self.consume_any(vec![TokenKind::Minus, TokenKind::Bang])?;
        let current_precedence = Precedence::handler(&Some(op.clone()))?.precedence;
        let rhs = self.parse_with_precedence(current_precedence + 1)?;

        self.add_expr(Unary(op.kind, rhs), tok)
    }

    pub(crate) fn binary(&mut self, _can_assign: bool, lhs: ExprID) -> Result<ExprID, ParserError> {
        let tok = self.push_lhs_location(lhs);

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
        let rhs = self.parse_with_precedence(current_precedence + 1)?;

        self.add_expr(Binary(lhs, op.kind, rhs), tok)
    }

    pub fn parse_with_precedence(&mut self, precedence: Precedence) -> Result<ExprID, ParserError> {
        log::trace!(
            "Parsing {:?} with precedence: {:?}",
            self.current,
            precedence
        );

        self.skip_newlines();

        let mut lhs: Option<ExprID> = None;
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
                    lhs = Some(infix(self, precedence.can_assign(), previous_lhs)?);
                }
            } else {
                break;
            }

            if self.did_match(TokenKind::Newline)? {
                break;
            }

            if i > 100 {
                self.advance();
                return Err(ParserError::UnknownError(format!(
                    "Infinite loop detected at: {:?}",
                    self.current.clone()
                )));
            }
        }

        #[allow(clippy::expect_fun_call)]
        if let Some(lhs) = lhs {
            Ok(lhs)
        } else {
            self.advance();
            Err(ParserError::UnexpectedEndOfInput(None))
        }
    }

    // MARK: Helpers

    pub(super) fn type_reprs(&mut self) -> Result<Vec<ExprID>, ParserError> {
        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                generics.push(self.type_repr(true)?);
                self.consume(TokenKind::Comma).ok();
            }
        };
        Ok(generics)
    }

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

    // Try to get an identifier. If it's a match, return it, otherwise return None
    pub(super) fn try_identifier(&mut self) -> Option<(String, Token)> {
        self.skip_semicolons_and_newlines();

        if let Some(current) = self.current.clone()
            && let TokenKind::Identifier(ref name) = current.kind
        {
            self.push_identifier(current.clone());
            self.advance();
            return Some((name.to_string(), current));
        };

        None
    }

    pub(super) fn peek_is(&self, expected: TokenKind) -> bool {
        if let Some(Token { kind: actual, .. }) = &self.current {
            *actual == expected
        } else {
            false
        }
    }

    pub(super) fn check_call(
        &mut self,
        callee: ExprID,
        can_assign: bool,
    ) -> Result<Option<ExprID>, ParserError> {
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
            let mut generics = vec![];
            while !self.did_match(TokenKind::Greater)? {
                self.skip_newlines();
                generics.push(self.type_repr(false)?);
                self.consume(TokenKind::Comma).ok();
                self.skip_newlines();
            }

            self.consume(TokenKind::LeftParen)?;

            return Ok(Some(self.call(can_assign, generics, callee)?));
        }

        if self.did_match(TokenKind::LeftParen)? {
            self.skip_newlines();
            return Ok(Some(self.call(can_assign, vec![], callee)?));
        }

        Ok(None)
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

    // Try to get a specific token. If it's not a match, return an error.
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

        Err(ParserError::UnexpectedToken(
            format!("Expected {expected:?}"),
            self.current.clone(),
        ))
    }

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
                    Err(ParserError::UnexpectedToken(
                        format!("{possible_tokens:?}"),
                        Some(current),
                    ))
                }
            }
            None => Err(ParserError::UnexpectedEndOfInput(Some(possible_tokens))),
        }
    }
}
