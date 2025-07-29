use std::path::PathBuf;
use tracing::info_span;

use crate::{
    SourceFile,
    compiling::compilation_session::SharedCompilationSession,
    diagnostic::Diagnostic,
    environment::Environment,
    expr_id::ExprID,
    expr_meta::ExprMeta,
    lexer::Lexer,
    parsed_expr::{self, Expr::*, IncompleteExpr, ParsedExpr, Pattern},
    token::Token,
    token_kind::TokenKind,
};

use super::{name::Name, precedence::Precedence};

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

pub fn parse(code: &str, file_path: PathBuf) -> SourceFile {
    let lexer = Lexer::new(code);
    let mut env = Environment::default();
    let session = SharedCompilationSession::default();
    let mut parser = Parser::new(session.clone(), lexer, file_path, &mut env);

    parser.parse();
    parser.parse_tree
}

#[cfg(test)]
pub fn parse_with_comments(code: &str) -> SourceFile {
    let lexer = Lexer::preserving_comments(code);
    let mut env = Environment::default();
    let mut parser = Parser::new(
        SharedCompilationSession::default(),
        lexer,
        PathBuf::from("-"),
        &mut env,
    );

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
    let session = SharedCompilationSession::default();
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
        let _s = info_span!("parsing", path = self.parse_tree.path.to_str()).entered();
        // Prime the pump
        self.advance();
        self.advance();
        self.skip_newlines();

        while let Some(current) = self.current.clone() {
            self.skip_semicolons_and_newlines();

            if current.kind == TokenKind::EOF {
                return;
            }

            tracing::trace!("{current:?}");

            match self.parse_with_precedence(Precedence::Assignment) {
                Ok(expr) => self.parse_tree.push_root(expr),
                Err(err) => {
                    tracing::error!("{}", err.message());
                    self.add_diagnostic(Diagnostic::parser(
                        self.parse_tree.path.clone(),
                        current.span(),
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
        tracing::trace!("Recovering parser: {:?}", self.current);

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

        self.current = self.next.take();
        self.next = self.lexer.next().ok();
        self.previous.clone()
    }

    pub(super) fn save_meta(&mut self, _loc: LocToken) -> Result<ExprID, ParserError> {
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

        let next_id = self.env.next_expr_id();

        self.parse_tree.add(next_id, expr_meta);

        Ok(next_id)
    }

    fn push_identifier(&mut self, identifier: Token) {
        if let Some(loc) = self.source_location_stack.last_mut() {
            loc.identifiers.push(identifier);
        }
    }

    #[must_use]
    #[allow(clippy::unwrap_used)]
    fn push_lhs_location(&mut self, lhs: ExprID) -> LocToken {
        #[allow(clippy::unwrap_used)]
        let meta = self.parse_tree.meta.borrow();
        let meta = meta.get(&lhs).unwrap();
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

    // MARK: Expr parsers

    pub(crate) fn protocol_expr(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Protocol)?;
        let name = Name::Raw(self.identifier()?);
        let associated_types = self.type_reprs()?;
        let conformances = self.conformances()?;
        let body = self.protocol_body()?;
        let id = self.save_meta(tok)?;

        Ok(ParsedExpr {
            id,
            expr: parsed_expr::Expr::ProtocolDecl {
                name,
                associated_types,
                conformances,
                body: Box::new(body),
            },
        })
    }

    fn conformances(&mut self) -> Result<Vec<ParsedExpr>, ParserError> {
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

    pub(crate) fn struct_expr(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Struct)?;

        let Some((name_str, _)) = self.try_identifier() else {
            return Err(ParserError::ExpectedIdentifier(self.current.clone()));
        };

        let generics = self.type_reprs()?;
        let conformances = self.conformances()?;
        let body = Box::new(self.struct_body()?);
        let id = self.save_meta(tok)?;

        Ok(ParsedExpr {
            id,
            expr: Struct {
                name: Name::Raw(name_str),
                generics,
                conformances,
                body,
            },
        })
    }

    pub(crate) fn import_expr(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Import)?;
        let name = self.identifier()?;
        self.add_expr(Import(name.to_string()), tok)
    }

    pub(crate) fn extend_expr(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Extend)?;

        let Some((name_str, _)) = self.try_identifier() else {
            return Err(ParserError::ExpectedIdentifier(self.current.clone()));
        };

        let generics = self.type_reprs()?;
        let conformances = self.conformances()?;
        let body = Box::new(self.extend_body()?);
        let id = self.save_meta(tok)?;

        Ok(ParsedExpr {
            id,
            expr: Extend {
                name: Name::Raw(name_str),
                generics,
                conformances,
                body,
            },
        })
    }

    fn struct_body(&mut self) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();
        tracing::info!("in struct body: {:?}", self.current);
        self.consume(TokenKind::LeftBrace)?;
        self.skip_semicolons_and_newlines();

        let mut members: Vec<ParsedExpr> = vec![];

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

        let id = self.save_meta(tok)?;

        Ok(ParsedExpr {
            id,
            expr: Block(members),
        })
    }

    fn extend_body(&mut self) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();
        self.consume(TokenKind::LeftBrace)?;
        self.skip_semicolons_and_newlines();

        let mut members: Vec<ParsedExpr> = vec![];

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

        self.add_expr(Block(members), tok)
    }

    fn protocol_body(&mut self) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();
        self.consume(TokenKind::LeftBrace)?;

        let mut members: Vec<ParsedExpr> = vec![];

        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_semicolons_and_newlines();
            tracing::info!("in struct body: {:?}", self.current);
            match self.current {
                some_kind!(Let) => {
                    members.push(self.property()?);
                }
                some_kind!(Init) => members.push(self.init()?),
                some_kind!(Func) => {
                    let tok = self.push_source_location();
                    let func_requirement = self.func_requirement()?;
                    let FuncSignature {
                        name,
                        params,
                        generics,
                        ret,
                    } = &func_requirement.expr
                    else {
                        return Err(ParserError::UnknownError(format!(
                            "Did not get protocol func requirement: {:?}",
                            self.current.clone()
                        )));
                    };

                    // See if we have a default implementation
                    if self.peek_is(TokenKind::LeftBrace) {
                        let body = Box::new(self.block(false)?);

                        let func = Func {
                            name: Some(name.clone()),
                            generics: generics.clone(),
                            params: params.clone(),
                            body,
                            ret: Some(ret.clone()),
                            captures: vec![],
                            attributes: vec![],
                        };

                        members.push(self.add_expr(func, tok)?);
                    } else {
                        members.push(self.add_expr(func_requirement.expr.clone(), tok)?)
                    }
                }
                _ => {
                    members.push(self.parse_with_precedence(Precedence::Assignment)?);
                }
            }

            self.skip_semicolons_and_newlines();
        }

        self.add_expr(Block(members), tok)
    }

    pub(crate) fn init(&mut self) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        let func_id = Box::new(self.func(vec![])?);
        self.add_expr(Init(None, func_id), tok)
    }

    pub(crate) fn property(&mut self) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Let)?;
        let name = self.identifier()?;
        let type_repr = if self.did_match(TokenKind::Colon)? {
            Some(Box::new(self.type_repr(false)?))
        } else {
            None
        };
        let default_value = if self.did_match(TokenKind::Equals)? {
            Some(Box::new(
                self.parse_with_precedence(Precedence::Assignment)?,
            ))
        } else {
            None
        };

        self.add_expr(
            Property {
                name: Name::Raw(name),
                type_repr,
                default_value,
            },
            tok,
        )
    }

    pub(crate) fn enum_decl(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Enum)?;
        self.skip_semicolons_and_newlines();

        let name = self.identifier()?;
        let generics = self.type_reprs()?;
        let conformances = self.conformances()?;

        // Consume the block
        let body = Box::new(self.enum_body()?);

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

    pub(crate) fn break_expr(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Break)?;
        self.add_expr(Break, tok)
    }

    pub(crate) fn return_expr(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Return)?;

        if self.peek_is(TokenKind::Newline) || self.peek_is(TokenKind::RightBrace) {
            return self.add_expr(Return(None), tok);
        }

        let rhs = Box::new(self.parse_with_precedence(Precedence::None)?);
        self.add_expr(Return(Some(rhs)), tok)
    }

    pub(crate) fn attribute(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        self.attributed_expr(vec![])
    }

    pub(crate) fn attributed_expr(
        &mut self,
        mut attributes: Vec<ParsedExpr>,
    ) -> Result<ParsedExpr, ParserError> {
        let attribute = self.parse_attribute()?;
        attributes.push(attribute);

        self.skip_newlines();

        let Some(current) = &self.current else {
            return Err(ParserError::UnexpectedEndOfInput(None));
        };

        match current.kind {
            TokenKind::At => self.attributed_expr(attributes),
            TokenKind::Struct => {
                // TODO: Actually save attributes on struct
                self.struct_expr(false)
            }
            TokenKind::Func => {
                self.consume(TokenKind::Func)?;
                self.func(attributes)
            }
            _ => Err(ParserError::UnknownError(format!(
                "Expr does not support attributes: {}",
                current.as_str()
            ))),
        }
    }

    fn parse_attribute(&mut self) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::At)?;
        let name = self.identifier()?;
        self.add_expr(Attribute(Name::Raw(name)), tok)
    }

    pub(crate) fn match_expr(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Match)?;

        let target = Box::new(self.parse_with_precedence(Precedence::Assignment)?);
        let body = self.match_block()?;

        self.add_expr(Match(target, body), tok)
    }

    fn match_block(&mut self) -> Result<Vec<ParsedExpr>, ParserError> {
        self.skip_semicolons_and_newlines();
        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<ParsedExpr> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            let tok = self.push_source_location();
            let pattern = self.parse_match_pattern()?;
            let pattern_id = Box::new(self.add_expr(ParsedPattern(pattern), tok)?);
            self.consume(TokenKind::Arrow)?;
            let tok = self.push_source_location();
            let body = Box::new(self.parse_with_precedence(Precedence::Primary)?);
            items.push(self.add_expr(MatchArm(pattern_id, body), tok)?);
            self.consume(TokenKind::Comma).ok();
            self.skip_semicolons_and_newlines();
        }

        Ok(items)
    }

    pub(super) fn parse_match_pattern(&mut self) -> Result<Pattern, ParserError> {
        self.skip_semicolons_and_newlines();
        tracing::trace!("parse_match_pattern: current token = {:?}", self.current);

        if self.did_match(TokenKind::Underscore)? {
            return Ok(Pattern::Wildcard);
        }

        if let Some(Token { kind, .. }) = self.current.clone() {
            match kind {
                TokenKind::Int(value) => {
                    self.advance();
                    return Ok(Pattern::LiteralInt(value));
                }
                TokenKind::Float(value) => {
                    self.advance();
                    return Ok(Pattern::LiteralFloat(value));
                }
                TokenKind::True => {
                    self.advance();
                    return Ok(Pattern::LiteralTrue);
                }
                TokenKind::False => {
                    self.advance();
                    return Ok(Pattern::LiteralFalse);
                }

                _ => (),
            }
        }
        
        // Check for unqualified struct pattern: { field1, field2 }
        if self.peek_is(TokenKind::LeftBrace) {
            self.consume(TokenKind::LeftBrace)?;
            let mut fields: Vec<(Name, ParsedExpr)> = vec![];
            let mut rest = false;
            
            while !self.did_match(TokenKind::RightBrace)? {
                // Check for .. pattern
                if self.did_match(TokenKind::DotDot)? {
                    rest = true;
                    // Check if there's a comma after ..
                    self.did_match(TokenKind::Comma)?;
                    // .. should be the last thing in the pattern
                    if !self.peek_is(TokenKind::RightBrace) {
                        return Err(ParserError::UnknownError(".. must be the last element in struct pattern".into()));
                    }
                    break;
                }
                
                // Parse field name
                let field_name = self.identifier()?;
                
                // Check if there's an explicit pattern after colon
                let pattern = if self.did_match(TokenKind::Colon)? {
                    // Field: pattern
                    let tok = self.push_source_location();
                    let pattern = self.parse_match_pattern()?;
                    self.add_expr(ParsedPattern(pattern), tok)?
                } else {
                    // Shorthand: field name is also the binding
                    let tok = self.push_source_location();
                    let pattern = Pattern::Bind(Name::Raw(field_name.clone()));
                    self.add_expr(ParsedPattern(pattern), tok)?
                };
                
                fields.push((Name::Raw(field_name), pattern));
                
                // Skip comma if present
                self.did_match(TokenKind::Comma)?;
                self.skip_semicolons_and_newlines();
            }
            
            // We already consume the right brace in the while loop condition
            let (field_names, field_patterns): (Vec<_>, Vec<_>) = fields.into_iter().unzip();
            return Ok(Pattern::Struct {
                struct_name: None,
                fields: field_patterns,
                field_names,
                rest,
            });
        }

        if let Ok(name) = self.identifier() {
            // Check if it's a struct pattern: Name { fields }
            if self.peek_is(TokenKind::LeftBrace) {
                self.consume(TokenKind::LeftBrace)?;
                let mut fields: Vec<(Name, ParsedExpr)> = vec![];
                let mut rest = false;
                
                while !self.did_match(TokenKind::RightBrace)? {
                    // Check for .. pattern
                    if self.did_match(TokenKind::DotDot)? {
                        rest = true;
                        // Check if there's a comma after ..
                        self.did_match(TokenKind::Comma)?;
                        // .. should be the last thing in the pattern
                        if !self.peek_is(TokenKind::RightBrace) {
                            return Err(ParserError::UnknownError(".. must be the last element in struct pattern".into()));
                        }
                        // Continue to consume the right brace
                        continue;
                    }
                    
                    // Parse field name
                    let field_name = self.identifier()?;
                    
                    // Check if there's an explicit pattern after colon
                    let pattern = if self.did_match(TokenKind::Colon)? {
                        // Field: pattern
                        let tok = self.push_source_location();
                        let pattern = self.parse_match_pattern()?;
                        self.add_expr(ParsedPattern(pattern), tok)?
                    } else {
                        // Shorthand: field name is also the binding
                        let tok = self.push_source_location();
                        let pattern = Pattern::Bind(Name::Raw(field_name.clone()));
                        self.add_expr(ParsedPattern(pattern), tok)?
                    };
                    
                    fields.push((Name::Raw(field_name), pattern));
                    
                    // Skip comma if present
                    self.did_match(TokenKind::Comma)?;
                    self.skip_semicolons_and_newlines();
                }
                
                let (field_names, field_patterns): (Vec<_>, Vec<_>) = fields.into_iter().unzip();
                return Ok(Pattern::Struct {
                    struct_name: Some(Name::Raw(name)),
                    fields: field_patterns,
                    field_names,
                    rest,
                });
            }
            
            // Check for enum variant pattern
            if !self.did_match(TokenKind::Dot)? {
                return Ok(Pattern::Bind(Name::Raw(name)));
            }

            let variant_name = self.identifier()?;
            let mut fields: Vec<ParsedExpr> = vec![];
            if self.did_match(TokenKind::LeftParen)? {
                while !self.did_match(TokenKind::RightParen)? {
                    let tok = self.push_source_location();
                    let pattern = self.parse_match_pattern()?;
                    fields.push(self.add_expr(ParsedPattern(pattern), tok)?);
                }
            }

            return Ok(Pattern::Variant {
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

            tracing::debug!("unqualified variant");

            let mut fields: Vec<ParsedExpr> = vec![];
            if self.did_match(TokenKind::LeftParen)? {
                while !self.did_match(TokenKind::RightParen)? {
                    tracing::trace!("adding arg: {:?}", self.current);
                    let tok = self.push_source_location();
                    let pattern = self.parse_match_pattern()?;
                    fields.push(self.add_expr(ParsedPattern(pattern), tok)?);
                }
            }

            return Ok(Pattern::Variant {
                enum_name: None,
                variant_name,
                fields,
            });
        }

        Err(ParserError::UnknownError("did not get match".into()))
    }

    pub(crate) fn member_prefix(&mut self, can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Dot)?;
        let name = self.identifier()?;

        let member = self.add_expr(Member(None, name), tok)?;
        if let Some(call_id) = self.check_call(&member, can_assign)? {
            Ok(call_id)
        } else {
            Ok(member)
        }
    }

    pub(crate) fn member_infix(
        &mut self,
        can_assign: bool,
        lhs: ParsedExpr,
    ) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_lhs_location(lhs.id);
        self.consume(TokenKind::Dot)?;

        let name = match self.identifier() {
            Ok(name) => name,
            Err(_) => {
                let incomplete_member = Incomplete(IncompleteExpr::Member(Some(Box::new(lhs))));
                return self.add_expr(incomplete_member, tok);
            }
        };

        let member = self.add_expr(Member(Some(Box::new(lhs)), name), tok)?;

        self.skip_semicolons_and_newlines();

        let expr = if let Some(call_expr) = self.check_call(&member, can_assign)? {
            call_expr
        } else {
            member
        };

        if self.did_match(TokenKind::Equals)? {
            if can_assign {
                let loc = self.push_source_location();
                let rhs = self.parse_with_precedence(Precedence::Assignment)?;
                return self.add_expr(Assignment(Box::new(expr), Box::new(rhs)), loc);
            } else {
                return Err(ParserError::CannotAssign);
            }
        }

        Ok(expr)
    }

    pub(crate) fn boolean(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();

        if self.did_match(TokenKind::True)? {
            return self.add_expr(LiteralTrue, tok);
        }

        if self.did_match(TokenKind::False)? {
            return self.add_expr(LiteralFalse, tok);
        }

        Err(ParserError::UnknownError("did not get bool".into()))
    }

    pub(crate) fn if_expr(&mut self, can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();

        self.consume(TokenKind::If)?;

        let condition = Box::new(self.parse_with_precedence(Precedence::Assignment)?);
        let body = Box::new(self.block(can_assign)?);

        if self.did_match(TokenKind::Else)? {
            let else_body = Box::new(self.block(can_assign)?);
            self.add_expr(If(condition, body, Some(else_body)), tok)
        } else {
            self.add_expr(If(condition, body, None), tok)
        }
    }

    pub(crate) fn loop_expr(&mut self, can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();

        self.consume(TokenKind::Loop)?;

        let mut condition = None;
        if !self.peek_is(TokenKind::LeftBrace) {
            condition = Some(Box::new(self.parse_with_precedence(Precedence::None)?))
        }

        let body = Box::new(self.block(can_assign)?);

        self.add_expr(Loop(condition, body), tok)
    }

    pub(crate) fn tuple(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
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

    pub(crate) fn let_expr(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();

        // Consume the `let` keyword
        self.advance();
        let name = self.identifier()?;

        let type_repr = if self.did_match(TokenKind::Colon)? {
            Some(Box::new(self.type_repr(false)?))
        } else {
            None
        };

        let let_expr = self.add_expr(Let(Name::Raw(name), type_repr), tok)?;

        if self.did_match(TokenKind::Equals)? {
            let tok = self.push_source_location();
            let rhs = Box::new(self.parse_with_precedence(Precedence::Assignment)?);
            self.add_expr(Assignment(Box::new(let_expr), rhs), tok)
        } else {
            Ok(let_expr)
        }
    }

    pub(crate) fn literal(&mut self, can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();

        self.advance();

        let prev = &self
            .previous
            .as_ref()
            .map(|p| p.kind.clone())
            .ok_or(ParserError::UnexpectedEndOfInput(None))?;

        let expr = match prev {
            TokenKind::Int(val) => self.add_expr(LiteralInt(val.clone()), tok),
            TokenKind::Float(val) => self.add_expr(LiteralFloat(val.clone()), tok),
            TokenKind::StringLiteral(val) => self.add_expr(LiteralString(val.to_string()), tok),
            TokenKind::Func => self.func(vec![]),
            _ => return Err(ParserError::UnknownError("did not get literal".into())),
        }?;

        if let Some(call_id) = self.check_call(&expr, can_assign)? {
            Ok(call_id)
        } else {
            Ok(expr)
        }
    }

    pub(crate) fn func_requirement(&mut self) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
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

        let ret = Box::new(self.type_repr(false)?);

        self.add_expr(
            FuncSignature {
                name,
                params,
                generics,
                ret,
            },
            tok,
        )
    }

    pub(crate) fn func(&mut self, attributes: Vec<ParsedExpr>) -> Result<ParsedExpr, ParserError> {
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

        match self.consume(TokenKind::LeftParen) {
            Ok(_) => (),
            Err(e) => {
                self.add_diagnostic(Diagnostic::parser(
                    self.parse_tree.path.clone(),
                    self.current.as_ref().map(|c| c.span()).unwrap_or_default(),
                    e,
                ));
                let incomplete_func = IncompleteExpr::Func {
                    name: name.map(|n| Name::Raw(n.into())),
                    params: None,
                    generics: None,
                    ret: None,
                    body: None,
                };

                return self.add_expr(Incomplete(incomplete_func), tok);
            }
        }

        let params = self.parameter_list()?;

        match self.consume(TokenKind::RightParen) {
            Ok(_) => (),
            Err(e) => {
                self.add_diagnostic(Diagnostic::parser(
                    self.parse_tree.path.clone(),
                    self.current.as_ref().map(|c| c.span()).unwrap_or_default(),
                    e,
                ));
                let incomplete_func = IncompleteExpr::Func {
                    name: name.map(|n| Name::Raw(n.into())),
                    params: Some(params),
                    generics: None,
                    ret: None,
                    body: None,
                };

                return self.add_expr(Incomplete(incomplete_func), tok);
            }
        }

        let ret = if self.did_match(TokenKind::Arrow)? {
            Some(Box::new(self.type_repr(false)?))
        } else {
            None
        };

        let body = match self.block(false) {
            Ok(body) => Box::new(body),
            Err(e) => {
                self.add_diagnostic(Diagnostic::parser(
                    self.parse_tree.path.clone(),
                    self.current.as_ref().map(|c| c.span()).unwrap_or_default(),
                    e,
                ));
                let incomplete_func = IncompleteExpr::Func {
                    name: name.map(|n| Name::Raw(n.into())),
                    params: Some(params),
                    generics: Some(generics),
                    ret,
                    body: None,
                };

                return self.add_expr(Incomplete(incomplete_func), tok);
            }
        };

        let func_id = self.add_expr(
            Func {
                name: name.map(|s| s.to_string()).map(Name::Raw),
                generics,
                params,
                body,
                ret,
                captures: vec![],
                attributes,
            },
            tok,
        )?;

        if let Some(call_id) = self.check_call(&func_id, false)? {
            Ok(call_id)
        } else {
            Ok(func_id)
        }
    }

    fn parameter_list(&mut self) -> Result<Vec<ParsedExpr>, ParserError> {
        let mut params: Vec<ParsedExpr> = vec![];
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
                Some(Box::new(self.type_repr(false)?))
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

    fn type_repr(&mut self, is_type_parameter: bool) -> Result<ParsedExpr, ParserError> {
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
                return self.add_expr(
                    FuncTypeRepr(sig_args, Box::new(ret), is_type_parameter),
                    tok,
                );
            } else {
                return self.add_expr(TupleTypeRepr(sig_args, is_type_parameter), tok);
            }
        }

        // Check for record type: {x: Int, y: Int, ..R}
        if self.did_match(TokenKind::LeftBrace)? {
            return self.record_type_repr(is_type_parameter, tok);
        }

        // Check for row variable: ..R
        if self.did_match(TokenKind::DotDot)? {
            let name = self.identifier()?;
            return self.add_expr(RowVariable(Name::Raw(name)), tok);
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

    fn enum_body(&mut self) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();
        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<ParsedExpr> = vec![];
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

                    let item = self.add_expr(EnumVariant(Name::Raw(name), types), tok)?;
                    items.push(item);
                    self.did_match(TokenKind::Comma)?
                } {}
            } else {
                let item = self.parse_with_precedence(Precedence::Assignment)?;
                items.push(item);
            };
        }

        self.add_expr(Block(items), tok)
    }

    pub(crate) fn block(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();

        self.consume(TokenKind::LeftBrace)?;

        // Check if this might be a record literal by looking ahead
        if self.peek_is_record_literal() {
            return self.record_literal_body(tok);
        }

        let mut items: Vec<ParsedExpr> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            items.push(self.parse_with_precedence(Precedence::Assignment)?)
        }

        self.add_expr(Block(items), tok)
    }

    fn peek_is_record_literal(&mut self) -> bool {
        // Record literals have the pattern: { identifier: expr, ... }
        // or { ...expr, ... }
        // Look for identifier followed by colon, or DotDotDot
        // Empty braces {} are always blocks, not records
        self.skip_newlines();

        match &self.current {
            Some(Token {
                kind: TokenKind::Identifier(_),
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

    fn record_literal_body(&mut self, tok: LocToken) -> Result<ParsedExpr, ParserError> {
        let mut fields: Vec<ParsedExpr> = vec![];

        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_newlines();

            if self.peek_is(TokenKind::DotDotDot) {
                // Spread syntax: ...expr
                self.consume(TokenKind::DotDotDot)?;
                let spread_tok = self.push_source_location();
                let expr = self.parse_with_precedence(Precedence::Assignment)?;
                fields.push(self.add_expr(Spread(Box::new(expr)), spread_tok)?);
            } else {
                // Regular field: label: expr
                let field_tok = self.push_source_location();
                let label = self.identifier()?;
                self.consume(TokenKind::Colon)?;
                let value = self.parse_with_precedence(Precedence::Assignment)?;
                fields.push(self.add_expr(
                    RecordField {
                        label: Name::Raw(label),
                        value: Box::new(value),
                    },
                    field_tok,
                )?);
            }

            // Handle comma
            if !self.peek_is(TokenKind::RightBrace) {
                self.consume(TokenKind::Comma)?;
            } else {
                self.consume(TokenKind::Comma).ok(); // Optional trailing comma
            }
            self.skip_newlines();
        }

        self.add_expr(RecordLiteral(fields), tok)
    }

    fn record_type_repr(
        &mut self,
        is_type_parameter: bool,
        tok: LocToken,
    ) -> Result<ParsedExpr, ParserError> {
        let mut fields: Vec<ParsedExpr> = vec![];
        let mut row_var: Option<Box<ParsedExpr>> = None;

        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_newlines();

            // Check for row variable: ..R
            if self.did_match(TokenKind::DotDot)? {
                let row_tok = self.push_source_location();
                let name = self.identifier()?;
                row_var = Some(Box::new(
                    self.add_expr(RowVariable(Name::Raw(name)), row_tok)?,
                ));

                // Row variable should be the last element
                self.consume(TokenKind::Comma).ok();
                self.skip_newlines();
                self.consume(TokenKind::RightBrace)?;
                break;
            }

            // Regular field: label: Type
            let field_tok = self.push_source_location();
            let label = self.identifier()?;
            self.consume(TokenKind::Colon)?;
            let ty = self.type_repr(false)?; // Fields are not type parameters
            fields.push(self.add_expr(
                RecordTypeField {
                    label: Name::Raw(label),
                    ty: Box::new(ty),
                },
                field_tok,
            )?);

            // Handle comma
            if !self.peek_is(TokenKind::RightBrace) && !self.peek_is(TokenKind::DotDot) {
                self.consume(TokenKind::Comma)?;
            } else {
                self.consume(TokenKind::Comma).ok(); // Optional trailing comma
            }
            self.skip_newlines();
        }

        self.add_expr(
            RecordTypeRepr {
                fields,
                row_var,
                introduces_type: is_type_parameter,
            },
            tok,
        )
    }

    pub(crate) fn array_literal(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::LeftBracket)?;
        self.skip_newlines();

        let mut items = vec![];
        while !self.did_match(TokenKind::RightBracket)? {
            items.push(self.parse_with_precedence(Precedence::None)?);
            self.consume(TokenKind::Comma).ok();
        }

        self.add_expr(LiteralArray(items), tok)
    }

    pub(crate) fn variable(&mut self, can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        let name = self.identifier()?;
        let variable = self.add_expr(Variable(Name::Raw(name.to_string())), tok)?;

        self.skip_newlines();

        let var = if let Some(call_expr) = self.check_call(&variable, can_assign)? {
            call_expr
        } else {
            variable
        };

        if can_assign && self.did_match(TokenKind::Equals)? {
            let tok = self.push_source_location();
            let rhs = Box::new(self.parse_with_precedence(Precedence::Assignment)?);
            self.add_expr(Assignment(Box::new(var), rhs), tok)
        } else {
            Ok(var)
        }
    }

    pub(crate) fn call_infix(
        &mut self,
        can_assign: bool,
        callee: ParsedExpr,
    ) -> Result<ParsedExpr, ParserError> {
        self.call(can_assign, vec![], callee)
    }

    pub(crate) fn call(
        &mut self,
        _can_assign: bool,
        type_args: Vec<ParsedExpr>,
        callee: ParsedExpr,
    ) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_lhs_location(callee.id);
        self.skip_newlines();
        let mut args: Vec<ParsedExpr> = vec![];

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
                    let value = Box::new(self.parse_with_precedence(Precedence::Assignment)?);
                    args.push(self.add_expr(
                        CallArg {
                            label: Some(Name::Raw(label)),
                            value,
                        },
                        tok,
                    )?)
                } else {
                    let value = Box::new(self.parse_with_precedence(Precedence::Assignment)?);
                    args.push(self.add_expr(CallArg { label: None, value }, tok)?);
                }

                self.did_match(TokenKind::Comma)?
            } {}

            self.consume(TokenKind::RightParen)?;
        }

        self.add_expr(
            Call {
                callee: Box::new(callee),
                type_args,
                args,
            },
            tok,
        )
    }

    pub(crate) fn unary(&mut self, _can_assign: bool) -> Result<ParsedExpr, ParserError> {
        let tok = self.push_source_location();
        let op = self.consume_any(vec![TokenKind::Minus, TokenKind::Bang])?;
        let current_precedence = Precedence::handler(&Some(op.clone()))?.precedence;
        let rhs = Box::new(self.parse_with_precedence(current_precedence)?);

        self.add_expr(Unary(op.kind, rhs), tok)
    }

    pub(crate) fn binary(
        &mut self,
        _can_assign: bool,
        lhs: ParsedExpr,
    ) -> Result<ParsedExpr, ParserError> {
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
        let rhs = Box::new(self.parse_with_precedence(current_precedence)?);

        self.add_expr(Binary(Box::new(lhs), op.kind, rhs), tok)
    }

    pub fn parse_with_precedence(
        &mut self,
        precedence: Precedence,
    ) -> Result<ParsedExpr, ParserError> {
        tracing::trace!(
            "Parsing {:?} with precedence: {:?}",
            self.current,
            precedence
        );

        self.skip_newlines();

        let mut lhs: Option<ParsedExpr> = None;
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

    pub(super) fn type_reprs(&mut self) -> Result<Vec<ParsedExpr>, ParserError> {
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
        callee: &ParsedExpr,
        can_assign: bool,
    ) -> Result<Option<ParsedExpr>, ParserError> {
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

            return Ok(Some(self.call(can_assign, generics, callee.clone())?));
        }

        if self.did_match(TokenKind::LeftParen)? {
            self.skip_newlines();
            return Ok(Some(self.call(can_assign, vec![], callee.clone())?));
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

    fn add_expr(
        &mut self,
        expr: parsed_expr::Expr,
        tok: LocToken,
    ) -> Result<ParsedExpr, ParserError> {
        let id = self.save_meta(tok)?;
        Ok(ParsedExpr { id, expr })
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
