use crate::{
    FileID, SourceFile, diagnostic::Diagnostic, lexer::Lexer, token::Token, token_kind::TokenKind,
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
    previous_before_newline: Option<Token>,
}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum ParserError {
    UnexpectedToken(String /* expected */, Option<Token> /* actual */),
    UnexpectedEndOfInput(Option<Vec<TokenKind>> /* expected */),
    UnknownError(&'static str),
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

pub fn parse(code: &str, file_id: FileID) -> SourceFile {
    let lexer = Lexer::new(code);
    let mut parser = Parser::new(lexer, file_id);

    parser.parse();
    parser.parse_tree
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>, file_id: FileID) -> Self {
        Self {
            lexer,
            previous: None,
            current: None,
            next: None,
            parse_tree: SourceFile::new(file_id),
            source_location_stack: Default::default(),
            previous_before_newline: None,
        }
    }

    pub fn parse(&mut self) {
        // Prime the pump
        self.advance();
        self.advance();
        self.skip_newlines();

        while let Some(current) = self.current.clone() {
            self.skip_newlines();

            if current.kind == TokenKind::EOF {
                return;
            }

            log::trace!("{current:?}");

            match self.parse_with_precedence(Precedence::Assignment) {
                Ok(expr) => self.parse_tree.push_root(expr),
                Err(err) => {
                    log::error!("{}", err.message());
                    self.parse_tree
                        .diagnostics
                        .insert(Diagnostic::parser(current, err));
                    self.recover();
                }
            }

            self.skip_newlines();
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
        while {
            if let Some(token) = &self.current {
                token.kind == TokenKind::Newline
            } else {
                false
            }
        } {
            self.advance();
        }
    }

    fn advance(&mut self) -> Option<Token> {
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
            .unwrap_or_else(|| self.previous.clone().unwrap());
        let start = self
            .source_location_stack
            .pop()
            .unwrap_or_else(|| panic!("unbalanced source location stack. current: {token:?}"));
        log::trace!("pop location: {:?}", start.token);

        let expr_meta = ExprMeta {
            start: start.token,
            end: token,
            identifiers: start.identifiers,
        };

        Ok(self.parse_tree.add(expr, expr_meta))
    }

    fn push_identifier(&mut self, identifier: Token) {
        if let Some(loc) = self.source_location_stack.last_mut() {
            loc.identifiers.push(identifier);
        }
    }

    #[must_use]
    fn push_lhs_location(&mut self, lhs: ExprID) -> LocToken {
        let meta = &self.parse_tree.meta[lhs as usize];
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
        let start = SourceLocationStart {
            token: self.current.clone().unwrap(),
            identifiers: vec![],
        };
        self.source_location_stack.push(start);
        LocToken
    }

    // MARK: Expr parsers

    pub(crate) fn struct_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.consume(TokenKind::Struct)?;

        let Some((name_str, _)) = self.try_identifier() else {
            return Err(ParserError::ExpectedIdentifier(self.current.clone()));
        };
        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                generics.push(self.type_repr(true)?);
                self.consume(TokenKind::Comma).ok();
            }
        };

        let body = self.struct_body()?;
        self.add_expr(Struct(Name::Raw(name_str), generics, body), tok)
    }

    fn struct_body(&mut self) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();
        self.skip_newlines();
        self.consume(TokenKind::LeftBrace)?;

        let mut members: Vec<ExprID> = vec![];

        while !self.did_match(TokenKind::RightBrace)? {
            self.skip_newlines();
            log::info!("in struct body: {:?}", self.current);
            match self.current {
                some_kind!(Let) => {
                    members.push(self.property()?);
                }
                some_kind!(Init) => members.push(self.init()?),
                _ => {
                    members.push(self.parse_with_precedence(Precedence::Assignment)?);
                }
            }

            self.skip_newlines();
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
        self.skip_newlines();

        let (name, _) = self.try_identifier().unwrap();

        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                generics.push(self.type_repr(true)?);
                self.consume(TokenKind::Comma).ok();
            }
        };

        // Consume the block
        let body = self.enum_body()?;

        self.add_expr(EnumDecl(Name::Raw(name), generics, body), tok)
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
        self.skip_newlines();
        log::debug!("in match block");
        self.consume(TokenKind::LeftBrace)?;
        log::debug!("consumed left brace");

        let mut items: Vec<ExprID> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            let tok = self.push_source_location();
            let pattern = self.parse_match_pattern()?;
            log::trace!("parsed pattern: {pattern:?}");
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
        self.skip_newlines();

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

        if let Some((name, _)) = self.try_identifier() {
            // It's not an enum variant so it's a bind
            if !self.did_match(TokenKind::Dot)? {
                return Ok(expr::Pattern::Bind(Name::Raw(name)));
            }

            let Some((variant_name, _)) = self.try_identifier() else {
                return Err(ParserError::ExpectedIdentifier(self.current.clone()));
            };

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
        let (name, _) = self.try_identifier().unwrap();

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
        let name = self.identifier()?;
        let member = self.add_expr(Member(Some(lhs), name), tok)?;

        self.skip_newlines();

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
        if let Some(Token {
            kind: TokenKind::LeftBrace,
            ..
        }) = self.current
        {
        } else {
            condition = Some(self.parse_with_precedence(Precedence::Any)?)
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
            let rhs = self.parse_with_precedence(Precedence::None)?;
            self.add_expr(Expr::Assignment(let_expr?, rhs), tok)
        } else {
            let_expr
        }
    }

    pub(crate) fn literal(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let tok = self.push_source_location();

        self.advance();

        match &self
            .previous
            .as_ref()
            .expect("got into #literal without having a token")
            .kind
        {
            TokenKind::Int(val) => self.add_expr(LiteralInt(val.clone()), tok),
            TokenKind::Float(val) => self.add_expr(LiteralFloat(val.clone()), tok),
            TokenKind::Func => self.func(),
            _ => unreachable!("didn't get a literal"),
        }
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

        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                generics.push(self.type_repr(true)?);
                self.consume(TokenKind::Comma).ok();
            }
        };

        self.consume(TokenKind::LeftParen)?;

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

        let Some((name, _)) = self.try_identifier() else {
            return Err(ParserError::UnexpectedToken(
                "Identifer".into(),
                self.current.clone(),
            ));
        };

        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                let generic = self.type_repr(is_type_parameter)?;
                generics.push(generic);
                self.consume(TokenKind::Comma).ok();
            }
        }

        let type_repr = TypeRepr(name.into(), generics, is_type_parameter);
        let type_repr_id = self.add_expr(type_repr, tok)?;

        if self.did_match(TokenKind::QuestionMark)? {
            let tok = self.push_source_location();
            self.add_expr(
                TypeRepr(
                    Name::Raw("Optional".to_string()),
                    vec![type_repr_id],
                    is_type_parameter,
                ),
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
                    let (name, _) = self.try_identifier().expect("did not get enum case name");
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
        let (name, _) = self.try_identifier().unwrap();
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
                return Err(ParserError::UnknownError("Infinite loop detected"));
            }
        }

        #[allow(clippy::expect_fun_call)]
        if let Some(lhs) = lhs {
            Ok(lhs)
        } else {
            Err(ParserError::UnexpectedEndOfInput(None))
        }
    }

    // MARK: Helpers

    pub(super) fn identifier(&mut self) -> Result<String, ParserError> {
        self.skip_newlines();
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
        self.skip_newlines();

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
        if self.did_match(TokenKind::Less)? {
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
        self.skip_newlines();

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

#[cfg(test)]
mod tests {
    use crate::{
        Parsed, SourceFile,
        name::Name,
        parsing::expr::Expr::{self, *},
        token_kind::TokenKind,
    };

    fn parse(input: &str) -> SourceFile<Parsed> {
        super::parse(input, 123)
    }

    #[test]
    fn parses_literal_expr() {
        let parsed = parse("123");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, LiteralInt("123".into()));
    }

    #[test]
    fn parses_eq() {
        let parsed = parse("1 == 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::EqualsEquals, 1,));
    }

    #[test]
    fn stores_expr_meta() {
        let parsed = parse("1 + 2");
        let meta = &parsed.meta[parsed.root_ids()[0] as usize];

        assert_eq!(meta.start.start, 0);
        assert_eq!(meta.start.end, 1);
        assert_eq!(meta.end.start, 4);
        assert_eq!(meta.end.end, 5);
        assert_eq!(meta.source_range(), 0..5);
    }

    #[test]
    fn parses_not_eq() {
        let parsed = parse("1 != 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::BangEquals, 1,));
    }

    #[test]
    fn parses_greater() {
        let parsed = parse("1 > 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Greater, 1,));
    }

    #[test]
    fn parses_greater_eq() {
        let parsed = parse("1 >= 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::GreaterEquals, 1,));
    }

    #[test]
    fn parses_less() {
        let parsed = parse("1 < 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Less, 1,));
    }

    #[test]
    fn parses_less_eq() {
        let parsed = parse("1 <= 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::LessEquals, 1,));
    }

    #[test]
    fn parses_plus_expr() {
        let parsed = parse("1 + 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Plus, 1,));
    }

    #[test]
    fn parses_minus_expr() {
        let parsed = parse("1 - 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Minus, 1));
    }

    #[test]
    fn parses_div_expr() {
        let parsed = parse("1 / 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Slash, 1));
    }

    #[test]
    fn parses_mult_expr() {
        let parsed = parse("1 * 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Star, 1));
    }

    #[test]
    fn parses_less_expr() {
        let parsed = parse("1 < 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Less, 1));
    }

    #[test]
    fn parses_less_equals_expr() {
        let parsed = parse("1 <= 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::LessEquals, 1));
    }

    #[test]
    fn parses_greater_expr() {
        let parsed = parse("1 > 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Greater, 1));
    }

    #[test]
    fn parses_greater_equals_expr() {
        let parsed = parse("1 >= 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::GreaterEquals, 1));
    }

    #[test]
    fn parses_caret_expr() {
        let parsed = parse("1 ^ 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Caret, 1));
    }

    #[test]
    fn parses_pipe_expr() {
        let parsed = parse("1 | 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Pipe, 1));
    }

    #[test]
    fn parses_correct_precedence() {
        let parsed = parse("1 + 2 * 2");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(2, TokenKind::Star, 3));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::Binary(0, TokenKind::Plus, 1)
        );
    }

    #[test]
    fn parses_group() {
        let parsed = parse("(1 + 2)");
        let expr = parsed.roots()[0].unwrap();
        let Expr::Tuple(tup) = &expr else {
            panic!("expected a Tuple, got {expr:?}");
        };

        assert_eq!(1, tup.len());
        let expr = parsed.get(&tup[0]).unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Plus, 1));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::Binary(0, TokenKind::Plus, 1)
        );
    }

    #[test]
    fn parses_var() {
        let parsed = parse("hello\nworld");
        let hello = parsed.roots()[0].unwrap();
        let world = parsed.roots()[1].unwrap();

        assert_eq!(*hello, Expr::Variable(Name::Raw("hello".to_string()), None));
        assert_eq!(*world, Expr::Variable(Name::Raw("world".to_string()), None));
    }

    #[test]
    fn parses_unary_bang() {
        let parsed = parse("!hello");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Unary(TokenKind::Bang, 0));
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::Variable(Name::Raw("hello".to_string()), None)
        );
    }

    #[test]
    fn parses_unary_minus() {
        let parsed = parse("-1");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Unary(TokenKind::Minus, 0));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("1".into()));
    }

    #[test]
    fn parses_tuple() {
        let parsed = parse("(1, 2, fizz)");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Tuple(vec![0, 1, 2]));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("1".into()));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("2".into()));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::Variable(Name::Raw("fizz".to_string()), None)
        );
    }

    #[test]
    fn parses_empty_tuple() {
        let parsed = parse("( )");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Tuple(vec![]));
    }

    #[test]
    fn parses_return() {
        let _parsed = parse("func() { return }");
    }

    #[test]
    fn parses_func_literal_no_name_no_args() {
        let parsed = parse("func() { }");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func {
                name: None,
                generics: vec![],
                params: vec![],
                body: 0,
                ret: None,
                captures: vec![],
            }
        );
        assert_eq!(*parsed.get(&0).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_literal_with_newlines() {
        let parsed = parse(
            "func greet(a) {
                a
            }",
        );

        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![0],
                body: 2,
                ret: None,
                captures: vec![],
            }
        );
    }

    #[test]
    fn parses_func_literal_name_no_args() {
        let parsed = parse("func greet() { }");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![],
                body: 0,
                ret: None,
                captures: vec![],
            }
        );
        assert_eq!(*parsed.get(&0).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_with_generics() {
        let parsed = parse(
            "
        func greet<T>(t) -> T { t }
        ",
        );
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![0],
                params: vec![1],
                body: 4,
                ret: Some(2),
                captures: vec![],
            }
        );

        assert_eq!(*parsed.get(&1).unwrap(), Expr::Parameter("t".into(), None));
        assert_eq!(*parsed.get(&4).unwrap(), Expr::Block(vec![3]));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::TypeRepr("T".into(), vec![], false)
        );
    }

    #[test]
    fn parses_func_call_with_generics() {
        let parsed = parse("foo<T>()");
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::Call {
                callee: 0,
                type_args: vec![1],
                args: vec![]
            }
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr("T".into(), vec![], false)
        );
    }

    #[test]
    fn parses_multiple_roots() {
        let parsed = parse("func hello() {}\nfunc world() {}");
        assert_eq!(2, parsed.roots().len());
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::Func {
                name: Some(Name::Raw("hello".to_string())),
                generics: vec![],
                params: vec![],
                body: 0,
                ret: None,
                captures: vec![],
            }
        );

        assert_eq!(*parsed.get(&0).unwrap(), Expr::Block(vec![]));
        assert_eq!(
            *parsed.roots()[1].unwrap(),
            Expr::Func {
                name: Some(Name::Raw("world".to_string())),
                generics: vec![],
                params: vec![],
                body: 2,
                ret: None,
                captures: vec![],
            }
        );
        assert_eq!(*parsed.get(&2).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_literal_name_with_args() {
        let parsed = parse("func greet(one, two) { }");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![0, 1],
                body: 2,
                ret: None,
                captures: vec![],
            }
        );
    }

    #[test]
    fn parses_param_type() {
        let parsed = parse("func greet(name: Int) {}");
        let expr = parsed.roots()[0].unwrap();
        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![1],
                body: 2,
                ret: None,
                captures: vec![],
            }
        );

        assert_eq!(
            *parsed.get(&1).unwrap(),
            Parameter(Name::Raw("name".to_string()), Some(0))
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            TypeRepr("Int".into(), vec![], false)
        );
    }

    #[test]
    fn parses_call_no_args() {
        let parsed = parse("fizz()");
        let expr = parsed.roots()[0].unwrap();

        let Expr::Call {
            callee: callee_id,
            args: args_ids,
            ..
        } = expr
        else {
            panic!("no call found")
        };

        let callee = parsed.get(callee_id).unwrap();
        let args_id: Vec<_> = args_ids.iter().map(|id| parsed.get(id).unwrap()).collect();
        assert_eq!(*callee, Expr::Variable(Name::Raw("fizz".to_string()), None));
        assert_eq!(args_id.len(), 0);
    }

    #[test]
    fn parses_call_with_args() {
        let parsed = parse("fizz(foo: 123)");

        println!("{:?}", parsed);

        let expr = parsed.roots()[0].unwrap();

        let Expr::Call {
            callee: callee_id,
            args: args_ids,
            ..
        } = expr
        else {
            panic!("no call found")
        };

        let callee = parsed.get(callee_id).unwrap();
        let args_id: Vec<_> = args_ids.iter().map(|id| parsed.get(id).unwrap()).collect();
        assert_eq!(*callee, Expr::Variable(Name::Raw("fizz".to_string()), None));
        assert_eq!(args_id.len(), 1);
        assert_eq!(
            *args_id[0],
            Expr::CallArg {
                label: Some("foo".into()),
                value: 1
            }
        );

        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("123".into()));
    }

    #[test]
    fn parses_let() {
        let parsed = parse("let fizz");
        let expr = parsed.roots()[0].unwrap();
        assert_eq!(*expr, Expr::Let(Name::Raw("fizz".to_string()), None));
    }

    #[test]
    fn parses_let_with_type() {
        let parsed = parse("let fizz: Int");
        let expr = parsed.roots()[0].unwrap();
        assert_eq!(*expr, Expr::Let(Name::Raw("fizz".to_string()), Some(0)));
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr("Int".into(), vec![], false)
        );
    }

    #[test]
    fn parses_let_with_tuple_type() {
        let parsed = parse("let fizz: (Int, Bool)");
        let expr = parsed.roots()[0].unwrap();
        assert_eq!(*expr, Expr::Let(Name::Raw("fizz".to_string()), Some(2)));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::TupleTypeRepr(vec![0, 1], false)
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr("Int".into(), vec![], false)
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr("Bool".into(), vec![], false)
        );
    }

    #[test]
    fn parses_return_type_annotation() {
        let parsed = parse("func fizz() -> Int { 123 }");
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("fizz".to_string())),
                generics: vec![],
                params: vec![],
                body: 2,
                ret: Some(0),
                captures: vec![],
            }
        );
    }

    #[test]
    fn parses_bools() {
        let parsed = parse("true\nfalse");
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.roots()[1].unwrap(), Expr::LiteralFalse);
    }

    #[test]
    fn parses_if() {
        let parsed = parse("if true { 123 }");
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::If(0, 2, None));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.get(&2).unwrap(), Expr::Block(vec![1]));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("123".into()));
    }

    #[test]
    fn parses_if_else() {
        let parsed = parse("if true { 123 } else { 456 }");
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::If(0, 2, Some(4)));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.get(&2).unwrap(), Expr::Block(vec![1]));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("123".into()));
        assert_eq!(*parsed.get(&4).unwrap(), Expr::Block(vec![3]));
        assert_eq!(*parsed.get(&3).unwrap(), Expr::LiteralInt("456".into()));
    }

    #[test]
    fn parses_loop() {
        let parsed = parse("loop { 123 }");
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::Loop(None, 1));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::Block(vec![0]));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("123".into()));
    }

    #[test]
    fn parses_loop_with_condition() {
        let parsed = parse("loop true { 123 }");
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::Loop(Some(0), 2));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.get(&2).unwrap(), Expr::Block(vec![1]));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("123".into()));
    }

    #[test]
    fn parses_empty_enum_decl() {
        let parsed = parse("enum Fizz {}");

        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::EnumDecl("Fizz".into(), vec![], 0)
        );
    }

    #[test]
    fn parses_empty_enum_instantiation() {
        let parsed = parse("enum Fizz { case foo }\nFizz.foo");

        assert_eq!(*parsed.roots()[1].unwrap(), Member(Some(3), "foo".into()));
    }

    #[test]
    fn parses_empty_enum_instantiation_with_value() {
        let parsed = parse("enum Fizz { case foo(Int) }\nFizz.foo(123)");

        assert_eq!(
            *parsed.roots()[1].unwrap(),
            Call {
                callee: 5,
                type_args: vec![],
                args: vec![7]
            }
        );
        assert_eq!(*parsed.get(&5).unwrap(), Member(Some(4), "foo".into()));
        assert_eq!(*parsed.get(&4).unwrap(), Variable("Fizz".into(), None));
    }

    #[test]
    fn parses_enum_with_generics() {
        let parsed = parse(
            "enum Fizz<T, Y> {
                case foo(T, Y), bar
            }
            
            enum Buzz<T, Y> {
                case foo(T, Y), bar
            }",
        );
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::EnumDecl("Fizz".into(), vec![0, 1], 6));

        // Check the enum generics
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr("T".into(), vec![], true)
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr("Y".into(), vec![], true)
        );

        // Check the body
        assert_eq!(*parsed.get(&6).unwrap(), Expr::Block(vec![4, 5]));
        assert_eq!(
            *parsed.get(&4).unwrap(),
            Expr::EnumVariant(Name::Raw("foo".into()), vec![2, 3])
        );
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::TypeRepr("T".into(), vec![], false)
        );
        assert_eq!(
            *parsed.get(&3).unwrap(),
            Expr::TypeRepr("Y".into(), vec![], false)
        );
    }

    #[test]
    fn parses_enum_cases() {
        let parsed = parse(
            "enum Fizz {
                case foo, bar
                case fizz
            }",
        );
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::EnumDecl("Fizz".into(), vec![], 3)
        );

        let Expr::Block(exprs) = parsed.get(&3).unwrap() else {
            panic!("didn't get body")
        };

        assert_eq!(exprs.len(), 3);
        assert_eq!(
            *parsed.get(&exprs[0]).unwrap(),
            Expr::EnumVariant(Name::Raw("foo".to_string()), vec![])
        );
        assert_eq!(
            *parsed.get(&exprs[1]).unwrap(),
            Expr::EnumVariant(Name::Raw("bar".to_string()), vec![])
        );
        assert_eq!(
            *parsed.get(&exprs[2]).unwrap(),
            Expr::EnumVariant(Name::Raw("fizz".to_string()), vec![])
        );
    }

    #[test]
    fn parses_enum_cases_with_associated_values() {
        let parsed = parse(
            "enum Fizz {
                case foo(Int, Float), bar(Float, Int)
            }",
        );
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::EnumDecl("Fizz".into(), vec![], 6)
        );

        let Expr::Block(exprs) = parsed.get(&6).unwrap() else {
            panic!("didn't get body")
        };

        assert_eq!(exprs.len(), 2);
        assert_eq!(
            *parsed.get(&exprs[0]).unwrap(),
            Expr::EnumVariant("foo".into(), vec![0, 1])
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr("Int".into(), vec![], false)
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr("Float".into(), vec![], false)
        );

        assert_eq!(
            *parsed.get(&exprs[1]).unwrap(),
            Expr::EnumVariant(Name::Raw("bar".into()), vec![3, 4])
        );
        assert_eq!(
            *parsed.get(&3).unwrap(),
            Expr::TypeRepr("Float".into(), vec![], false)
        );
        assert_eq!(
            *parsed.get(&4).unwrap(),
            Expr::TypeRepr("Int".into(), vec![], false)
        );
    }

    #[test]
    fn parses_match() {
        let parsed = parse(
            "match fizz {
                .foo(name) -> name
                .bar -> fizz
            }",
        );

        assert_eq!(*parsed.roots()[0].unwrap(), Expr::Match(0, vec![4, 7]));
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Variable(Name::Raw("fizz".to_string()), None)
        );

        assert_eq!(*parsed.get(&4).unwrap(), MatchArm(2, 3));
        assert_eq!(*parsed.get(&7).unwrap(), MatchArm(5, 6));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Pattern(crate::expr::Pattern::Variant {
                enum_name: None,
                variant_name: "foo".into(),
                fields: vec![1]
            })
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Pattern(crate::expr::Pattern::Bind(Name::Raw("name".into())))
        );
        assert_eq!(
            *parsed.get(&5).unwrap(),
            Pattern(crate::expr::Pattern::Variant {
                enum_name: None,
                variant_name: "bar".into(),
                fields: vec![]
            })
        );
    }

    #[test]
    fn parses_fn_type_repr() {
        let parsed = parse(
            "
        func greet(using: (T) -> Y) {}
        ",
        );
        let expr = parsed.roots()[0].unwrap();
        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![3],
                body: 4,
                ret: None,
                captures: vec![],
            }
        );

        assert_eq!(
            *parsed.get(&3).unwrap(),
            Expr::Parameter("using".into(), Some(2))
        );

        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::FuncTypeRepr(vec![0], 1, false)
        );

        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr("T".into(), vec![], false)
        );

        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr("Y".into(), vec![], false)
        );
    }

    #[test]
    fn converts_question_to_optional_for_type_repr() {
        let parsed = parse("func greet(name: Int?) {}");
        let expr = parsed.roots()[0].unwrap();
        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![2],
                body: 3,
                ret: None,
                captures: vec![],
            }
        );

        assert_eq!(
            *parsed.get(&2).unwrap(),
            Parameter(Name::Raw("name".to_string()), Some(1))
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            TypeRepr("Optional".into(), vec![0], false)
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            TypeRepr("Int".into(), vec![], false)
        );
    }

    #[test]
    fn parses_enum_methods() {
        let parsed = parse(
            "
            enum MyEnum {
                case val(Int), nope

                func fizz() {
                    123
                }
            }
        ",
        );

        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::EnumDecl("MyEnum".into(), vec![], 6)
        );

        let Expr::Block(exprs) = parsed.get(&6).unwrap() else {
            panic!("didn't get block: {:?}", parsed.get(&3));
        };

        assert_eq!(3, exprs.len());
        assert_eq!(
            *parsed.get(&exprs[2]).unwrap(),
            Expr::Func {
                name: Some(Name::Raw("fizz".into())),
                generics: vec![],
                params: vec![],
                body: 4,
                ret: None,
                captures: vec![],
            }
        )
    }

    #[test]
    fn parses_variable_assignment() {
        let parsed = parse(
            "
            foo = 123
            ",
        );

        assert_eq!(*parsed.roots()[0].unwrap(), Expr::Assignment(0, 1));
    }
}

#[cfg(test)]
mod pattern_parsing_tests {
    use crate::{expr::Pattern, lexer::Lexer, name::Name};

    use super::Parser;

    fn parse_pattern(input: &'static str) -> Pattern {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer, 123);
        parser.advance();
        parser.advance();
        parser.parse_match_pattern().unwrap()
    }

    #[test]
    fn parses_wildcard() {
        assert_eq!(parse_pattern("_ "), Pattern::Wildcard);
    }

    #[test]
    fn parses_literal_int() {
        assert_eq!(parse_pattern("123"), Pattern::LiteralInt("123".into()));
    }

    #[test]
    fn parses_literal_float() {
        assert_eq!(parse_pattern("123."), Pattern::LiteralFloat("123.".into()));
    }

    #[test]
    fn parses_literal_bools() {
        assert_eq!(parse_pattern("true"), Pattern::LiteralTrue);
        assert_eq!(parse_pattern("false"), Pattern::LiteralFalse);
    }

    #[test]
    fn parses_variant_pattern() {
        assert_eq!(
            parse_pattern("Fizz.buzz"),
            Pattern::Variant {
                enum_name: Some(Name::Raw("Fizz".into())),
                variant_name: "buzz".into(),
                fields: vec![]
            }
        );

        assert_eq!(
            parse_pattern(".foo"),
            Pattern::Variant {
                enum_name: None,
                variant_name: "foo".into(),
                fields: vec![]
            }
        );
    }
}

#[cfg(test)]
mod arrays {
    use crate::{expr::Expr, parser::parse};

    #[test]
    fn parses_array_literal() {
        let parsed = parse("[1, 2, 3]", 0);
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::LiteralArray(vec!(0, 1, 2))
        );

        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("1".into()));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("2".into()));
        assert_eq!(*parsed.get(&2).unwrap(), Expr::LiteralInt("3".into()));
    }

    #[test]
    fn parses_array_literal_with_newlines() {
        let parsed = parse(
            "[
          1
          ,
        2, 3
        ]",
            0,
        );
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::LiteralArray(vec!(0, 1, 2))
        );
    }
}

#[cfg(test)]
mod structs {
    use crate::{expr::Expr, name::Name, parser::parse};

    #[test]
    fn parses_empty_struct_def() {
        let parsed = parse(
            "
        struct Person {}
        ",
            0,
        );

        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::Struct(Name::Raw("Person".into()), vec![], 0)
        );
    }

    #[test]
    fn parses_struct_properties() {
        let parsed = parse(
            "
        struct Person {
            let age: Int
            let count: Int = 123
            let height = 456
        }
        ",
            0,
        );

        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::Struct(Name::Raw("Person".into()), vec![], 7)
        );
        assert_eq!(*parsed.get(&7).unwrap(), Expr::Block(vec![1, 4, 6]));
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::Property {
                name: "age".into(),
                type_repr: Some(0),
                default_value: None
            }
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr("Int".into(), vec![], false)
        );

        assert_eq!(
            *parsed.get(&4).unwrap(),
            Expr::Property {
                name: "count".into(),
                type_repr: Some(2),
                default_value: Some(3)
            }
        );
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::TypeRepr("Int".into(), vec![], false)
        );
        assert_eq!(*parsed.get(&3).unwrap(), Expr::LiteralInt("123".into()));

        assert_eq!(
            *parsed.get(&6).unwrap(),
            Expr::Property {
                name: "height".into(),
                type_repr: None,
                default_value: Some(5)
            }
        );
        assert_eq!(*parsed.get(&5).unwrap(), Expr::LiteralInt("456".into()));
    }

    #[test]
    fn parses_init() {
        let parsed = parse(
            "
        struct Person {
            let age: Int
            
            init(age: Int) {
                self.age = age
            }
        }
        ",
            0,
        );

        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::Struct("Person".into(), vec![], 11)
        );

        let Some(Expr::Block(items)) = parsed.get(&11) else {
            unreachable!()
        };

        let Some(Expr::Init(None, func_id)) = parsed.get(&items[1]) else {
            unreachable!()
        };

        let Some(Expr::Func {
            name,
            generics,
            params,
            body,
            ret,
            captures,
        }) = parsed.get(func_id)
        else {
            unreachable!()
        };

        assert_eq!(&Some(Name::Raw("init".into())), name);
        assert!(generics.is_empty());
        assert_eq!(&vec![3], params);
        assert_eq!(&None, ret);
        assert_eq!(&8, body);
        assert!(captures.is_empty());
    }
}

#[cfg(test)]
mod error_handling_tests {
    use crate::{
        diagnostic::Diagnostic, expr::Expr, parser::parse, token::Token, token_kind::TokenKind,
    };

    #[test]
    fn handles_unclosed_paren() {
        let parsed = parse("(", 0);
        assert_eq!(parsed.diagnostics.len(), 1);
        assert!(parsed.diagnostics.contains(&Diagnostic::parser(
            Token {
                kind: TokenKind::LeftParen,
                col: 1,
                line: 0,
                start: 0,
                end: 1,
            },
            crate::parser::ParserError::UnexpectedEndOfInput(None)
        )))
    }

    #[test]
    fn handles_unclosed_brace() {
        let parsed = parse("func foo() {", 0);
        assert_eq!(parsed.diagnostics.len(), 1);
        assert!(
            parsed.diagnostics.contains(&Diagnostic::parser(
                Token {
                    kind: TokenKind::Func,
                    col: 4,
                    line: 0,
                    start: 0,
                    end: 4,
                },
                crate::parser::ParserError::UnexpectedEndOfInput(None)
            )),
            "{:?}",
            parsed.diagnostics
        )
    }

    #[test]
    fn recovers() {
        let parsed = parse("func foo() {\n\nfunc fizz() {}", 0);
        assert_eq!(parsed.diagnostics.len(), 1, "{:?}", parsed);
        assert!(parsed.diagnostics.contains(&Diagnostic::parser(
            Token {
                kind: TokenKind::Func,
                col: 4,
                line: 0,
                start: 0,
                end: 4,
            },
            crate::parser::ParserError::UnexpectedEndOfInput(None)
        )));

        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::Func {
                name: Some("fizz".into()),
                body: 0,
                ret: None,
                params: vec![],
                generics: vec![],
                captures: vec![]
            }
        )
    }
}
