use crate::{SourceFile, lexer::Lexer, token::Token, token_kind::TokenKind};

use super::{
    expr::{
        Expr::{self, *},
        ExprMeta, FuncName, Name,
    },
    precedence::Precedence,
};

pub type ExprID = i32;
pub type VariableID = u32;

pub struct Parser {
    pub(crate) lexer: Lexer,
    pub(crate) previous: Option<Token>,
    pub(crate) current: Option<Token>,
    pub(crate) parse_tree: SourceFile,
}

#[derive(Debug)]
pub enum ParserError {
    UnexpectedToken(
        Vec<TokenKind>, /* expected */
        TokenKind,      /* actual */
    ),
    UnexpectedEndOfInput(Vec<TokenKind> /* expected */),
    UnknownError(&'static str),
}

pub fn parse(code: &'static str) -> Result<SourceFile, ParserError> {
    let lexer = Lexer::new(code);
    let mut parser = Parser::new(lexer);

    parser.parse();

    Ok(parser.parse_tree)
}

impl Parser {
    pub fn new(lexer: Lexer) -> Self {
        Self {
            lexer,
            previous: None,
            current: None,
            parse_tree: SourceFile::new(),
        }
    }

    pub fn parse(&mut self) {
        self.advance();
        self.skip_newlines();

        while let Some(current) = self.current.clone() {
            self.skip_newlines();

            if current.kind == TokenKind::EOF {
                return;
            }

            let expr = self
                .parse_with_precedence(Precedence::Assignment)
                .unwrap_or_else(|_| panic!("did not get an expr: {:?}", self.current));

            self.parse_tree.push_root(expr);

            self.skip_newlines();
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
        self.previous = self.current.clone();
        self.current = self.lexer.next().ok();
        self.previous.clone()
    }

    fn add_expr(&mut self, expr: Expr) -> Result<ExprID, ParserError> {
        let token = self.current.clone().unwrap();

        let expr_meta = ExprMeta {
            start: token.clone(),
            end: token,
        };

        Ok(self.parse_tree.add(expr, expr_meta))
    }

    // MARK: Expr parsers

    pub(crate) fn enum_decl(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        self.consume(TokenKind::Enum)?;
        self.skip_newlines();

        let name = self.type_repr()?;

        // Consume the block
        let body = self.enum_body()?;

        self.add_expr(EnumDecl(name, body))
    }

    pub(crate) fn match_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        self.consume(TokenKind::Match)?;

        let target = self.parse_with_precedence(Precedence::Call)?;
        let body = self.match_block()?;

        self.add_expr(Match(target, body))
    }

    fn match_block(&mut self) -> Result<ExprID, ParserError> {
        self.skip_newlines();

        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<ExprID> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            let pattern = self.parse_match_pattern()?;
            self.consume(TokenKind::Arrow)?;
            let body = self.parse_with_precedence(Precedence::Primary)?;
            items.push(self.add_expr(MatchArm(pattern, body))?);
        }

        self.add_expr(Expr::Block(items))
    }

    fn parse_match_pattern(&mut self) -> Result<ExprID, ParserError> {
        self.skip_newlines();

        // Handle unqualified enum cases: .EnumCase or .EnumCase(args)
        if self.did_match(TokenKind::Dot)? {
            // Get the enum case name
            let Some((
                _,
                Token {
                    kind: TokenKind::Identifier(name),
                    ..
                },
            )) = self.try_identifier()
            else {
                return Err(ParserError::UnexpectedToken(
                    vec![TokenKind::Identifier("_".to_string())],
                    self.current.clone().unwrap().kind,
                ));
            };

            // Check if it has arguments: .Case(arg1, arg2)
            if self.did_match(TokenKind::LeftParen)? {
                let mut args: Vec<ExprID> = vec![];

                // Parse arguments (could be patterns themselves)
                if !self.did_match(TokenKind::RightParen)? {
                    loop {
                        args.push(self.parse_match_pattern()?);

                        if !self.did_match(TokenKind::Comma)? {
                            break;
                        }
                    }
                    self.consume(TokenKind::RightParen)?;
                }

                // Create a pattern call: .Case(args)
                let member = self.add_expr(Member(None, name))?;
                self.add_expr(Call(member, args))
            } else {
                // Simple case: .Case
                self.add_expr(Member(None, name))
            }
        }
        // Handle variable patterns: just a name
        else if let Some((
            _,
            Token {
                kind: TokenKind::Identifier(name),
                ..
            },
        )) = self.try_identifier()
        {
            self.add_expr(Variable(Name::Raw(name.to_string()), None))
        }
        // Handle literal patterns: numbers, etc.
        else if let Some(current) = self.current.clone() {
            match current.kind {
                TokenKind::Int(_) | TokenKind::Float(_) => self.literal(false),
                _ => Err(ParserError::UnexpectedToken(
                    vec![
                        TokenKind::Dot,
                        TokenKind::Identifier("_".to_string()),
                        TokenKind::Int("_"),
                    ],
                    current.kind,
                )),
            }
        } else {
            Err(ParserError::UnexpectedEndOfInput(vec![
                TokenKind::Dot,
                TokenKind::Identifier("_".to_string()),
            ]))
        }
    }

    pub(crate) fn member_prefix(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        self.consume(TokenKind::Dot)?;
        let (name, _) = self.try_identifier().unwrap();
        self.add_expr(Member(None, name.to_string()))
    }

    pub(crate) fn boolean(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        if self.did_match(TokenKind::True)? {
            return self.add_expr(Expr::LiteralTrue);
        }

        if self.did_match(TokenKind::False)? {
            return self.add_expr(Expr::LiteralFalse);
        }

        unreachable!()
    }

    pub(crate) fn if_expr(&mut self, can_assign: bool) -> Result<ExprID, ParserError> {
        self.consume(TokenKind::If)?;

        let condition = self.parse_with_precedence(Precedence::Any)?;
        let body = self.block(can_assign)?;

        if self.did_match(TokenKind::Else)? {
            let else_body = self.block(can_assign)?;
            self.add_expr(If(condition, body, Some(else_body)))
        } else {
            self.add_expr(If(condition, body, None))
        }
    }

    pub(crate) fn loop_expr(&mut self, can_assign: bool) -> Result<ExprID, ParserError> {
        self.consume(TokenKind::Loop)?;

        let mut condition = None;
        if let Some(Token {
            kind: TokenKind::LeftBrace,
            ..
        }) = self.current
        {
            ()
        } else {
            condition = Some(self.parse_with_precedence(Precedence::Any)?)
        }

        let body = self.block(can_assign)?;

        self.add_expr(Loop(condition, body))
    }

    pub(crate) fn tuple(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        self.consume(TokenKind::LeftParen)?;

        if self.did_match(TokenKind::RightParen)? {
            return self.add_expr(Tuple(vec![]));
        }

        let child = self.parse_with_precedence(Precedence::Assignment)?;

        if self.did_match(TokenKind::RightParen)? {
            return self.add_expr(Tuple(vec![child]));
        }

        self.consume(TokenKind::Comma)?;

        let mut items = vec![child];
        while {
            items.push(self.parse_with_precedence(Precedence::Assignment)?);
            self.did_match(TokenKind::Comma)?
        } {}

        self.consume(TokenKind::RightParen)?;

        self.add_expr(Tuple(items))
    }

    pub(crate) fn let_expr(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        // Consume the `let` keyword
        self.advance();
        let (name, _) = self.try_identifier().expect("did not get identifier");

        let rhs = if self.did_match(TokenKind::Equals)? {
            Some(self.parse_with_precedence(Precedence::Assignment)?)
        } else {
            None
        };

        let let_expr = self.add_expr(Let(Name::Raw(name.to_string()), rhs));

        if self.did_match(TokenKind::Equals)? {
            let rhs = self.parse_with_precedence(Precedence::None)?;
            self.add_expr(Expr::Assignment(let_expr?, rhs))
        } else {
            let_expr
        }
    }

    pub(crate) fn literal(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        self.advance();

        match self
            .previous
            .clone()
            .expect("got into #literal without having a token")
            .kind
        {
            TokenKind::Int(val) => self.add_expr(LiteralInt(val)),
            TokenKind::Float(val) => self.add_expr(LiteralFloat(val)),
            TokenKind::Func => self.func(),
            _ => unreachable!("didn't get a literal"),
        }
    }

    pub(crate) fn func(&mut self) -> Result<ExprID, ParserError> {
        let name = if let Some((
            _,
            Token {
                kind: TokenKind::Identifier(name),
                ..
            },
        )) = self.try_identifier()
        {
            Some(name)
        } else {
            None
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
            let ty_repr = if self.did_match(TokenKind::Colon)? {
                Some(self.type_repr()?)
            } else {
                None
            };

            params.push(self.add_expr(Parameter(Name::Raw(name.to_string()), ty_repr))?);

            if self.did_match(TokenKind::Comma)? {
                continue;
            }

            break;
        }

        self.consume(TokenKind::RightParen)?;

        let ret = if self.did_match(TokenKind::Arrow)? {
            if let Some((
                _,
                Token {
                    kind: TokenKind::Identifier(ret_name),
                    ..
                },
            )) = self.try_identifier()
            {
                let ret_id = self.add_expr(TypeRepr(ret_name, vec![]))?;
                Some(ret_id)
            } else {
                None
            }
        } else {
            None
        };

        let body = self.block(false)?;

        self.add_expr(Expr::Func(
            name.map(|s| s.to_string()).map(FuncName::Token),
            params,
            body,
            ret,
        ))
    }

    fn type_repr(&mut self) -> Result<ExprID, ParserError> {
        let Some((name, _)) = self.try_identifier() else {
            return Err(ParserError::UnexpectedToken(
                vec![TokenKind::Identifier("_".to_string())],
                self.current.clone().unwrap().kind,
            ));
        };

        let mut generics = vec![];
        if self.did_match(TokenKind::Less)? {
            while !self.did_match(TokenKind::Greater)? {
                let generic = self.type_repr()?;
                generics.push(generic);
                self.consume(TokenKind::Comma).ok();
            }
        }

        let type_repr = TypeRepr(name, generics);
        self.add_expr(type_repr)
    }

    fn enum_body(&mut self) -> Result<ExprID, ParserError> {
        self.skip_newlines();
        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<ExprID> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            if self.did_match(TokenKind::Case)? {
                while {
                    let (name, _) = self.try_identifier().expect("did not get enum case name");
                    let mut types = vec![];

                    if self.did_match(TokenKind::LeftParen)? {
                        while !self.did_match(TokenKind::RightParen)? {
                            types.push(self.type_repr()?);
                            self.consume(TokenKind::Comma).ok();
                        }
                    }

                    let item = self.add_expr(Expr::EnumVariant(Name::Raw(name), types))?;
                    items.push(item);
                    self.did_match(TokenKind::Comma)?
                } {}
            } else {
                let item = self.parse_with_precedence(Precedence::Assignment)?;
                items.push(item);
            };
        }

        self.add_expr(Expr::Block(items))
    }

    pub(crate) fn block(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        self.skip_newlines();

        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<ExprID> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            items.push(self.parse_with_precedence(Precedence::Assignment)?)
        }

        self.add_expr(Expr::Block(items))
    }

    pub(crate) fn variable(&mut self, can_assign: bool) -> Result<ExprID, ParserError> {
        let (name, _) = self.try_identifier().unwrap();
        let variable = self.add_expr(Variable(Name::Raw(name.to_string()), None))?;

        self.skip_newlines();

        if self.did_match(TokenKind::LeftParen)? {
            self.skip_newlines();
            self.call(can_assign, variable)
        } else {
            Ok(variable)
        }
    }

    pub(crate) fn call(
        &mut self,
        _can_assign: bool,
        callee: ExprID,
    ) -> Result<ExprID, ParserError> {
        let mut args: Vec<ExprID> = vec![];

        if !self.did_match(TokenKind::RightParen)? {
            while {
                let arg = self.parse_with_precedence(Precedence::Assignment)?;
                args.push(arg);
                self.did_match(TokenKind::Comma)?
            } {}

            self.consume(TokenKind::RightParen)?;
        }

        self.add_expr(Expr::Call(callee, args))
    }

    pub(crate) fn unary(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let op = self.consume_any(vec![TokenKind::Minus, TokenKind::Bang])?;
        let current_precedence = Precedence::handler(&Some(op.clone()))?.precedence;
        let rhs = self
            .parse_with_precedence(current_precedence + 1)
            .expect("did not get binop rhs");

        self.add_expr(Unary(op.kind, rhs))
    }

    pub(crate) fn binary(&mut self, _can_assign: bool, lhs: ExprID) -> Result<ExprID, ParserError> {
        let op = self.consume_any(vec![
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Star,
            TokenKind::Slash,
            TokenKind::Less,
            TokenKind::LessEquals,
            TokenKind::Greater,
            TokenKind::GreaterEquals,
            TokenKind::Caret,
            TokenKind::Pipe,
        ])?;

        let current_precedence = Precedence::handler(&Some(op.clone()))?.precedence;
        let rhs = self
            .parse_with_precedence(current_precedence + 1)
            .expect("did not get binop rhs");

        self.add_expr(Binary(lhs, op.kind, rhs))
    }

    pub fn parse_with_precedence(&mut self, precedence: Precedence) -> Result<ExprID, ParserError> {
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
                println!("No infix found for {:?}", self.current)
            }

            if self.did_match(TokenKind::Newline)? {
                break;
            }

            if i > 100 {
                panic!(
                    "we've got a problem: {:?}, parsed: {:?}",
                    self.current, self.parse_tree
                );
            }
        }

        #[allow(clippy::expect_fun_call)]
        Ok(lhs.expect(&format!("did not get lhs: {:?}", self.current)))
    }

    // MARK: Helpers

    // Try to get an identifier. If it's a match, return it, otherwise return None
    fn try_identifier(&mut self) -> Option<(String, Token)> {
        self.skip_newlines();

        if let Some(current) = self.current.clone() {
            if let TokenKind::Identifier(ref name) = current.kind {
                self.advance();
                return Some((name.to_string(), current));
            };
        }

        None
    }

    // Try to get a specific token. If it's a match, return true.
    fn did_match(&mut self, expected: TokenKind) -> Result<bool, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current.clone() {
            if current.kind == expected {
                self.advance();
                return Ok(true);
            };
        }

        Ok(false)
    }

    // Try to get a specific token. If it's not a match, return an error.
    fn consume(&mut self, expected: TokenKind) -> Result<Token, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current.clone() {
            if current.kind == expected {
                self.advance();
                return Ok(current);
            };
        }

        Err(ParserError::UnexpectedToken(
            vec![expected],
            self.current.clone().unwrap().kind,
        ))
    }

    fn consume_any(&mut self, possible_tokens: Vec<TokenKind>) -> Result<Token, ParserError> {
        self.skip_newlines();

        match self.current.clone() {
            Some(current) => {
                if possible_tokens.contains(&current.kind) {
                    self.advance();
                    Ok(current)
                } else {
                    Err(ParserError::UnexpectedToken(possible_tokens, current.kind))
                }
            }
            None => Err(ParserError::UnexpectedEndOfInput(possible_tokens)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        expr::{FuncName, Name},
        parser::parse,
        parsing::expr::Expr::{self, *},
        token_kind::TokenKind,
    };

    #[test]
    fn parses_literal_expr() {
        let parsed = parse("123").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, LiteralInt("123"));
    }

    #[test]
    fn parses_plus_expr() {
        let parsed = parse("1 + 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Plus, 1,));
    }

    #[test]
    fn parses_minus_expr() {
        let parsed = parse("1 - 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Minus, 1));
    }

    #[test]
    fn parses_div_expr() {
        let parsed = parse("1 / 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Slash, 1));
    }

    #[test]
    fn parses_mult_expr() {
        let parsed = parse("1 * 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Star, 1));
    }

    #[test]
    fn parses_less_expr() {
        let parsed = parse("1 < 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Less, 1));
    }

    #[test]
    fn parses_less_equals_expr() {
        let parsed = parse("1 <= 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::LessEquals, 1));
    }

    #[test]
    fn parses_greater_expr() {
        let parsed = parse("1 > 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Greater, 1));
    }

    #[test]
    fn parses_greater_equals_expr() {
        let parsed = parse("1 >= 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::GreaterEquals, 1));
    }

    #[test]
    fn parses_caret_expr() {
        let parsed = parse("1 ^ 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Caret, 1));
    }

    #[test]
    fn parses_pipe_expr() {
        let parsed = parse("1 | 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Pipe, 1));
    }

    #[test]
    fn parses_correct_precedence() {
        let parsed = parse("1 + 2 * 2").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Binary(2, TokenKind::Star, 3));
        assert_eq!(*parsed.get(2).unwrap(), Expr::Binary(0, TokenKind::Plus, 1));
    }

    #[test]
    fn parses_group() {
        let parsed = parse("(1 + 2)").unwrap();
        let expr = parsed.roots()[0].unwrap();
        let Expr::Tuple(tup) = &expr else {
            panic!("expected a Tuple, got {:?}", expr);
        };

        assert_eq!(1, tup.len());
        let expr = parsed.get(tup[0]).unwrap();

        assert_eq!(*expr, Expr::Binary(0, TokenKind::Plus, 1));
        assert_eq!(*parsed.get(2).unwrap(), Expr::Binary(0, TokenKind::Plus, 1));
    }

    #[test]
    fn parses_var() {
        let parsed = parse("hello\nworld").unwrap();
        let hello = parsed.roots()[0].unwrap();
        let world = parsed.roots()[1].unwrap();

        assert_eq!(*hello, Expr::Variable(Name::Raw("hello".to_string()), None));
        assert_eq!(*world, Expr::Variable(Name::Raw("world".to_string()), None));
    }

    #[test]
    fn parses_unary_bang() {
        let parsed = parse("!hello").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Unary(TokenKind::Bang, 0));
        assert_eq!(
            *parsed.get(0).unwrap(),
            Expr::Variable(Name::Raw("hello".to_string()), None)
        );
    }

    #[test]
    fn parses_unary_minus() {
        let parsed = parse("-1").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Unary(TokenKind::Minus, 0));
        assert_eq!(*parsed.get(0).unwrap(), Expr::LiteralInt("1"));
    }

    #[test]
    fn parses_tuple() {
        let parsed = parse("(1, 2, fizz)").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Tuple(vec![0, 1, 2]));
        assert_eq!(*parsed.get(0).unwrap(), Expr::LiteralInt("1"));
        assert_eq!(*parsed.get(1).unwrap(), Expr::LiteralInt("2"));
        assert_eq!(
            *parsed.get(2).unwrap(),
            Expr::Variable(Name::Raw("fizz".to_string()), None)
        );
    }

    #[test]
    fn parses_empty_tuple() {
        let parsed = parse("( )").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Tuple(vec![]));
    }

    #[test]
    fn parses_func_literal_no_name_no_args() {
        let parsed = parse("func() { }").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Func(None, vec![], 0, None));
        assert_eq!(*parsed.get(0).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_literal_with_newlines() {
        let parsed = parse(
            "func greet(a) {
                a
            }",
        )
        .unwrap();

        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func(Some(FuncName::Token("greet".to_string())), vec![0], 2, None)
        );
    }

    #[test]
    fn parses_func_literal_name_no_args() {
        let parsed = parse("func greet() { }").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func(Some(FuncName::Token("greet".to_string())), vec![], 0, None)
        );
        assert_eq!(*parsed.get(0).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_multiple_roots() {
        let parsed = parse("func hello() {}\nfunc world() {}").unwrap();
        assert_eq!(2, parsed.roots().len());
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::Func(Some(FuncName::Token("hello".to_string())), vec![], 0, None)
        );

        assert_eq!(*parsed.get(0).unwrap(), Expr::Block(vec![]));
        assert_eq!(
            *parsed.roots()[1].unwrap(),
            Expr::Func(Some(FuncName::Token("world".to_string())), vec![], 2, None)
        );
        assert_eq!(*parsed.get(2).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_literal_name_with_args() {
        let parsed = parse("func greet(one, two) { }").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func(
                Some(FuncName::Token("greet".to_string())),
                vec![0, 1],
                2,
                None
            )
        );
    }

    #[test]
    fn parses_param_type() {
        let parsed = parse("func greet(name: Int) {}").unwrap();
        let expr = parsed.roots()[0].unwrap();
        assert_eq!(
            *expr,
            Expr::Func(Some(FuncName::Token("greet".to_string())), vec![1], 2, None)
        );

        assert_eq!(
            *parsed.get(1).unwrap(),
            Parameter(Name::Raw("name".to_string()), Some(0))
        );
        assert_eq!(*parsed.get(0).unwrap(), TypeRepr("Int".to_string(), vec![]));
    }

    #[test]
    fn parses_call_no_args() {
        let parsed = parse("fizz()").unwrap();
        let expr = parsed.roots()[0].unwrap();

        let Expr::Call(callee_id, args_ids) = expr else {
            panic!("no call found")
        };

        let callee = parsed.get(*callee_id).unwrap();
        let args_id: Vec<_> = args_ids.iter().map(|id| parsed.get(*id).unwrap()).collect();
        assert_eq!(*callee, Expr::Variable(Name::Raw("fizz".to_string()), None));
        assert_eq!(args_id.len(), 0);
    }

    #[test]
    fn parses_let() {
        let parsed = parse("let fizz").unwrap();
        let expr = parsed.roots()[0].unwrap();
        assert_eq!(*expr, Expr::Let(Name::Raw("fizz".to_string()), None));
    }

    #[test]
    fn parses_return_type_annotation() {
        let parsed = parse("func fizz() -> Int { 123 }").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func(
                Some(FuncName::Token("fizz".to_string())),
                vec![],
                2,
                Some(0)
            )
        );
    }

    #[test]
    fn parses_bools() {
        let parsed = parse("true\nfalse").unwrap();
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.roots()[1].unwrap(), Expr::LiteralFalse);
    }

    #[test]
    fn parses_if() {
        let parsed = parse("if true { 123 }").unwrap();
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::If(0, 2, None));
        assert_eq!(*parsed.get(0).unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.get(2).unwrap(), Expr::Block(vec![1]));
        assert_eq!(*parsed.get(1).unwrap(), Expr::LiteralInt("123"));
    }

    #[test]
    fn parses_if_else() {
        let parsed = parse("if true { 123 } else { 456 }").unwrap();
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::If(0, 2, Some(4)));
        assert_eq!(*parsed.get(0).unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.get(2).unwrap(), Expr::Block(vec![1]));
        assert_eq!(*parsed.get(1).unwrap(), Expr::LiteralInt("123"));
        assert_eq!(*parsed.get(4).unwrap(), Expr::Block(vec![3]));
        assert_eq!(*parsed.get(3).unwrap(), Expr::LiteralInt("456"));
    }

    #[test]
    fn parses_loop() {
        let parsed = parse("loop { 123 }").unwrap();
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::Loop(None, 1));
        assert_eq!(*parsed.get(1).unwrap(), Expr::Block(vec![0]));
        assert_eq!(*parsed.get(0).unwrap(), Expr::LiteralInt("123"));
    }

    #[test]
    fn parses_loop_with_condition() {
        let parsed = parse("loop true { 123 }").unwrap();
        assert_eq!(*parsed.roots()[0].unwrap(), Expr::Loop(Some(0), 2));
        assert_eq!(*parsed.get(0).unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.get(2).unwrap(), Expr::Block(vec![1]));
        assert_eq!(*parsed.get(1).unwrap(), Expr::LiteralInt("123"));
    }

    #[test]
    fn parses_empty_enum_decl() {
        let parsed = parse("enum Fizz {}").unwrap();

        assert_eq!(*parsed.roots()[0].unwrap(), Expr::EnumDecl(0, 1));
    }

    #[test]
    fn parses_enum_with_generics() {
        let parsed = parse(
            "enum Fizz<T> {
                case foo(T), bar
            }",
        )
        .unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::EnumDecl(1, 5));
    }

    #[test]
    fn parses_enum_cases() {
        let parsed = parse(
            "enum Fizz {
                case foo, bar
                case fizz
            }",
        )
        .unwrap();

        assert_eq!(*parsed.roots()[0].unwrap(), Expr::EnumDecl(0, 4));

        let Expr::Block(exprs) = parsed.get(4).unwrap() else {
            panic!("didn't get body")
        };

        assert_eq!(exprs.len(), 3);
        assert_eq!(
            *parsed.get(exprs[0]).unwrap(),
            Expr::EnumVariant(Name::Raw("foo".to_string()), vec![])
        );
        assert_eq!(
            *parsed.get(exprs[1]).unwrap(),
            Expr::EnumVariant(Name::Raw("bar".to_string()), vec![])
        );
        assert_eq!(
            *parsed.get(exprs[2]).unwrap(),
            Expr::EnumVariant(Name::Raw("fizz".to_string()), vec![])
        );
    }

    #[test]
    fn parses_enum_cases_with_associated_values() {
        let parsed = parse(
            "enum Fizz {
                case foo(Int, Float), bar(Float, Int)
            }",
        )
        .unwrap();

        assert_eq!(*parsed.roots()[0].unwrap(), Expr::EnumDecl(0, 7));

        let Expr::Block(exprs) = parsed.get(7).unwrap() else {
            panic!("didn't get body")
        };

        assert_eq!(exprs.len(), 2);
        assert_eq!(
            *parsed.get(exprs[0]).unwrap(),
            Expr::EnumVariant(Name::Raw("foo".to_string()), vec![1, 2])
        );
        assert_eq!(
            *parsed.get(1).unwrap(),
            Expr::TypeRepr("Int".to_string(), vec![])
        );
        assert_eq!(
            *parsed.get(2).unwrap(),
            Expr::TypeRepr("Float".to_string(), vec![])
        );

        assert_eq!(
            *parsed.get(exprs[1]).unwrap(),
            Expr::EnumVariant(Name::Raw("bar".to_string()), vec![4, 5])
        );
        assert_eq!(
            *parsed.get(4).unwrap(),
            Expr::TypeRepr("Float".to_string(), vec![])
        );
        assert_eq!(
            *parsed.get(5).unwrap(),
            Expr::TypeRepr("Int".to_string(), vec![])
        );
    }

    #[test]
    fn parses_match() {
        let parsed = parse(
            "match fizz {
                .foo(name) -> name
                .bar -> fizz
            }",
        )
        .unwrap();

        assert_eq!(*parsed.roots()[0].unwrap(), Expr::Match(0, 9));
        assert_eq!(
            *parsed.get(0).unwrap(),
            Variable(Name::Raw("fizz".to_string()), None)
        );

        assert_eq!(*parsed.get(9).unwrap(), Block(vec![5, 8]));
        assert_eq!(*parsed.get(5).unwrap(), MatchArm(3, 4));
        assert_eq!(*parsed.get(3).unwrap(), Call(2, vec![1]));
        assert_eq!(
            *parsed.get(4).unwrap(),
            Variable(Name::Raw("name".to_string()), None)
        );
        assert_eq!(*parsed.get(8).unwrap(), MatchArm(6, 7));
        assert_eq!(*parsed.get(6).unwrap(), Member(None, "bar".to_string()));
        assert_eq!(
            *parsed.get(7).unwrap(),
            Variable(Name::Raw("fizz".to_string()), None)
        );
    }
}
