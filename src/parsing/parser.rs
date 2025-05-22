use crate::{lexer::Lexer, token::Token, token_kind::TokenKind};

use super::{
    expr::{
        Expr::{self, *},
        ExprMeta, FuncName,
    },
    parse_tree::ParseTree,
    precedence::Precedence,
};

pub type ExprID = u32;
pub type VariableID = u32;

pub struct Parser {
    pub(crate) lexer: Lexer,
    pub(crate) previous: Option<Token>,
    pub(crate) current: Option<Token>,
    pub(crate) parse_tree: ParseTree,
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

pub fn parse(code: &'static str) -> Result<ParseTree, ParserError> {
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
            parse_tree: ParseTree::new(),
        }
    }

    pub fn parse(&mut self) {
        self.advance();
        self.skip_newlines();

        while let Some(current) = self.current {
            self.skip_newlines();

            if current.kind == TokenKind::EOF {
                return;
            }

            let expr = self
                .parse_with_precedence(Precedence::Assignment)
                .expect("did not get an expr");

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
        self.previous = self.current;
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

        let Some(ident) = self.try_identifier() else {
            return Err(ParserError::UnexpectedToken(
                vec![TokenKind::Identifier("_")],
                self.current.unwrap().kind,
            ));
        };

        let TokenKind::Identifier(name) = ident.kind else {
            unreachable!()
        };

        let rhs = if self.did_match(TokenKind::Equals)? {
            Some(self.parse_with_precedence(Precedence::Assignment)?)
        } else {
            None
        };

        let let_expr = self.add_expr(Let(name, rhs));

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
        let name = self.try_identifier();

        self.consume(TokenKind::LeftParen)?;

        let mut params: Vec<ExprID> = vec![];
        while let Some(Token {
            kind: TokenKind::Identifier(name),
            ..
        }) = self.try_identifier()
        {
            let ty_repr = if self.did_match(TokenKind::Colon)? {
                if let Some(Token {
                    kind: TokenKind::Identifier(name),
                    ..
                }) = self.try_identifier()
                {
                    let type_repr = TypeRepr(name);
                    Ok(Some(self.add_expr(type_repr)?))
                } else {
                    Err(ParserError::UnexpectedToken(
                        vec![TokenKind::Identifier("_")],
                        self.current.unwrap().kind,
                    ))
                }
            } else {
                Ok(None)
            }?;

            params.push(self.add_expr(Parameter(name, ty_repr))?);

            if self.did_match(TokenKind::Comma)? {
                continue;
            }

            break;
        }

        self.consume(TokenKind::RightParen)?;

        let ret = if self.did_match(TokenKind::Arrow)? {
            if let Some(Token {
                kind: TokenKind::Identifier(ret_name),
                ..
            }) = self.try_identifier()
            {
                let ret_id = self.add_expr(TypeRepr(ret_name))?;
                Some(ret_id)
            } else {
                None
            }
        } else {
            None
        };

        let body = self.block()?;

        self.add_expr(Expr::Func(
            name.map(|n| FuncName::Token(n)),
            params,
            body,
            ret,
        ))
    }

    pub(crate) fn block(&mut self) -> Result<ExprID, ParserError> {
        self.skip_newlines();

        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<ExprID> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            items.push(self.parse_with_precedence(Precedence::Assignment)?)
        }

        self.add_expr(Expr::Block(items))
    }

    pub(crate) fn variable(&mut self, can_assign: bool) -> Result<ExprID, ParserError> {
        let Some(Token {
            kind: TokenKind::Identifier(name),
            ..
        }) = self.current
        else {
            unreachable!()
        };

        self.consume(TokenKind::Identifier(name))?;
        let variable = self.add_expr(Variable(name))?;

        self.skip_newlines();

        if self.did_match(TokenKind::LeftParen)? {
            self.skip_newlines();
            self.call(variable, can_assign)
        } else {
            Ok(variable)
        }
    }

    pub(crate) fn call(
        &mut self,
        callee: ExprID,
        _can_assign: bool,
    ) -> Result<ExprID, ParserError> {
        let mut args: Vec<ExprID> = vec![];

        if !self.did_match(TokenKind::RightParen)? {
            while {
                args.push(self.parse_with_precedence(Precedence::Assignment)?);
                self.did_match(TokenKind::Comma)?
            } {}

            self.consume(TokenKind::RightParen)?;
        }

        self.add_expr(Expr::Call(callee, args))
    }

    pub(crate) fn unary(&mut self, _can_assign: bool) -> Result<ExprID, ParserError> {
        let op = self.consume_any(vec![TokenKind::Minus, TokenKind::Bang])?;
        let current_precedence = Precedence::handler(Some(op.clone()))?.precedence;
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

        let current_precedence = Precedence::handler(Some(op.clone()))?.precedence;
        let rhs = self
            .parse_with_precedence(current_precedence + 1)
            .expect("did not get binop rhs");

        self.add_expr(Binary(lhs, op.kind, rhs))
    }

    pub fn parse_with_precedence(&mut self, precedence: Precedence) -> Result<ExprID, ParserError> {
        self.skip_newlines();

        let mut lhs: Option<ExprID> = None;
        let mut handler = Precedence::handler(self.current)?;

        if let Some(prefix) = handler.prefix {
            lhs = Some(prefix(self, precedence.can_assign())?);
        }

        let mut i = 0;

        while {
            self.skip_newlines();
            handler = Precedence::handler(self.current)?;
            precedence < handler.precedence
        } {
            i += 1;

            if let Some(infix) = handler.infix {
                if let Some(previous_lhs) = lhs {
                    lhs = Some(infix(self, precedence.can_assign(), previous_lhs)?);
                }
            }

            if i > 100 {
                panic!("we've got a problem");
            }
        }

        #[allow(clippy::expect_fun_call)]
        Ok(lhs.expect(&format!("did not get lhs: {:?}", self.current)))
    }

    // MARK: Helpers

    // Try to get an identifier. If it's a match, return it, otherwise return None
    fn try_identifier(&mut self) -> Option<Token> {
        self.skip_newlines();

        if let Some(current) = self.current {
            if let TokenKind::Identifier(_) = current.kind {
                self.advance();
                return Some(current);
            };
        }

        None
    }

    // Try to get a specific token. If it's a match, return true.
    fn did_match(&mut self, expected: TokenKind) -> Result<bool, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current {
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

        if let Some(current) = self.current {
            if current.kind == expected {
                self.advance();
                return Ok(current.clone());
            };
        }

        Err(ParserError::UnexpectedToken(
            vec![expected],
            self.current.unwrap().kind,
        ))
    }

    fn consume_any(&mut self, possible_tokens: Vec<TokenKind>) -> Result<Token, ParserError> {
        self.skip_newlines();

        match self.current {
            Some(current) => {
                if possible_tokens.contains(&current.kind) {
                    self.advance();
                    Ok(current.clone())
                } else {
                    Err(ParserError::UnexpectedToken(
                        possible_tokens,
                        current.clone().kind,
                    ))
                }
            }
            None => Err(ParserError::UnexpectedEndOfInput(possible_tokens)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        expr::FuncName,
        parser::parse,
        parsing::expr::Expr::{self, *},
        token::Token,
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

        assert_eq!(*hello, Expr::Variable("hello"));
        assert_eq!(*world, Expr::Variable("world"));
    }

    #[test]
    fn parses_unary_bang() {
        let parsed = parse("!hello").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(*expr, Expr::Unary(TokenKind::Bang, 0));
        assert_eq!(*parsed.get(0).unwrap(), Expr::Variable("hello"));
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
        assert_eq!(*parsed.get(2).unwrap(), Expr::Variable("fizz"));
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
            Expr::Func(
                Some(FuncName::Token(Token {
                    kind: TokenKind::Identifier("greet"),
                    start: 6,
                    end: 10,
                })),
                vec![0],
                2,
                None
            )
        );
    }

    #[test]
    fn parses_func_literal_name_no_args() {
        let parsed = parse("func greet() { }").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func(
                Some(FuncName::Token(Token {
                    kind: TokenKind::Identifier("greet"),
                    start: 6,
                    end: 10,
                })),
                vec![],
                0,
                None
            )
        );
        assert_eq!(*parsed.get(0).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_multiple_roots() {
        let parsed = parse("func hello() {}\nfunc world() {}").unwrap();
        assert_eq!(2, parsed.roots().len());
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::Func(
                Some(FuncName::Token(Token {
                    kind: TokenKind::Identifier("hello"),
                    start: 6,
                    end: 10,
                })),
                vec![],
                0,
                None
            )
        );

        assert_eq!(*parsed.get(0).unwrap(), Expr::Block(vec![]));
        assert_eq!(
            *parsed.roots()[1].unwrap(),
            Expr::Func(
                Some(FuncName::Token(Token {
                    kind: TokenKind::Identifier("world"),
                    start: 22,
                    end: 26,
                })),
                vec![],
                2,
                None
            )
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
                Some(FuncName::Token(Token {
                    kind: TokenKind::Identifier("greet"),
                    start: 6,
                    end: 10,
                })),
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
            Expr::Func(
                Some(FuncName::Token(Token {
                    kind: TokenKind::Identifier("greet"),
                    start: 6,
                    end: 10,
                })),
                vec![1],
                2,
                None
            )
        );

        assert_eq!(*parsed.get(1).unwrap(), Parameter("name", Some(0)));
        assert_eq!(*parsed.get(0).unwrap(), TypeRepr("Int"));
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
        assert_eq!(*callee, Expr::Variable("fizz"));
        assert_eq!(args_id.len(), 0);
    }

    #[test]
    fn parses_let() {
        let parsed = parse("let fizz").unwrap();
        let expr = parsed.roots()[0].unwrap();
        assert_eq!(*expr, Expr::Let("fizz", None));
    }

    #[test]
    fn parses_return_type_annotation() {
        let parsed = parse("func fizz() -> Int { 123 }").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func(
                Some(FuncName::Token(Token {
                    kind: TokenKind::Identifier("fizz"),
                    start: 6,
                    end: 9,
                })),
                vec![],
                2,
                Some(0)
            )
        );
    }
}
