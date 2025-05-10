use crate::{lexer::Lexer, token::Token, token_kind::TokenKind};

use super::{
    expr::{
        Expr::{self, *},
        ExprMeta,
    },
    parse_tree::ParseTree,
    precedence::Precedence,
};

pub type NodeID = u32;
pub type VariableID = u32;

#[allow(unused)]
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
            if let Some(token) = self.current {
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
        self.previous
    }

    fn add_expr(&mut self, expr: Expr) -> Result<NodeID, ParserError> {
        let expr_meta = ExprMeta {
            start: self.current.unwrap(),
            end: self.current.unwrap(),
        };

        Ok(self.parse_tree.add(expr, expr_meta))
    }

    // MARK: Expr parsers

    pub(crate) fn tuple(&mut self, _can_assign: bool) -> Result<NodeID, ParserError> {
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

    pub(crate) fn literal(&mut self, _can_assign: bool) -> Result<NodeID, ParserError> {
        self.advance();

        match self
            .previous
            .expect("got into #literal without having a token").kind
            
        {
            TokenKind::Int(val) => self.add_expr(LiteralInt(val)),
            TokenKind::Float(val) => self.add_expr(LiteralFloat(val)),
            TokenKind::Func => self.func(),
            _ => unreachable!("didn't get a literal"),
        }
    }

    pub(crate) fn func(&mut self) -> Result<NodeID, ParserError> {
        let name = self.try_identifier();

        self.consume(TokenKind::LeftParen)?;
        let mut params: Vec<NodeID> = vec![];
        while let Some(identifier) = self.try_identifier() {
            let TokenKind::Identifier(name) = identifier.kind else {
                unreachable!()
            };

            params.push(self.add_expr(Variable(name))?);

            if self.did_match(TokenKind::Comma)? {
                continue;
            }

            break;
        }

        let params_id = self.add_expr(Tuple(params))?;

        self.consume(TokenKind::RightParen)?;

        let body = self.block()?;

        self.add_expr(Expr::Func(name, params_id, body))
    }

    pub(crate) fn block(&mut self) -> Result<NodeID, ParserError> {
        self.consume(TokenKind::LeftBrace)?;

        let mut items: Vec<NodeID> = vec![];
        while !self.did_match(TokenKind::RightBrace)? {
            items.push(self.parse_with_precedence(Precedence::Assignment)?)
        }

        self.add_expr(Expr::Block(items))
    }

    pub(crate) fn variable(&mut self, _can_assign: bool) -> Result<NodeID, ParserError> {
        if let Some(token) = self.current {
            if let TokenKind::Identifier(name) = token.kind {
                self.consume(TokenKind::Identifier(name))?;
                return self.add_expr(Variable(name));
            }
        }

        unreachable!()
    }

    pub(crate) fn unary(&mut self, _can_assign: bool) -> Result<NodeID, ParserError> {
        let op = self.consume_any(vec![TokenKind::Minus, TokenKind::Bang])?;
        let current_precedence = Precedence::handler(Some(op))?.precedence;
        let rhs = self
            .parse_with_precedence(current_precedence + 1)
            .expect("did not get binop rhs");

        self.add_expr(Unary(op.kind, rhs))
    }

    pub(crate) fn binary(&mut self, _can_assign: bool, lhs: NodeID) -> Result<NodeID, ParserError> {
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

        let current_precedence = Precedence::handler(Some(op))?.precedence;
        let rhs = self
            .parse_with_precedence(current_precedence + 1)
            .expect("did not get binop rhs");

        self.add_expr(Binary(lhs, op.kind, rhs))
    }

    pub fn parse_with_precedence(&mut self, precedence: Precedence) -> Result<NodeID, ParserError> {
        let mut lhs: Option<NodeID> = None;
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
        if let Some(current) = self.current {
            if current.kind == expected {
                self.advance();
                return Ok(current);
            };
        }

        Err(ParserError::UnexpectedToken(
            vec![expected],
            self.current.unwrap().kind,
        ))
    }

    fn consume_any(&mut self, possible_tokens: Vec<TokenKind>) -> Result<Token, ParserError> {
        match self.current {
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
        assert_eq!(
            *parsed.get(2).unwrap(),
            Expr::Binary(0, TokenKind::Plus, 1)
        );
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
        assert_eq!(
            *parsed.get(2).unwrap(),
            Expr::Binary(0, TokenKind::Plus, 1)
        );
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

        assert_eq!(*expr, Expr::Func(None, 0, 1));
        assert_eq!(*parsed.get(0).unwrap(), Expr::Tuple(vec![]));
        assert_eq!(*parsed.get(1).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_literal_name_no_args() {
        let parsed = parse("func greet() { }").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func(
                Some(Token {
                    kind: TokenKind::Identifier("greet"),
                    start: 6,
                    end: 10,
                }),
                0,
                1
            )
        );
        assert_eq!(*parsed.get(0).unwrap(), Expr::Tuple(vec![]));
        assert_eq!(*parsed.get(1).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_multiple_roots() {
        let parsed = parse("func hello() {}\nfunc world() {}").unwrap();
        assert_eq!(2, parsed.roots().len());
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::Func(
                Some(Token {
                    kind: TokenKind::Identifier("hello"),
                    start: 6,
                    end: 10,
                }),
                0,
                1
            )
        );

        assert_eq!(*parsed.get(1).unwrap(), Expr::Block(vec![]));
        assert_eq!(
            *parsed.roots()[1].unwrap(),
            Expr::Func(
                Some(Token {
                    kind: TokenKind::Identifier("world"),
                    start: 22,
                    end: 26,
                }),
                3,
                4
            )
        );
        assert_eq!(*parsed.get(4).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_literal_name_with_args() {
        let parsed = parse("func greet(one, two) { }").unwrap();
        let expr = parsed.roots()[0].unwrap();

        assert_eq!(
            *expr,
            Expr::Func(
                Some(Token {
                    kind: TokenKind::Identifier("greet"),
                    start: 6,
                    end: 10,
                }),
                2,
                3
            )
        );

        assert_eq!(*parsed.get(2).unwrap(), Tuple(vec![0, 1]));
    }
}
