use crate::{lexer::Lexer, token::Token, token_kind::TokenKind};

use super::{
    expr::{Expr, ExprKind, ExprKind::*},
    parse_tree::ParseTree,
    precedence::Precedence,
};

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

        if let Some(current) = self.current {
            if current.kind == TokenKind::EOF {
                return;
            }

            let expr = self
                .parse_with_precedence(Precedence::Assignment)
                .expect("did not get an expr");

            self.parse_tree.root = expr.id;
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

    fn add_expr(&mut self, kind: ExprKind) -> Result<Expr, ParserError> {
        let mut expr = Expr {
            id: 0,
            start: self.current.unwrap(),
            end: self.current.unwrap(),
            kind,
        };
        expr.id = self.parse_tree.add(expr);
        Ok(expr)
    }

    // MARK: Expr parsers

    pub(crate) fn grouping(&mut self, _can_assign: bool) -> Result<Expr, ParserError> {
        self.consume_any(vec![TokenKind::LeftParen])?;
        let child = self.parse_with_precedence(Precedence::Assignment)?;
        self.consume_any(vec![TokenKind::RightParen])?;
        self.add_expr(Grouping(child.id))
    }

    pub(crate) fn literal(&mut self, _can_assign: bool) -> Result<Expr, ParserError> {
        self.advance();

        match self
            .previous
            .expect("got into #literal without having a token")
            .kind
        {
            TokenKind::Int(val) => self.add_expr(LiteralInt(val)),
            TokenKind::Float(val) => self.add_expr(LiteralFloat(val)),
            _ => unreachable!("didn't get a literal"),
        }
    }

    pub(crate) fn variable(&mut self, _can_assign: bool) -> Result<Expr, ParserError> {
        if let Some(token) = self.current {
            if let TokenKind::Identifier(name) = token.kind {
                self.consume(TokenKind::Identifier(name))?;
                return self.add_expr(Variable(name));
            }
        }

        unreachable!()
    }

    pub(crate) fn unary(&mut self, _can_assign: bool) -> Result<Expr, ParserError> {
        todo!()
    }

    pub(crate) fn binary(&mut self, _can_assign: bool, lhs: Expr) -> Result<Expr, ParserError> {
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

        self.add_expr(Binary(lhs.id, rhs.id, op.kind))
    }

    pub fn parse_with_precedence(&mut self, precedence: Precedence) -> Result<Expr, ParserError> {
        let mut lhs: Option<Expr> = None;
        let mut handler = Precedence::handler(self.current)?;

        if let Some(prefix) = handler.prefix {
            lhs = Some(prefix(self, precedence.can_assign())?);
        }

        let mut i = 0;

        while {
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

        Ok(lhs.expect("did not get lhs"))
    }

    // MARK: Helpers

    fn consume(&mut self, expected: TokenKind) -> Result<Token, ParserError> {
        if let Some(current) = self.current {
            if current.kind == expected {
                self.advance();
                return Ok(current);
            };
        }

        return Err(ParserError::UnexpectedToken(
            vec![expected],
            self.current.unwrap().kind,
        ));
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
        parsing::expr::ExprKind::{self, *},
        token_kind::TokenKind,
    };

    #[test]
    fn parses_literal_expr() {
        let parsed = parse("123").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, LiteralInt("123"));
    }

    #[test]
    fn parses_plus_expr() {
        let parsed = parse("1 + 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::Plus));
    }

    #[test]
    fn parses_minus_expr() {
        let parsed = parse("1 - 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::Minus));
    }

    #[test]
    fn parses_div_expr() {
        let parsed = parse("1 / 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::Slash));
    }

    #[test]
    fn parses_mult_expr() {
        let parsed = parse("1 * 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::Star));
    }

    #[test]
    fn parses_less_expr() {
        let parsed = parse("1 < 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::Less));
    }

    #[test]
    fn parses_less_equals_expr() {
        let parsed = parse("1 <= 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::LessEquals));
    }

    #[test]
    fn parses_greater_expr() {
        let parsed = parse("1 > 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::Greater));
    }

    #[test]
    fn parses_greater_equals_expr() {
        let parsed = parse("1 >= 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::GreaterEquals));
    }

    #[test]
    fn parses_caret_expr() {
        let parsed = parse("1 ^ 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::Caret));
    }

    #[test]
    fn parses_pipe_expr() {
        let parsed = parse("1 | 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, TokenKind::Pipe));
    }

    #[test]
    fn parses_correct_precedence() {
        let parsed = parse("1 + 2 * 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(2, 3, TokenKind::Star));
        assert_eq!(
            parsed.get(2).unwrap().kind,
            ExprKind::Binary(0, 1, TokenKind::Plus)
        );
    }

    #[test]
    fn parses_group() {
        let parsed = parse("(1 + 2) * 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(3, 4, TokenKind::Star));
        assert_eq!(parsed.get(3).unwrap().kind, ExprKind::Grouping(2));
    }

    #[test]
    fn parses_var() {
        let parsed = parse("hello").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Variable("hello"));
    }
}
