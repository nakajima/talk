use crate::{lexer::Lexer, tokens::Token};

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
pub struct ParserError {}

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
            if current == Token::EOF {
                return;
            }

            let expr = self
                .parse_with_precedence(Precedence::Assignment)
                .expect("did not get an expr");

            self.parse_tree.root = expr.id;
        }
    }

    fn skip_newlines(&mut self) {
        while let Some(Token::Newline) = self.current {
            self.advance();
        }
    }

    fn advance(&mut self) {
        self.previous = self.current;
        self.current = self.lexer.next().ok();
    }

    fn add_expr(&mut self, kind: ExprKind) -> Expr {
        let mut expr = Expr {
            id: 0,
            start: self.current.unwrap(),
            end: self.current.unwrap(),
            kind,
        };
        expr.id = self.parse_tree.add(expr);
        expr
    }

    pub(crate) fn grouping(&mut self, _can_assign: bool) -> Result<Expr, ParserError> {
        Err(ParserError {})
    }

    pub(crate) fn literal(&mut self, _can_assign: bool) -> Result<Expr, ParserError> {
        self.advance();

        match self
            .previous
            .expect("got into #literal without having a token")
        {
            Token::Int(val) => Ok(self.add_expr(LiteralInt(val))),
            Token::Float(val) => Ok(self.add_expr(LiteralFloat(val))),
            _ => unreachable!("didn't get a literal"),
        }
    }

    pub(crate) fn binary(&mut self, _can_assign: bool, lhs: Expr) -> Result<Expr, ParserError> {
        // parse(precedence: current.kind.rule.precedence + 1)

        let op = self.current.expect("did not get current token");
        self.advance();

        println!("OP: {:?}", op);

        let current_precedence = Precedence::handler(op).precedence;
        let rhs = self
            .parse_with_precedence(current_precedence + 1)
            .expect("did not get binop rhs");

        Ok(self.add_expr(Binary(lhs.id, rhs.id, op)))
    }

    pub fn parse_with_precedence(&mut self, precedence: Precedence) -> Result<Expr, ParserError> {
        let mut lhs: Option<Expr> = None;
        let mut handler = Precedence::handler(
            self.current
                .expect("did not have current token for parsing"),
        );

        if let Some(prefix) = handler.prefix {
            lhs = Some(prefix(self, precedence.can_assign())?);
        }

        println!("lhs: {:?}", lhs);
        println!("current: {:?}", self.current);
        println!("precedence: {:?} {:?}", precedence, precedence as u8);
        println!(
            "current precedence: {:?} {:?}",
            Precedence::handler(
                self.current
                    .expect("did not have current token for parsing"),
            )
            .precedence,
            Precedence::handler(
                self.current
                    .expect("did not have current token for parsing"),
            )
            .precedence as u8
        );

        let mut i = 0;

        while {
            handler = Precedence::handler(
                self.current
                    .expect("did not have current token for parsing"),
            );

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
}

#[cfg(test)]
mod tests {
    use crate::{
        parser::parse,
        parsing::expr::ExprKind::{self, *},
        tokens::Token,
    };

    #[test]
    fn parses_literal_expr() {
        let parsed = parse("123").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, LiteralInt("123"));
    }

    #[test]
    fn parses_binary_expr() {
        let parsed = parse("1 + 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 1, Token::Plus));
    }
}
