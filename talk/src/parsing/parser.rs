use crate::{lexer::Lexer, tokens::Token};

use super::expr::Expr;

#[allow(unused)]
pub struct Parser<'a> {
    lexer: &'a mut Lexer<'a>,
    previous: Option<Token<'a>>,
    current: Option<Token<'a>>,
}

#[derive(Debug)]
pub struct ParseError {}

pub struct ParseTree<'a> {
    root: usize,
    nodes: Vec<Expr<'a>>,
}

impl<'a> ParseTree<'a> {
    pub fn root(&'a self) -> Option<&'a Expr<'a>> {
        if self.nodes.len() <= self.root {
            None
        } else {
            Some(&self.nodes[self.root])
        }
    }
}

impl<'a> Parser<'a> {
    pub fn parse(_code: &str) -> Result<ParseTree, ParseError> {
        Ok(ParseTree {
            root: 0,
            nodes: vec![],
        })
    }

    pub fn new(lexer: &'a mut Lexer<'a>) -> Self {
        Self {
            lexer,
            previous: None,
            current: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parsing::expr::ExprKind;

    use super::Parser;

    #[test]
    fn parses_literal_expr() {
        let parsed = Parser::parse("123").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::LiteralInt);
    }

    #[test]
    fn parses_binary_expr() {
        let parsed = Parser::parse("1 + 2").unwrap();
        let expr = parsed.root().unwrap();

        assert_eq!(expr.kind, ExprKind::Binary(0, 2));
    }
}
