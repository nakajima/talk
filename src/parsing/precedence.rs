use std::{mem::transmute, ops::Add};

use crate::tokens::Token;

use super::{
    expr::Expr,
    parser::{Parser, ParserError},
};

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Precedence {
    None,
    Assignment, // =
    Or,
    And,
    Equality,
    Comparison,
    Term,
    Factor, // *
    Unary,  // - !
    Call,
    Primary,
    Any,
}

impl Precedence {
    pub fn can_assign(&self) -> bool {
        self <= &Precedence::Assignment
    }
}

#[allow(clippy::type_complexity)]
pub struct ParseHandler {
    pub(crate) prefix: Option<fn(&mut Parser, bool) -> Result<Expr, ParserError>>,
    pub(crate) infix: Option<fn(&mut Parser, bool, Expr) -> Result<Expr, ParserError>>,
    pub(crate) precedence: Precedence,
}

impl ParseHandler {
    const NONE: ParseHandler = ParseHandler {
        prefix: None,
        infix: None,
        precedence: Precedence::None,
    };
}

impl Precedence {
    pub fn handler(token: Token) -> ParseHandler {
        match token {
            Token::LeftParen => ParseHandler {
                prefix: Some(Parser::grouping),
                infix: None,
                precedence: Precedence::Call,
            },

            Token::Int(_) => ParseHandler {
                prefix: Some(Parser::literal),
                infix: None,
                precedence: Precedence::None,
            },

            Token::Float(_) => ParseHandler {
                prefix: Some(Parser::literal),
                infix: None,
                precedence: Precedence::None,
            },

            Token::Plus => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Term,
            },

            Token::Newline => ParseHandler::NONE,
            Token::Dot => todo!(),

            Token::Minus => todo!(),
            Token::Slash => todo!(),
            Token::Star => todo!(),
            Token::Equals => todo!(),
            Token::Bang => todo!(),
            Token::Less => todo!(),
            Token::LessEquals => todo!(),
            Token::Greater => todo!(),
            Token::GreaterEquals => todo!(),
            Token::Tilde => todo!(),
            Token::PlusEquals => todo!(),
            Token::MinusEquals => todo!(),
            Token::StarEquals => todo!(),
            Token::SlashEquals => todo!(),
            Token::EqualsEquals => todo!(),
            Token::BangEquals => todo!(),
            Token::TildeEquals => todo!(),
            Token::Caret => todo!(),
            Token::CaretEquals => todo!(),
            Token::Pipe => todo!(),
            Token::PipePipe => todo!(),
            Token::Amp => todo!(),
            Token::AmpEquals => todo!(),
            Token::LeftBrace => todo!(),
            Token::RightBrace => todo!(),

            Token::RightParen => todo!(),

            Token::Identifier(_) => todo!(),
            Token::Keyword => todo!(),
            Token::EOF => ParseHandler::NONE,
        }
    }
}

impl Add<u8> for Precedence {
    type Output = Precedence;

    fn add(self, rhs: u8) -> Self::Output {
        unsafe { transmute(self as u8 + rhs) }
    }
}
