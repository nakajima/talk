use std::{mem::transmute, ops::Add};

use crate::{token::Token, token_kind::TokenKind};

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
    pub const fn handler(token: Option<Token>) -> Result<ParseHandler, ParserError> {
        let token = match token {
            Some(t) => t,
            None => {
                return Err(ParserError::UnknownError(
                    "did not get token for parser handler",
                ));
            }
        };

        Ok(match token.kind {
            TokenKind::LeftParen => ParseHandler {
                prefix: Some(Parser::grouping),
                infix: None,
                precedence: Precedence::Call,
            },

            TokenKind::Int(_) => ParseHandler {
                prefix: Some(Parser::literal),
                infix: None,
                precedence: Precedence::None,
            },

            TokenKind::Float(_) => ParseHandler {
                prefix: Some(Parser::literal),
                infix: None,
                precedence: Precedence::None,
            },

            TokenKind::Plus => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Term,
            },

            TokenKind::Minus => ParseHandler {
                prefix: Some(Parser::unary),
                infix: Some(Parser::binary),
                precedence: Precedence::Term,
            },

            TokenKind::Star => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Factor,
            },

            TokenKind::Slash => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Factor,
            },

            TokenKind::Less => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Comparison,
            },

            TokenKind::LessEquals => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Comparison,
            },

            TokenKind::Greater => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Comparison,
            },

            TokenKind::GreaterEquals => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Comparison,
            },

            TokenKind::Caret => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Factor,
            },

            TokenKind::Pipe => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Factor,
            },

            TokenKind::Identifier(_) => ParseHandler {
                prefix: Some(Parser::variable),
                infix: None,
                precedence: Precedence::None,
            },

            TokenKind::Newline => ParseHandler::NONE,
            TokenKind::Dot => todo!(),
            TokenKind::Equals => todo!(),
            TokenKind::Bang => todo!(),

            TokenKind::Tilde => todo!(),
            TokenKind::PlusEquals => todo!(),
            TokenKind::MinusEquals => todo!(),
            TokenKind::StarEquals => todo!(),
            TokenKind::SlashEquals => todo!(),
            TokenKind::EqualsEquals => todo!(),
            TokenKind::BangEquals => todo!(),
            TokenKind::TildeEquals => todo!(),

            TokenKind::CaretEquals => todo!(),

            TokenKind::PipePipe => todo!(),
            TokenKind::Amp => todo!(),
            TokenKind::AmpEquals => todo!(),
            TokenKind::LeftBrace => todo!(),
            TokenKind::RightBrace => todo!(),

            TokenKind::RightParen => ParseHandler::NONE,

            TokenKind::Keyword => todo!("keyword"),
            TokenKind::EOF => ParseHandler::NONE,
        })
    }
}

impl Add<u8> for Precedence {
    type Output = Precedence;

    fn add(self, rhs: u8) -> Self::Output {
        unsafe { transmute(self as u8 + rhs) }
    }
}
