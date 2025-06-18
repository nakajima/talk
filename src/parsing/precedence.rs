use std::{mem::transmute, ops::Add};

use crate::{token::Token, token_kind::TokenKind};

use super::parser::{ExprID, Parser, ParserError};

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

#[derive(Debug)]
#[allow(clippy::type_complexity)]
pub struct ParseHandler<'a> {
    pub(crate) prefix: Option<fn(&mut Parser<'a>, bool) -> Result<ExprID, ParserError>>,
    pub(crate) infix: Option<fn(&mut Parser<'a>, bool, ExprID) -> Result<ExprID, ParserError>>,
    pub(crate) precedence: Precedence,
}

impl<'a> ParseHandler<'a> {
    const NONE: ParseHandler<'a> = ParseHandler {
        prefix: None,
        infix: None,
        precedence: Precedence::None,
    };
}

impl Precedence {
    pub fn handler<'a>(token: &Option<Token>) -> Result<ParseHandler<'a>, ParserError> {
        let token = match token {
            Some(t) => t,
            None => {
                return Err(ParserError::UnknownError(
                    "did not get token for parser handler",
                ));
            }
        };

        log::trace!("getting handler for {token:?}");

        Ok(match &token.kind {
            TokenKind::LeftParen => ParseHandler {
                prefix: Some(Parser::tuple),
                infix: Some(Parser::call_infix),
                precedence: Precedence::Call,
            },

            TokenKind::If => ParseHandler {
                prefix: Some(Parser::if_expr),
                infix: None,
                precedence: Precedence::Primary,
            },
            TokenKind::Else => ParseHandler::NONE,
            TokenKind::Loop => ParseHandler {
                prefix: Some(Parser::loop_expr),
                infix: None,
                precedence: Precedence::None,
            },

            TokenKind::Match => ParseHandler {
                prefix: Some(Parser::match_expr),
                infix: None,
                precedence: Precedence::Primary,
            },

            TokenKind::Return => ParseHandler {
                prefix: Some(Parser::return_expr),
                infix: None,
                precedence: Precedence::Primary,
            },

            TokenKind::Break => ParseHandler {
                prefix: Some(Parser::break_expr),
                infix: None,
                precedence: Precedence::Primary
            },

            TokenKind::True => ParseHandler {
                prefix: Some(Parser::boolean),
                infix: None,
                precedence: Precedence::None,
            },

            TokenKind::False => ParseHandler {
                prefix: Some(Parser::boolean),
                infix: None,
                precedence: Precedence::None,
            },

            TokenKind::Enum => ParseHandler {
                prefix: Some(Parser::enum_decl),
                infix: None,
                precedence: Precedence::Call,
            },

            TokenKind::LeftBrace => ParseHandler {
                prefix: Some(Parser::block),
                infix: None,
                precedence: Precedence::Call,
            },

            TokenKind::Struct => ParseHandler {
                prefix: Some(Parser::struct_expr),
                infix: None,
                precedence: Precedence::Call,
            },

            TokenKind::LeftBracket => ParseHandler {
                prefix: Some(Parser::array_literal),
                infix: None,
                precedence: Precedence::Call,
            },

            TokenKind::Int(_) => ParseHandler {
                prefix: Some(Parser::literal),
                infix: None,
                precedence: Precedence::Primary,
            },

            TokenKind::Float(_) => ParseHandler {
                prefix: Some(Parser::literal),
                infix: None,
                precedence: Precedence::Primary,
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

            TokenKind::EqualsEquals => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Equality,
            },

            TokenKind::BangEquals => ParseHandler {
                prefix: None,
                infix: Some(Parser::binary),
                precedence: Precedence::Equality,
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

            TokenKind::Func => ParseHandler {
                prefix: Some(Parser::literal),
                infix: None,
                precedence: Precedence::Assignment,
            },

            TokenKind::Let => ParseHandler {
                prefix: Some(Parser::let_expr),
                infix: None,
                precedence: Precedence::None,
            },

            TokenKind::Newline => ParseHandler::NONE,
            TokenKind::Dot => ParseHandler {
                prefix: Some(Parser::member_prefix),
                infix: Some(Parser::member_infix),
                precedence: Precedence::Call,
            },
            TokenKind::Equals => ParseHandler::NONE,
            TokenKind::Bang => ParseHandler {
                prefix: Some(Parser::unary),
                infix: None,
                precedence: Precedence::Factor,
            },

            TokenKind::Tilde => ParseHandler::NONE,
            TokenKind::PlusEquals => ParseHandler::NONE,
            TokenKind::MinusEquals => ParseHandler::NONE,
            TokenKind::StarEquals => ParseHandler::NONE,
            TokenKind::SlashEquals => ParseHandler::NONE,

            TokenKind::TildeEquals => ParseHandler::NONE,

            TokenKind::CaretEquals => ParseHandler::NONE,

            TokenKind::PipePipe => ParseHandler::NONE,
            TokenKind::Amp => ParseHandler::NONE,
            TokenKind::AmpEquals => ParseHandler::NONE,

            TokenKind::RightBrace => ParseHandler::NONE,
            TokenKind::RightParen => ParseHandler::NONE,
            TokenKind::Comma => ParseHandler::NONE,
            TokenKind::EOF => ParseHandler::NONE,
            TokenKind::Colon => ParseHandler::NONE,
            TokenKind::Arrow => ParseHandler::NONE,
            _ => ParseHandler::NONE,
        })
    }
}

impl Add<u8> for Precedence {
    type Output = Precedence;

    fn add(self, rhs: u8) -> Self::Output {
        unsafe { transmute(self as u8 + rhs) }
    }
}
