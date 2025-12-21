use crate::{parser::BlockContext, token::Token, token_kind::TokenKind};
use std::{error::Error, fmt::Display};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ParserError {
    UnexpectedToken {
        expected: String,
        actual: String,
        token: Option<Token>,
    },
    UnexpectedEndOfInput(Option<String>),
    InfiniteLoop(Option<Token>),
    ExpectedIdentifier(Option<Token>),
    UnbalancedLocationStack,
    BadLabel(String),
    CannotAssign,
    ExpectedDecl(TokenKind),
    LetNotAllowed(BlockContext),
    InitNotAllowed(BlockContext),
    IncompleteFuncSignature(String),
    ConversionError(String),
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedEndOfInput(expected) => {
                if let Some(expected) = expected {
                    write!(f, "Unexpected end of input. Expected {expected:?}")
                } else {
                    write!(f, "Unexpected end of input.")
                }
            }
            Self::UnexpectedToken { expected, actual, .. } => {
                write!(f, "Unexpected token. Expected {expected:?}, got {actual:?}")
            }
            Self::InfiniteLoop(current) => {
                write!(
                    f,
                    "Parser failed to make forward progress. Stuck at {current:?}"
                )
            }
            Self::UnbalancedLocationStack => {
                write!(f, "Unbalanced source location stack")
            }
            Self::ExpectedIdentifier(current) => {
                write!(f, "Expected identifier, got: {current:?}")
            }
            Self::BadLabel(label) => write!(f, "Unable to parse label: {label}"),
            Self::CannotAssign => write!(f, "Cannot assign in this context"),
            Self::ExpectedDecl(actual) => write!(f, "Expected declaration, got {actual:?}"),
            Self::LetNotAllowed(context) => write!(f, "Cannot use `let` in {context:?} body"),
            Self::InitNotAllowed(_context) => write!(f, "Cannot use `init` in this context"),
            Self::IncompleteFuncSignature(msg) => write!(f, "{}", msg),
            Self::ConversionError(msg) => write!(f, "{}", msg),
        }
    }
}

impl Error for ParserError {}
