use crate::token_kind::TokenKind;
use std::{error::Error, fmt::Display};

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ParserError {
    /// A failure or diagnostic that crossed the frontend ABI (ADR
    /// 0043): the reference code plus its already-rendered message,
    /// with the structured position and expected-token payloads the
    /// editor's ranges and quick fixes read.
    Frontend {
        code: String,
        message: String,
        span: Option<crate::parsing::span::Span>,
        expected: Option<TokenKind>,
    },
    CannotAssign,
    ConversionError(String),
}

impl ParserError {
    pub(crate) fn is_incomplete_input(&self) -> bool {
        match self {
            // Frontend-bridged failures carry the reference renderings:
            // the same three incomplete shapes, detected by code and
            // the frozen message spellings.
            Self::Frontend { code, message, .. } => match code.as_str() {
                "parser.unexpected-end-of-input" => true,
                "parser.unexpected-token" => message.ends_with("got end of input"),
                "parser.lexer" => {
                    message.contains("Unterminated string")
                        || message.contains("Unterminated character literal")
                        || message.contains("Unexpected EOF")
                }
                _ => false,
            },
            Self::CannotAssign | Self::ConversionError(_) => false,
        }
    }

    pub fn code(&self) -> &str {
        match self {
            // A frontend-bridged diagnostic carries the reference's own
            // code string.
            Self::Frontend { code, .. } => code,
            Self::CannotAssign => "parser.cannot-assign",
            Self::ConversionError(_) => "parser.conversion",
        }
    }
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Frontend { message, .. } => write!(f, "{message}"),
            Self::CannotAssign => write!(f, "Cannot assign in this context"),
            Self::ConversionError(msg) => write!(f, "{}", msg),
        }
    }
}

impl Error for ParserError {}
