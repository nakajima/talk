use crate::{
    lexer::LexerError, parser::BlockContext, span::Span, token::Token, token_kind::TokenKind,
};
use std::{error::Error, fmt::Display};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExpectedSyntax {
    Token(TokenKind),
    Description(String),
}

impl ExpectedSyntax {
    pub fn token(&self) -> Option<TokenKind> {
        match self {
            Self::Token(token) => Some(*token),
            Self::Description(_) => None,
        }
    }
}

impl From<TokenKind> for ExpectedSyntax {
    fn from(value: TokenKind) -> Self {
        Self::Token(value)
    }
}

impl From<String> for ExpectedSyntax {
    fn from(value: String) -> Self {
        Self::Description(value)
    }
}

impl From<&str> for ExpectedSyntax {
    fn from(value: &str) -> Self {
        Self::Description(value.to_string())
    }
}

impl Display for ExpectedSyntax {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Token(token) => write!(f, "{}", token.as_str()),
            Self::Description(description) => f.write_str(description),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ParserError {
    Lexer {
        error: LexerError,
        line: u32,
        col: u32,
    },
    UnexpectedToken {
        expected: ExpectedSyntax,
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
    ExplicitSelfParameterNotAllowed {
        parameter: Span,
    },
    /// A `mut`/`consume` mode on a function-type parameter whose
    /// annotation already spells a borrow (ADR 0018): the mode and the
    /// `&` are rival spellings of the same decision.
    ParamModeBorrowConflict {
        mode: &'static str,
        annotation: Span,
    },
    ConformanceListNotAllowed {
        context: BlockContext,
        token: Option<Token>,
    },
    IncompleteFuncSignature(String),
    ConversionError(String),
}

impl ParserError {
    pub fn code(&self) -> &'static str {
        match self {
            Self::Lexer { .. } => "parser.lexer",
            Self::UnexpectedToken { .. } => "parser.unexpected-token",
            Self::UnexpectedEndOfInput(_) => "parser.unexpected-end-of-input",
            Self::InfiniteLoop(_) => "parser.infinite-loop",
            Self::ExpectedIdentifier(_) => "parser.expected-identifier",
            Self::UnbalancedLocationStack => "parser.unbalanced-location-stack",
            Self::BadLabel(_) => "parser.bad-label",
            Self::CannotAssign => "parser.cannot-assign",
            Self::ExpectedDecl(_) => "parser.expected-declaration",
            Self::LetNotAllowed(_) => "parser.let-not-allowed",
            Self::InitNotAllowed(_) => "parser.init-not-allowed",
            Self::ExplicitSelfParameterNotAllowed { .. } => "parser.explicit-self-parameter",
            Self::ParamModeBorrowConflict { .. } => "parser.param-mode-borrow-conflict",
            Self::ConformanceListNotAllowed { .. } => "parser.conformance-list-not-allowed",
            Self::IncompleteFuncSignature(_) => "parser.incomplete-function-signature",
            Self::ConversionError(_) => "parser.conversion",
        }
    }
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Lexer { error, line, col } => {
                write!(
                    f,
                    "Lex error at line {}, column {}: {}",
                    line + 1,
                    col,
                    error.message()
                )
            }
            Self::UnexpectedEndOfInput(expected) => {
                if let Some(expected) = expected {
                    write!(f, "Unexpected end of input. Expected {expected:?}")
                } else {
                    write!(f, "Unexpected end of input.")
                }
            }
            Self::UnexpectedToken {
                expected, actual, ..
            } => {
                write!(f, "Unexpected token. Expected {expected}, got {actual:?}")
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
            Self::ExplicitSelfParameterNotAllowed { .. } => {
                write!(
                    f,
                    "Methods do not declare `self`; use `func`, `mut func`, or `consuming func`"
                )
            }
            Self::ParamModeBorrowConflict { mode, .. } => {
                write!(
                    f,
                    "Parameter mode `{mode}` conflicts with its type: the annotation is already a borrow. The mode decides borrowing — drop the `&` from the annotation, or drop the mode"
                )
            }
            Self::ConformanceListNotAllowed { context, .. } => write!(
                f,
                "Cannot declare conformances on {context:?}; use an `extend` block instead"
            ),
            Self::IncompleteFuncSignature(msg) => write!(f, "{}", msg),
            Self::ConversionError(msg) => write!(f, "{}", msg),
        }
    }
}

impl Error for ParserError {}
