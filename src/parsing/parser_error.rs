use crate::{
    lexing::LexerError, span::Span, token::Token, token_kind::TokenKind,
};
use std::{error::Error, fmt::Display};

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
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
            Self::Token(token) => write!(f, "`{}`", token.as_str()),
            Self::Description(description) => f.write_str(description),
        }
    }
}

#[derive(PartialEq, Clone, Copy, Debug, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub enum BlockContext {
    Struct,
    Protocol,
    Enum,
    Func,
    If,
    Loop,
    MatchArmBody,
    Extend,
    None,
}

impl BlockContext {
    pub fn allows_conformances(&self) -> bool {
        matches!(self, BlockContext::Extend | BlockContext::Protocol)
    }
}

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
    /// `use` inside a block-items parse (ADR 0043 category entry):
    /// imports are file-level only.
    ImportInBlockItems,
    InfiniteLoop(Option<Token>),
    ExpectedIdentifier(Option<Token>),
    UnbalancedLocationStack,
    BadLabel(String),
    IntegerLiteralOutOfRange {
        literal: String,
    },
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
    /// Static generic parameters follow the generic-parameter naming
    /// convention (ADR 0035): `static N: Int` is valid, `static n: Int`
    /// is not.
    LowercaseStaticParameter {
        name: String,
        span: Span,
    },
    /// The removed `public` spelling (ADR 0042); the modifier is `pub`.
    LegacyPublicModifier {
        span: Span,
    },
    /// `pub` on a declaration or position that admits no visibility
    /// modifier (ADR 0042 declaration matrix).
    VisibilityNotAllowed {
        what: &'static str,
        span: Span,
    },
    RepeatedVisibilityModifier {
        span: Span,
    },
    /// `pub macro` awaits an accepted macro-export design (ADR 0042).
    MacroExportUnsupported {
        span: Span,
    },
}

impl ParserError {
    pub(crate) fn is_incomplete_input(&self) -> bool {
        match self {
            Self::UnexpectedEndOfInput(_) => true,
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
            Self::UnexpectedToken {
                token: Some(token), ..
            } => token.kind == TokenKind::EOF,
            Self::Lexer { error, .. } => matches!(
                error,
                LexerError::UnexpectedEOF
                    | LexerError::UnterminatedCharacterLiteral
                    | LexerError::UnterminatedString
            ),
            _ => false,
        }
    }

    pub fn code(&self) -> &'static str {
        match self {
            // A frontend-bridged diagnostic carries the reference's own
            // code string; the closed set maps back to the static codes.
            Self::Frontend { code, .. } => match code.as_str() {
                "parser.lexer" => "parser.lexer",
                "parser.unexpected-token" => "parser.unexpected-token",
                "parser.import-in-block-items" => "parser.import-in-block-items",
                "parser.unexpected-end-of-input" => "parser.unexpected-end-of-input",
                "parser.infinite-loop" => "parser.infinite-loop",
                "parser.expected-identifier" => "parser.expected-identifier",
                "parser.bad-label" => "parser.bad-label",
                "parser.integer-literal-out-of-range" => "parser.integer-literal-out-of-range",
                "parser.cannot-assign" => "parser.cannot-assign",
                "parser.expected-declaration" => "parser.expected-declaration",
                "parser.let-not-allowed" => "parser.let-not-allowed",
                "parser.init-not-allowed" => "parser.init-not-allowed",
                "parser.explicit-self-parameter" => "parser.explicit-self-parameter",
                "parser.param-mode-borrow-conflict" => "parser.param-mode-borrow-conflict",
                "parser.conformance-list-not-allowed" => "parser.conformance-list-not-allowed",
                "parser.lowercase-static-parameter" => "parser.lowercase-static-parameter",
                "parser.macro-export-unsupported" => "parser.macro-export-unsupported",
                "parser.incomplete-function-signature" => "parser.incomplete-function-signature",
                _ => "parser.frontend",
            },
            Self::Lexer { .. } => "parser.lexer",
            Self::UnexpectedToken { .. } => "parser.unexpected-token",
            Self::ImportInBlockItems => "parser.import-in-block-items",
            Self::UnexpectedEndOfInput(_) => "parser.unexpected-end-of-input",
            Self::InfiniteLoop(_) => "parser.infinite-loop",
            Self::ExpectedIdentifier(_) => "parser.expected-identifier",
            Self::UnbalancedLocationStack => "parser.unbalanced-location-stack",
            Self::BadLabel(_) => "parser.bad-label",
            Self::IntegerLiteralOutOfRange { .. } => "parser.integer-literal-out-of-range",
            Self::CannotAssign => "parser.cannot-assign",
            Self::ExpectedDecl(_) => "parser.expected-declaration",
            Self::LetNotAllowed(_) => "parser.let-not-allowed",
            Self::InitNotAllowed(_) => "parser.init-not-allowed",
            Self::ExplicitSelfParameterNotAllowed { .. } => "parser.explicit-self-parameter",
            Self::ParamModeBorrowConflict { .. } => "parser.param-mode-borrow-conflict",
            Self::ConformanceListNotAllowed { .. } => "parser.conformance-list-not-allowed",
            Self::IncompleteFuncSignature(_) => "parser.incomplete-function-signature",
            Self::ConversionError(_) => "parser.conversion",
            Self::LowercaseStaticParameter { .. } => "parser.lowercase-static-parameter",
            Self::LegacyPublicModifier { .. } => "parser.legacy-public-modifier",
            Self::VisibilityNotAllowed { .. } => "parser.visibility-not-allowed",
            Self::RepeatedVisibilityModifier { .. } => "parser.repeated-visibility-modifier",
            Self::MacroExportUnsupported { .. } => "parser.macro-export-unsupported",
        }
    }
}

/// A token kind described for a user-facing message: literal spellings
/// in backticks, classes of token in words.
fn describe_kind(kind: &TokenKind) -> String {
    match kind {
        TokenKind::EOF => "end of input".into(),
        TokenKind::Newline => "a newline".into(),
        TokenKind::Identifier => "an identifier".into(),
        TokenKind::Int => "an integer literal".into(),
        TokenKind::Float => "a float literal".into(),
        TokenKind::StringLiteral => "a string literal".into(),
        TokenKind::CharacterLiteral => "a character literal".into(),
        other => format!("`{}`", other.as_str()),
    }
}

fn describe(token: &Option<Token>) -> String {
    match token {
        Some(token) => describe_kind(&token.kind),
        None => "end of input".into(),
    }
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Frontend { message, .. } => write!(f, "{message}"),
            Self::ImportInBlockItems => {
                write!(f, "imports are not allowed in block items")
            }
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
                    write!(f, "Unexpected end of input; expected {expected}")
                } else {
                    write!(f, "Unexpected end of input")
                }
            }
            Self::UnexpectedToken {
                expected,
                actual,
                token,
            } => {
                // The token names itself when present; `actual` is the
                // fallback for sites without one.
                let got = match token {
                    Some(token) => describe_kind(&token.kind),
                    None => actual.clone(),
                };
                write!(f, "Unexpected token: expected {expected}, got {got}")
            }
            Self::InfiniteLoop(current) => {
                write!(
                    f,
                    "Parser failed to make forward progress at {}",
                    describe(current)
                )
            }
            Self::UnbalancedLocationStack => {
                write!(f, "Unbalanced source location stack")
            }
            Self::ExpectedIdentifier(current) => {
                write!(f, "Expected an identifier, got {}", describe(current))
            }
            Self::BadLabel(label) => write!(f, "Unable to parse label: {label}"),
            Self::IntegerLiteralOutOfRange { literal } => write!(
                f,
                "Integer literal {literal} is outside the signed 64-bit range"
            ),
            Self::CannotAssign => write!(f, "Cannot assign in this context"),
            Self::ExpectedDecl(actual) => {
                write!(f, "Expected a declaration, got {}", describe_kind(actual))
            }
            Self::LetNotAllowed(context) => write!(
                f,
                "Cannot use `let` in {} body",
                format!("{context:?}").to_lowercase()
            ),
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
                "Cannot declare conformances on {}; use an `extend` block instead",
                format!("{context:?}").to_lowercase()
            ),
            Self::IncompleteFuncSignature(msg) => write!(f, "{}", msg),
            Self::ConversionError(msg) => write!(f, "{}", msg),
            Self::LowercaseStaticParameter { name, .. } => write!(
                f,
                "Static generic parameter `{name}` must begin with an uppercase letter"
            ),
            Self::LegacyPublicModifier { .. } => {
                write!(f, "`public` was renamed to `pub`; replace `public` with `pub`")
            }
            Self::VisibilityNotAllowed { what, .. } => {
                write!(f, "`pub` is not allowed on {what}")
            }
            Self::RepeatedVisibilityModifier { .. } => {
                write!(f, "Repeated visibility modifier; write `pub` once")
            }
            Self::MacroExportUnsupported { .. } => {
                write!(f, "Macros cannot be exported; remove `pub`")
            }
        }
    }
}

impl Error for ParserError {}
