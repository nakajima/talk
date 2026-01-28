use crate::{node_id::FileID, span::Span};

use super::token_kind::TokenKind;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Token {
    pub kind: TokenKind,
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub col: u32,
}

impl Token {
    pub const EOF: Token = Token {
        kind: TokenKind::EOF,
        start: 0,
        end: 0,
        line: 0,
        col: 0,
    };

    pub const GENERATED: Token = Token {
        kind: TokenKind::Generated,
        start: 0,
        end: 0,
        line: 0,
        col: 0,
    };

    pub fn as_str(&self) -> &'static str {
        self.kind.as_str()
    }

    /// Extract the lexeme text from source code
    pub fn lexeme<'a>(&self, source: &'a str) -> &'a str {
        &source[self.start as usize..self.end as usize]
    }

    pub fn span(&self, file_id: FileID) -> Span {
        Span {
            start: self.start,
            end: self.end,
            file_id,
        }
    }
}
