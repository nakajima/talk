use super::token_kind::TokenKind;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Token {
    pub kind: TokenKind,
    pub start: usize,
    pub end: usize,
    pub line: u32,
    pub col: u32,
}

impl Token {
    pub const GENERATED: Token = Token {
        kind: TokenKind::Generated,
        start: 0,
        end: 0,
        line: 0,
        col: 0,
    };

    pub fn as_str(&self) -> String {
        self.kind.as_str()
    }
}
