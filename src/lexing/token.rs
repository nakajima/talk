use super::token_kind::TokenKind;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub start: usize,
    pub end: usize,
}

impl Token {
    pub const GENERATED: Token = Token {
        kind: TokenKind::Generated,
        start: 0,
        end: 0,
    };
}
