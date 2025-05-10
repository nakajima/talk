use super::token_kind::TokenKind;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub start: usize,
    pub end: usize,
}
