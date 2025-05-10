use std::fmt::Display;

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum TokenKind {
    Newline,
    Dot,
    Plus,
    Minus,
    Slash,
    Star,
    Equals,
    Bang,
    Less,
    LessEquals,
    Greater,
    GreaterEquals,
    Tilde,
    PlusEquals,
    MinusEquals,
    StarEquals,
    SlashEquals,
    EqualsEquals,
    BangEquals,
    TildeEquals,
    Caret,
    CaretEquals,
    Pipe,
    PipePipe,
    Amp,
    AmpEquals,
    LeftBrace,
    RightBrace,
    LeftParen,
    RightParen,
    Comma,
    Int(&'static str),
    Float(&'static str),
    Identifier(&'static str),
    Func,
    EOF,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
