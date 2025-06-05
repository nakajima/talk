use std::fmt::Display;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TokenKind {
    // Control flow
    If,
    Else,
    Loop,
    Return,

    True,
    False,

    // Enums/pattern matching
    Enum,
    Case,
    Match,
    Underscore,

    // More
    QuestionMark,
    Arrow,
    Colon,
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
    Int(String),
    Float(String),
    Identifier(String),
    Func,
    Let,
    EOF,
    Generated,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
