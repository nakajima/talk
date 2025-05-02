#[derive(PartialEq, Debug)]
pub enum Token<'a> {
    LeftBrace,
    RightBrace,
    LeftParen,
    RightParen,
    Identifier(&'a str),
    Keyword,
    EOF,
}
