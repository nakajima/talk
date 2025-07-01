use core::iter::Peekable;
use core::str::Chars;

use super::token::Token;
use super::token_kind::TokenKind::{self, *};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LexerError {
    UnexpectedInput(char),
}

impl LexerError {
    pub fn message(&self) -> String {
        match &self {
            Self::UnexpectedInput(ch) => format!("Unexpected character: {ch:?}"),
        }
    }
}

#[derive(Debug)]
pub struct Lexer<'a> {
    pub code: &'a str,
    chars: Peekable<Chars<'a>>,
    current: u32,
    started: u32,
    line: u32,
    col: u32,
}

impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Self {
        Self {
            code,
            chars: code.chars().peekable(),
            current: 0,
            started: 0,
            line: 0,
            col: 0,
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Token, LexerError> {
        // Skip whitespaces
        loop {
            match self.chars.peek() {
                Some(ch) => {
                    if !ch.is_whitespace() || *ch == '\n' {
                        // Collapse multiple newlines into one
                        if *ch == '\n' {
                            while self.chars.peek() == Some(&'\n') {
                                self.line += 1;
                                self.chars.next();
                                self.current += 1;
                            }

                            self.col = 0;

                            return self.make(Newline);
                        }

                        break;
                    }
                }
                None => {
                    return self.make(EOF);
                }
            }

            self.advance();
        }

        match self.chars.next() {
            Some(char) => self.consume(char),
            None => self.make(EOF),
        }
    }

    fn consume(&mut self, char: char) -> Result<Token, LexerError> {
        self.started = self.current;
        self.current += 1;
        self.col += 1;

        match char {
            '.' => self.make(Dot),
            ',' => self.make(Comma),
            ':' => self.make(Colon),
            '?' => self.make(QuestionMark),
            '+' => self.compound('=', PlusEquals, Plus),
            '-' => self.minus(),
            '*' => self.compound('=', StarEquals, Star),
            '/' => self.compound('=', SlashEquals, Slash),
            '=' => self.compound('=', EqualsEquals, Equals),
            '~' => self.compound('=', TildeEquals, Tilde),
            '!' => self.compound('=', BangEquals, Bang),
            '^' => self.compound('=', CaretEquals, Caret),
            '|' => self.compound('|', PipePipe, Pipe),
            '&' => self.compound('=', AmpEquals, Amp),
            '<' => self.compound('=', LessEquals, Less),
            '>' => self.compound('=', GreaterEquals, Greater),
            '{' => self.make(LeftBrace),
            '}' => self.make(RightBrace),
            '(' => self.make(LeftParen),
            ')' => self.make(RightParen),
            '[' => self.make(LeftBracket),
            ']' => self.make(RightBracket),
            '\n' => self.make(Newline),
            '_' => {
                if let Some(next) = self.chars.peek()
                    && (*next == '_' || next.is_alphanumeric())
                {
                    let ident = self.identifier(self.current - 1);
                    return self.make(ident);
                }

                self.make(Underscore)
            }
            'a'..='z' | 'A'..='Z' => {
                let ident = self.identifier(self.current - 1);
                self.make(ident)
            }
            '0'..='9' => {
                let number = self.number(self.current - 1);
                self.make(number)
            }
            _ => Err(LexerError::UnexpectedInput(char)),
        }
    }

    fn compound(
        &mut self,
        expecting: char,
        found: TokenKind,
        not_found: TokenKind,
    ) -> Result<Token, LexerError> {
        if self.chars.peek() == Some(&expecting) {
            self.advance();
            self.make(found)
        } else {
            self.make(not_found)
        }
    }

    fn identifier(&mut self, starting_at: u32) -> TokenKind {
        while let Some(ch) = self.chars.peek() {
            if ch.is_alphanumeric() || *ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        #[allow(clippy::unwrap_used)]
        let start_idx = self
            .code
            .char_indices()
            .nth(starting_at as usize)
            .unwrap()
            .0;
        #[allow(clippy::unwrap_used)]
        let end_idx = self
            .code
            .char_indices()
            .nth(self.current as usize - 1)
            .unwrap()
            .0;

        match &self.code[start_idx..=end_idx] {
            "func" => Func,
            "let" => Let,
            "if" => If,
            "else" => Else,
            "true" => True,
            "false" => False,
            "loop" => Loop,
            "enum" => Enum,
            "case" => Case,
            "match" => Match,
            "return" => Return,
            "struct" => Struct,
            "break" => Break,
            "init" => Init,
            "protocol" => Protocol,
            _ => Identifier(self.code[start_idx..=end_idx].to_string()),
        }
    }

    fn minus(&mut self) -> Result<Token, LexerError> {
        if self.did_match(&'>') {
            return self.make(Arrow);
        }

        if self.did_match(&'=') {
            return self.make(MinusEquals);
        }

        self.make(Minus)
    }

    fn number(&mut self, starting_at: u32) -> TokenKind {
        let mut is_float = false;

        while let Some(ch) = self.chars.peek() {
            if *ch == '.' {
                is_float = true;
                self.advance();
            } else if ch.is_numeric() || *ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        #[allow(clippy::unwrap_used)]
        let start_idx = self
            .code
            .char_indices()
            .nth(starting_at as usize)
            .unwrap()
            .0;
        #[allow(clippy::unwrap_used)]
        let end_idx = self
            .code
            .char_indices()
            .nth(self.current as usize - 1)
            .unwrap()
            .0;

        if is_float {
            Float(self.code[start_idx..=end_idx].to_string())
        } else {
            Int(self.code[start_idx..=end_idx].to_string())
        }
    }

    fn make(&mut self, kind: TokenKind) -> Result<Token, LexerError> {
        Ok(Token {
            kind,
            start: self.started,
            end: self.current,
            line: self.line,
            col: self.col,
        })
    }

    fn did_match(&mut self, ch: &char) -> bool {
        if Some(ch) == self.chars.peek() {
            self.advance();
            true
        } else {
            false
        }
    }

    pub(crate) fn advance(&mut self) {
        self.col += 1;
        self.current += 1;
        self.chars.next();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn braces() {
        let mut lexer = Lexer::new("{}");
        assert_eq!(lexer.next().unwrap().kind, LeftBrace);
        assert_eq!(lexer.next().unwrap().kind, RightBrace);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn arrow() {
        let mut lexer = Lexer::new("-> Int");
        assert_eq!(lexer.next().unwrap().kind, Arrow);
        assert_eq!(lexer.next().unwrap().kind, Identifier("Int".to_string()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn colon() {
        let mut lexer = Lexer::new(":");
        assert_eq!(lexer.next().unwrap().kind, Colon);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn parens() {
        let mut lexer = Lexer::new("()");
        assert_eq!(lexer.next().unwrap().kind, LeftParen);
        assert_eq!(lexer.next().unwrap().kind, RightParen);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn dot() {
        let mut lexer = Lexer::new("fizz.buzz");
        assert_eq!(lexer.next().unwrap().kind, Identifier("fizz".to_string()));
        assert_eq!(lexer.next().unwrap().kind, Dot);
        assert_eq!(lexer.next().unwrap().kind, Identifier("buzz".to_string()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn identifier() {
        let mut lexer = Lexer::new("hello world");
        assert_eq!(lexer.next().unwrap().kind, Identifier("hello".to_string()));
        assert_eq!(lexer.next().unwrap().kind, Identifier("world".to_string()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn ints() {
        let mut lexer = Lexer::new("123 4_56");
        assert_eq!(lexer.next().unwrap().kind, Int("123".into()));
        assert_eq!(lexer.next().unwrap().kind, Int("4_56".into()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn floats() {
        let mut lexer = Lexer::new("12.3 4.56");
        assert_eq!(lexer.next().unwrap().kind, Float("12.3".into()));
        assert_eq!(lexer.next().unwrap().kind, Float("4.56".into()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn specials() {
        let mut lexer = Lexer::new("+ - / * = ! ~ ^ | & < > ,");
        assert_eq!(lexer.next().unwrap().kind, Plus);
        assert_eq!(lexer.next().unwrap().kind, Minus);
        assert_eq!(lexer.next().unwrap().kind, Slash);
        assert_eq!(lexer.next().unwrap().kind, Star);
        assert_eq!(lexer.next().unwrap().kind, Equals);
        assert_eq!(lexer.next().unwrap().kind, Bang);
        assert_eq!(lexer.next().unwrap().kind, Tilde);
        assert_eq!(lexer.next().unwrap().kind, Caret);
        assert_eq!(lexer.next().unwrap().kind, Pipe);
        assert_eq!(lexer.next().unwrap().kind, Amp);
        assert_eq!(lexer.next().unwrap().kind, Less);
        assert_eq!(lexer.next().unwrap().kind, Greater);
        assert_eq!(lexer.next().unwrap().kind, Comma);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn double_specials() {
        let mut lexer = Lexer::new("+= -= *= /= == != ~= ^= ||  &= <= >=");
        assert_eq!(lexer.next().unwrap().kind, PlusEquals);
        assert_eq!(lexer.next().unwrap().kind, MinusEquals);
        assert_eq!(lexer.next().unwrap().kind, StarEquals);
        assert_eq!(lexer.next().unwrap().kind, SlashEquals);
        assert_eq!(lexer.next().unwrap().kind, EqualsEquals);
        assert_eq!(lexer.next().unwrap().kind, BangEquals);
        assert_eq!(lexer.next().unwrap().kind, TildeEquals);
        assert_eq!(lexer.next().unwrap().kind, CaretEquals);
        assert_eq!(lexer.next().unwrap().kind, PipePipe);
        assert_eq!(lexer.next().unwrap().kind, AmpEquals);
        assert_eq!(lexer.next().unwrap().kind, LessEquals);
        assert_eq!(lexer.next().unwrap().kind, GreaterEquals);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn newlines() {
        let mut lexer = Lexer::new("\n");
        assert_eq!(lexer.next().unwrap().kind, Newline);
        assert_eq!(lexer.next().unwrap().kind, EOF);

        // Collapses multiple newlines into 1
        let mut lexer = Lexer::new("\n\n\n");
        assert_eq!(lexer.next().unwrap().kind, Newline);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn keywords() {
        let mut lexer = Lexer::new("func");
        assert_eq!(lexer.next().unwrap().kind, Func);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn underscore() {
        let mut lexer = Lexer::new("_ _sup");
        assert_eq!(lexer.next().unwrap().kind, Underscore);
        assert_eq!(lexer.next().unwrap().kind, Identifier("_sup".to_string()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }
}
