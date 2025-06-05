use std::{iter::Peekable, str::Chars};

pub enum LexerError {
    UnexpectedInput(char),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Tokind {
    Percent,
    At,
    Hash,
    Comma,
    LeftParen,
    RightParen,
    Func,
    Equals,
    Colon,
    Semicolon,
    Underscore,
    Newline,
    ConstFloat(String),
    ConstInt(String),
    Identifier(String),
    Int,
    Float,
    True,
    False,
    Bool,
    Void,
    Ret,
    Entry,
    EOF,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: Tokind,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug)]
pub struct Lexer<'a> {
    pub code: &'a str,
    chars: Peekable<Chars<'a>>,
    current: usize,
    started: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Self {
        Self {
            code,
            chars: code.chars().peekable(),
            current: 0,
            started: 0,
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
                                self.chars.next();
                                self.current += 1;
                            }

                            return self.make(Tokind::Newline);
                        }

                        break;
                    }
                }
                None => {
                    return self.make(Tokind::EOF);
                }
            }

            self.chars.next();
            self.current += 1;
        }

        match self.chars.next() {
            Some(char) => self.consume(char),
            None => self.make(Tokind::EOF),
        }
    }

    fn consume(&mut self, char: char) -> Result<Token, LexerError> {
        self.current += 1;
        self.started = self.current;

        match char {
            ',' => self.make(Tokind::Comma),
            '(' => self.make(Tokind::LeftParen),
            ')' => self.make(Tokind::RightParen),
            ':' => self.make(Tokind::Colon),
            ';' => self.make(Tokind::Semicolon),
            '%' => self.make(Tokind::Percent),
            '@' => self.make(Tokind::At),
            '#' => self.make(Tokind::Hash),
            '=' => self.make(Tokind::Equals),
            '\n' => self.make(Tokind::Newline),
            '_' => {
                if let Some(next) = self.chars.peek() {
                    if *next == '_' || next.is_alphanumeric() {
                        let ident = self.identifier(self.current - 1);
                        return self.make(ident);
                    }
                }

                self.make(Tokind::Underscore)
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

    fn make(&mut self, kind: Tokind) -> Result<Token, LexerError> {
        Ok(Token {
            kind,
            start: self.started,
            end: self.current,
        })
    }
    fn identifier(&mut self, starting_at: usize) -> Tokind {
        while let Some(ch) = self.chars.peek() {
            if ch.is_alphanumeric() || *ch == '_' {
                self.chars.next();
                self.current += 1;
            } else {
                break;
            }
        }

        let start_idx = self.code.char_indices().nth(starting_at).unwrap().0;
        let end_idx = self.code.char_indices().nth(self.current - 1).unwrap().0;

        match &self.code[start_idx..=end_idx] {
            "func" => Tokind::Func,
            "int" => Tokind::Int,
            "float" => Tokind::Float,
            "bool" => Tokind::Bool,
            "void" => Tokind::Void,
            "entry" => Tokind::Entry,
            "ret" => Tokind::Ret,
            _ => Tokind::Identifier(self.code[start_idx..=end_idx].to_string()),
        }
    }

    fn number(&mut self, starting_at: usize) -> Tokind {
        let mut is_float = false;

        while let Some(ch) = self.chars.peek() {
            if *ch == '.' {
                is_float = true;
                self.chars.next();
                self.current += 1;
            } else if ch.is_numeric() || *ch == '_' {
                self.chars.next();
                self.current += 1;
            } else {
                break;
            }
        }

        let start_idx = self.code.char_indices().nth(starting_at).unwrap().0;
        let end_idx = self.code.char_indices().nth(self.current - 1).unwrap().0;

        if is_float {
            Tokind::ConstFloat(self.code[start_idx..=end_idx].to_string())
        } else {
            Tokind::ConstInt(self.code[start_idx..=end_idx].to_string())
        }
    }
}
