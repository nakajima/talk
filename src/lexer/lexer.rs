use core::iter::Peekable;
use core::str::Chars;

use super::tokens::Token::*;
use super::tokens::*;

#[derive(Debug)]
pub enum LexerError {
    UnexpectedInput(char),
}

#[derive(Debug)]
struct Lexer<'a> {
    code: &'a str,
    chars: Peekable<Chars<'a>>,
    current: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Self {
        Self {
            code,
            chars: code.chars().peekable(),
            current: 0,
        }
    }

    pub fn next(&mut self) -> Result<Token, LexerError> {
        // Skip whitespaces
        loop {
            match self.chars.peek() {
                Some(ch) => {
                    if !ch.is_whitespace() {
                        break;
                    }
                }
                None => {
                    return Ok(EOF);
                }
            }

            self.chars.next();
            self.current += 1;
        }

        match self.chars.next() {
            Some(char) => self.consume(char),
            None => Ok(Token::EOF),
        }
    }

    fn consume(&mut self, char: char) -> Result<Token, LexerError> {
        self.current += 1;

        let result = match char {
            '{' => Ok(LeftBrace),
            '}' => Ok(RightBrace),
            '(' => Ok(LeftParen),
            ')' => Ok(RightParen),
            'a'..='z' | 'A'..='Z' | '_' => Ok(self.identifier(self.current - 1)),
            _ => Err(LexerError::UnexpectedInput(char)),
        };

        result
    }

    fn identifier<'b>(&'b mut self, starting_at: usize) -> Token<'a> {
        while let Some(ch) = self.chars.peek() {
            if ch.is_alphanumeric() {
                self.chars.next();
                self.current += 1;
            } else {
                break;
            }
        }

        let start_idx = self.code.char_indices().nth(starting_at).unwrap().0;
        let end_idx = self.code.char_indices().nth(self.current - 1).unwrap().0;

        Identifier(&self.code[start_idx..=end_idx])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn braces() {
        let mut lexer = Lexer::new("{}");
        assert_eq!(lexer.next().unwrap(), LeftBrace);
        assert_eq!(lexer.next().unwrap(), RightBrace);
        assert_eq!(lexer.next().unwrap(), EOF);
    }

    #[test]
    fn parens() {
        let mut lexer = Lexer::new("()");
        assert_eq!(lexer.next().unwrap(), LeftParen);
        assert_eq!(lexer.next().unwrap(), RightParen);
        assert_eq!(lexer.next().unwrap(), EOF);
    }

    #[test]
    fn identifier() {
        let mut lexer = Lexer::new("hello world");
        assert_eq!(lexer.next().unwrap(), Identifier("hello"));
        assert_eq!(lexer.next().unwrap(), Identifier("world"));
        assert_eq!(lexer.next().unwrap(), EOF);
    }
}
