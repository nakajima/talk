use core::iter::Peekable;
use core::str::Chars;

use super::tokens::Token::*;
use super::tokens::*;

#[derive(Debug)]
pub enum LexerError {
    UnexpectedInput(char),
}

#[derive(Debug)]
pub struct Lexer {
    code: &'static str,
    chars: Peekable<Chars<'static>>,
    current: usize,
}

impl Lexer {
    pub fn new(code: &'static str) -> Self {
        Self {
            code,
            chars: code.chars().peekable(),
            current: 0,
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Token, LexerError> {
        // Skip whitespaces
        loop {
            match self.chars.peek() {
                Some(ch) => {
                    if !ch.is_whitespace() || *ch == '\n' {
                        if *ch == '\n' {
                            while self.chars.peek() == Some(&'\n') {
                                self.chars.next();
                                self.current += 1;
                            }

                            return Ok(Newline);
                        }

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
            None => Ok(EOF),
        }
    }

    fn consume(&mut self, char: char) -> Result<Token, LexerError> {
        self.current += 1;

        let result = match char {
            '.' => Ok(Dot),
            '+' => Ok(self.compound('=', PlusEquals, Plus)),
            '-' => Ok(self.compound('=', MinusEquals, Minus)),
            '*' => Ok(self.compound('=', StarEquals, Star)),
            '/' => Ok(self.compound('=', SlashEquals, Slash)),
            '=' => Ok(self.compound('=', EqualsEquals, Equals)),
            '~' => Ok(self.compound('=', TildeEquals, Tilde)),
            '!' => Ok(self.compound('=', BangEquals, Bang)),
            '^' => Ok(self.compound('=', CaretEquals, Caret)),
            '|' => Ok(self.compound('|', PipePipe, Pipe)),
            '&' => Ok(self.compound('=', AmpEquals, Amp)),
            '<' => Ok(self.compound('=', LessEquals, Less)),
            '>' => Ok(self.compound('=', GreaterEquals, Greater)),
            '{' => Ok(LeftBrace),
            '}' => Ok(RightBrace),
            '(' => Ok(LeftParen),
            ')' => Ok(RightParen),
            '\n' => Ok(Newline),
            'a'..='z' | 'A'..='Z' | '_' => Ok(self.identifier(self.current - 1)),
            '0'..='9' => Ok(self.number(self.current - 1)),
            _ => Err(LexerError::UnexpectedInput(char)),
        };

        result
    }

    fn compound(&mut self, expecting: char, found: Token, not_found: Token) -> Token {
        if self.chars.peek() == Some(&expecting) {
            self.chars.next();
            self.current += 1;
            found
        } else {
            not_found
        }
    }

    fn identifier<'b>(&'b mut self, starting_at: usize) -> Token {
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

    fn number(&mut self, starting_at: usize) -> Token {
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
            Float(&self.code[start_idx..=end_idx])
        } else {
            Int(&self.code[start_idx..=end_idx])
        }
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
    fn dot() {
        let mut lexer = Lexer::new("fizz.buzz");
        assert_eq!(lexer.next().unwrap(), Identifier("fizz"));
        assert_eq!(lexer.next().unwrap(), Dot);
        assert_eq!(lexer.next().unwrap(), Identifier("buzz"));
        assert_eq!(lexer.next().unwrap(), EOF);
    }

    #[test]
    fn identifier() {
        let mut lexer = Lexer::new("hello world");
        assert_eq!(lexer.next().unwrap(), Identifier("hello"));
        assert_eq!(lexer.next().unwrap(), Identifier("world"));
        assert_eq!(lexer.next().unwrap(), EOF);
    }

    #[test]
    fn ints() {
        let mut lexer = Lexer::new("123 4_56");
        assert_eq!(lexer.next().unwrap(), Int("123"));
        assert_eq!(lexer.next().unwrap(), Int("4_56"));
        assert_eq!(lexer.next().unwrap(), EOF);
    }

    #[test]
    fn floats() {
        let mut lexer = Lexer::new("12.3 4.56");
        assert_eq!(lexer.next().unwrap(), Float("12.3"));
        assert_eq!(lexer.next().unwrap(), Float("4.56"));
        assert_eq!(lexer.next().unwrap(), EOF);
    }

    #[test]
    fn specials() {
        let mut lexer = Lexer::new("+ - / * = ! ~ ^ | & < >");
        assert_eq!(lexer.next().unwrap(), Plus);
        assert_eq!(lexer.next().unwrap(), Minus);
        assert_eq!(lexer.next().unwrap(), Slash);
        assert_eq!(lexer.next().unwrap(), Star);
        assert_eq!(lexer.next().unwrap(), Equals);
        assert_eq!(lexer.next().unwrap(), Bang);
        assert_eq!(lexer.next().unwrap(), Tilde);
        assert_eq!(lexer.next().unwrap(), Caret);
        assert_eq!(lexer.next().unwrap(), Pipe);
        assert_eq!(lexer.next().unwrap(), Amp);
        assert_eq!(lexer.next().unwrap(), Less);
        assert_eq!(lexer.next().unwrap(), Greater);
        assert_eq!(lexer.next().unwrap(), EOF);
    }

    #[test]
    fn double_specials() {
        let mut lexer = Lexer::new("+= -= *= /= == != ~= ^= ||  &= <= >=");
        assert_eq!(lexer.next().unwrap(), PlusEquals);
        assert_eq!(lexer.next().unwrap(), MinusEquals);
        assert_eq!(lexer.next().unwrap(), StarEquals);
        assert_eq!(lexer.next().unwrap(), SlashEquals);
        assert_eq!(lexer.next().unwrap(), EqualsEquals);
        assert_eq!(lexer.next().unwrap(), BangEquals);
        assert_eq!(lexer.next().unwrap(), TildeEquals);
        assert_eq!(lexer.next().unwrap(), CaretEquals);
        assert_eq!(lexer.next().unwrap(), PipePipe);
        assert_eq!(lexer.next().unwrap(), AmpEquals);
        assert_eq!(lexer.next().unwrap(), LessEquals);
        assert_eq!(lexer.next().unwrap(), GreaterEquals);
        assert_eq!(lexer.next().unwrap(), EOF);
    }

    #[test]
    fn newlines() {
        let mut lexer = Lexer::new("\n");
        assert_eq!(lexer.next().unwrap(), Newline);
        assert_eq!(lexer.next().unwrap(), EOF);

        // Collapses multiple newlines into 1
        let mut lexer = Lexer::new("\n\n\n");
        assert_eq!(lexer.next().unwrap(), Newline);
        assert_eq!(lexer.next().unwrap(), EOF);
    }
}
