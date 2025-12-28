use core::str::Chars;
use std::ops::RangeInclusive;

use itertools::{Itertools, MultiPeek};

use crate::keywords;

use super::token::Token;
use super::token_kind::TokenKind::{self, *};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LexerError {
    ExpectedChar { expected: char, actual: char },
    UnexpectedInput(char),
    InvalidEscape(char),
    UnexpectedEOF,
    InvalidUnicodeEscape,
    UnterminatedString,
}

impl LexerError {
    pub fn message(&self) -> String {
        match &self {
            Self::ExpectedChar { expected, actual } => {
                format!("Expected character: {expected:?}, got: {actual:?}")
            }
            Self::UnexpectedInput(ch) => format!("Unexpected character: {ch:?}"),
            Self::UnexpectedEOF => "Unexpected end of file".to_string(),
            Self::InvalidEscape(ch) => format!("Invalid escape: {ch:?}"),
            Self::InvalidUnicodeEscape => "Invalid unicode escape".to_string(),
            Self::UnterminatedString => "Unterminated string".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Lexer<'a> {
    pub code: &'a str,
    preserve_comments: bool,
    _chars: MultiPeek<Chars<'a>>,
    current: u32,
    started: u32,
    line: u32,
    col: u32,
    pub comments: Vec<Token>,
}

impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Self {
        Self {
            code,
            preserve_comments: false,
            _chars: code.chars().multipeek(),
            current: 0,
            started: 0,
            line: 0,
            col: 0,
            comments: vec![],
        }
    }

    pub fn preserving_comments(code: &'a str) -> Self {
        Self {
            code,
            preserve_comments: true,
            _chars: code.chars().multipeek(),
            current: 0,
            started: 0,
            line: 0,
            col: 0,
            comments: vec![],
        }
    }

    fn skip_whitespace(&mut self) {
        // Skip whitespaces
        while let Some(peeked) = self.peek() {
            if peeked.is_whitespace() && peeked != '\n' {
                self.advance();
            } else {
                break;
            }
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Token, LexerError> {
        self.skip_whitespace();

        if self.preserve_comments {
            self.preserve_comments()?;
        } else {
            self.skip_comments();
        }

        self.skip_whitespace();

        self.started = self.current;

        let Some(ch) = self.advance() else {
            return self.make(TokenKind::EOF);
        };

        match ch {
            '.' => self.dot(),
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
            '&' => self.compound_many(Amp, &[('=', AmpEquals), ('&', AmpAmp)]),
            '<' => self.compound('=', LessEquals, Less),
            '>' => self.compound('=', GreaterEquals, Greater),
            '{' => self.make(LeftBrace),
            '}' => self.make(RightBrace),
            '(' => self.make(LeftParen),
            ')' => self.make(RightParen),
            '[' => self.make(LeftBracket),
            ']' => self.make(RightBracket),
            ';' => self.make(Semicolon),
            '%' => self.percent(),
            '@' => self.at(),
            '$' => self.dollar(),
            '"' => self.string(),
            '\'' => self.effect_name(),
            '\n' => self.newline(),
            '_' => {
                if let Some(next) = self.peek()
                    && (next == '_' || next.is_alphanumeric())
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
            _ => Err(LexerError::UnexpectedInput(ch)),
        }
    }

    fn peek(&mut self) -> Option<char> {
        let ch = self._chars.peek().cloned();
        self._chars.reset_peek();
        ch
    }

    fn peek_next(&mut self) -> Option<char> {
        self._chars.peek();
        let ch = self._chars.peek().cloned();
        self._chars.reset_peek();
        ch
    }

    fn newline(&mut self) -> Result<Token, LexerError> {
        while self.peek() == Some('\n') {
            self.advance();
        }

        self.make(Newline)
    }

    fn skip_comments(&mut self) {
        // Handle single line comments
        if self.peek() == Some('/') && self.peek_next() == Some('/') {
            self.advance();
            self.advance();
            while let Some(ch) = self.peek() {
                if ch == '\n' {
                    break;
                }

                self.advance();
            }
        }
    }

    fn preserve_comments(&mut self) -> Result<(), LexerError> {
        if self.peek() == Some('/') && self.peek_next() == Some('/') {
            self.started = self.current;

            while let Some(ch) = self.peek() {
                if ch == '\n' {
                    break;
                }

                self.advance();
            }

            let comment = self.make(LineComment(self.string_from(self.started, self.current)))?;
            self.comments.push(comment);
        }

        Ok(())
    }

    fn compound(
        &mut self,
        expecting: char,
        found: TokenKind,
        not_found: TokenKind,
    ) -> Result<Token, LexerError> {
        if self.peek() == Some(expecting) {
            self.advance();
            self.make(found)
        } else {
            self.make(not_found)
        }
    }

    fn compound_many(
        &mut self,
        not_found: TokenKind,
        options: &[(char, TokenKind)],
    ) -> Result<Token, LexerError> {
        for (expecting, found) in options {
            if self.peek() == Some(*expecting) {
                self.advance();
                return self.make(found.clone());
            }
        }

        self.make(not_found)
    }

    fn effect_name(&mut self) -> Result<Token, LexerError> {
        self.started = self.current;

        if !self
            .peek()
            .map(|t| t.is_alphanumeric() || t == '_')
            .unwrap_or(false)
        {
            return self.make(TokenKind::SingleQuote);
        }

        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let string = self.string_from(self.started, self.current);
        self.make(TokenKind::EffectName(string))
    }

    fn string(&mut self) -> Result<Token, LexerError> {
        // opening quote was already eaten by `next()`
        self.started = self.current;
        let mut buf = String::new();

        loop {
            // pull the next physical character
            let ch = self.advance().ok_or(LexerError::UnexpectedEOF)?;

            match ch {
                '"' => break,
                '\\' => {
                    // start of an escape
                    let esc = self.advance().ok_or(LexerError::UnexpectedEOF)?;
                    match esc {
                        'n' => buf.push('\n'),
                        't' => buf.push('\t'),
                        'r' => buf.push('\r'),
                        '"' => buf.push('"'),
                        '\\' => buf.push('\\'),

                        // Unicode escape: \u{1F600}
                        'u' => {
                            self.expect_char('{')?;
                            let digits = self.take_hex_digits(1..=6)?;
                            self.expect_char('}')?;

                            let cp = u32::from_str_radix(&digits, 16)
                                .map_err(|_| LexerError::InvalidUnicodeEscape)?;
                            buf.push(char::from_u32(cp).ok_or(LexerError::InvalidUnicodeEscape)?);
                        }

                        '\n' => {
                            self.line += 1;
                            self.col = 0;
                        }

                        other => return Err(LexerError::InvalidEscape(other)),
                    }
                }
                '\n' => buf.push('\n'),
                _ => buf.push(ch),
            }
        }

        let mut tok = self.make(TokenKind::StringLiteral(buf))?;
        tok.end -= 1; // move `end` back over the quote only
        Ok(tok)
    }

    fn identifier(&mut self, starting_at: u32) -> TokenKind {
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let string = self.string_from(starting_at, self.current);

        // Keyword handling
        keywords::handle(string)
    }

    fn at(&mut self) -> Result<Token, LexerError> {
        if !self
            .peek()
            .map(|c| c.is_alphanumeric() || c == '_')
            .unwrap_or(false)
        {
            // It's a standalone @
            return self.make(TokenKind::At);
        }

        let starting_at = self.current;

        // It's an attribute
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let string = self.string_from(starting_at, self.current);
        self.make(TokenKind::Attribute(string))
    }

    fn dollar(&mut self) -> Result<Token, LexerError> {
        if !self
            .peek()
            .map(|c| c.is_alphanumeric() || c == '_')
            .unwrap_or(false)
        {
            // It's a standalone $
            return self.make(TokenKind::Dollar);
        }

        let starting_at = self.current;

        // It's an attribute
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let string = self.string_from(starting_at, self.current);
        self.make(TokenKind::BoundVar(string))
    }

    fn percent(&mut self) -> Result<Token, LexerError> {
        if !self
            .peek()
            .map(|c| c.is_numeric() || c == '?')
            .unwrap_or(false)
        {
            // It's a standalone %
            return self.make(TokenKind::Percent);
        }

        let starting_at = self.current;

        // It's an attribute
        while let Some(ch) = self.peek() {
            if ch.is_numeric() || ch == '?' {
                self.advance();
            } else {
                break;
            }
        }

        let string = self.string_from(starting_at, self.current);
        self.make(TokenKind::IRRegister(string))
    }

    fn minus(&mut self) -> Result<Token, LexerError> {
        if self.peek() == Some('>') {
            self.advance();
            return self.make(Arrow);
        }

        if self.peek() == Some('=') {
            self.advance();
            return self.make(MinusEquals);
        }

        self.make(Minus)
    }

    fn dot(&mut self) -> Result<Token, LexerError> {
        if self.peek() == Some('.') {
            self.advance();
            if self.peek() == Some('.') {
                self.advance();
                return self.make(DotDotDot);
            }
            return self.make(DotDot);
        }
        self.make(Dot)
    }

    fn number(&mut self, starting_at: u32) -> TokenKind {
        let mut is_float = false;

        while let Some(ch) = self.peek() {
            if ch == '.' && self.peek_next().map(|f| f.is_numeric()).unwrap_or(false) && !is_float {
                is_float = true;
                self.advance();
            } else if ch.is_numeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        if is_float {
            Float(self.string_from(starting_at, self.current))
        } else {
            Int(self.string_from(starting_at, self.current))
        }
    }

    fn string_from(&self, start: u32, end: u32) -> String {
        self.code[(start as usize)..=(end as usize - 1)].to_string()
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

    pub(crate) fn advance(&mut self) -> Option<char> {
        if let Some(ch) = self._chars.next() {
            if ch == '\n' {
                self.col = 0;
                self.line += 1;
            } else {
                self.col += 1;
            }
            self.current += ch.len_utf8() as u32;
            Some(ch)
        } else {
            None
        }
    }

    /// Consumes the next character and verifies it matches `expected`.
    /// Errors if it doesn’t or if we hit EOF.
    fn expect_char(&mut self, expected: char) -> Result<(), LexerError> {
        match self.advance() {
            Some(c) if c == expected => Ok(()),
            Some(actual) => Err(LexerError::ExpectedChar { expected, actual }), // add this variant
            None => Err(LexerError::UnexpectedEOF),
        }
    }

    /// Collects 1–6 hex digits (or whatever `range` you pass) and returns them as a `String`.
    /// Fails if the digit count is outside the range or a non-hex char is encountered first.
    fn take_hex_digits(&mut self, range: RangeInclusive<usize>) -> Result<String, LexerError> {
        let mut buf = String::new();

        while let Some(ch) = self.peek() {
            if ch.is_ascii_hexdigit()
                && buf.len() < *range.end()
                && let Some(next) = self.advance()
            {
                buf.push(next);
            } else {
                break;
            }
        }

        if range.contains(&buf.len()) {
            Ok(buf)
        } else {
            Err(LexerError::InvalidUnicodeEscape) // add this variant
        }
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
    fn dot_dot() {
        let mut lexer = Lexer::new("..R");
        assert_eq!(lexer.next().unwrap().kind, DotDot);
        assert_eq!(lexer.next().unwrap().kind, Identifier("R".to_string()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn dot_dot_dot() {
        let mut lexer = Lexer::new("...obj");
        assert_eq!(lexer.next().unwrap().kind, DotDotDot);
        assert_eq!(lexer.next().unwrap().kind, Identifier("obj".to_string()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn attribute() {
        let mut lexer = Lexer::new("@sup @ sup");
        assert_eq!(lexer.next().unwrap().kind, Attribute("sup".to_string()));
        assert_eq!(lexer.next().unwrap().kind, At);
        assert_eq!(lexer.next().unwrap().kind, Identifier("sup".to_string()));
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
        let mut lexer = Lexer::new("+= -= *= /= == != ~= ^= ||  &= <= >= &&");
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
        assert_eq!(lexer.next().unwrap().kind, AmpAmp);
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
    fn strings() {
        let mut lexer = Lexer::new("- \"hello world\" + ");
        assert_eq!(lexer.next().unwrap().kind, Minus);
        assert_eq!(
            lexer.next().unwrap().kind,
            StringLiteral("hello world".to_string())
        );
        assert_eq!(lexer.next().unwrap().kind, Plus);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn strings_with_emoji() {
        let mut lexer = Lexer::new("- \"😎😎 hello 🗿\" + ");
        assert_eq!(lexer.next().unwrap().kind, Minus);
        assert_eq!(
            lexer.next().unwrap().kind,
            StringLiteral("😎😎 hello 🗿".to_string())
        );
        assert_eq!(lexer.next().unwrap().kind, Plus);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn strings_with_escapes() {
        let mut lexer = Lexer::new(r#""\thello\nworld""#);
        assert_eq!(
            lexer.next().unwrap().kind,
            StringLiteral("\thello\nworld".to_string())
        );
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn strings_with_unicode_escape() {
        // 😀 = U+1F600
        let mut lexer = Lexer::new(r#""smile: \u{1F600}""#);

        assert_eq!(
            lexer.next().unwrap().kind,
            StringLiteral("smile: 😀".to_string())
        );
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

    #[test]
    fn handles_semicolons() {
        let mut lexer = Lexer::new(";");
        assert_eq!(lexer.next().unwrap().kind, Semicolon);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn handles_typealias() {
        let mut lexer = Lexer::new("typealias");
        assert_eq!(lexer.next().unwrap().kind, Typealias);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn skips_line_comments_by_default() {
        let mut lexer = Lexer::new("_\n// Hello world\n_");
        assert_eq!(lexer.next().unwrap().kind, Underscore);
        assert_eq!(lexer.next().unwrap().kind, Newline);
        assert_eq!(lexer.next().unwrap().kind, Newline);
        assert_eq!(lexer.next().unwrap().kind, Underscore);
        assert_eq!(lexer.next().unwrap().kind, EOF);
        assert!(lexer.comments.is_empty());
    }

    #[test]
    fn preserves_line_comments_when_specified() {
        let mut lexer = Lexer::preserving_comments("_\n// Hello world\n_");
        assert_eq!(lexer.next().unwrap().kind, Underscore);
        assert_eq!(lexer.next().unwrap().kind, Newline);
        assert_eq!(lexer.next().unwrap().kind, Newline);
        assert_eq!(lexer.next().unwrap().kind, Underscore);
        assert_eq!(lexer.next().unwrap().kind, EOF);
        assert_eq!(lexer.comments.len(), 1);
    }

    #[test]
    fn ir_register() {
        let mut lexer = Lexer::new("%? %1 %123 % 1");
        assert_eq!(lexer.next().unwrap().kind, IRRegister("?".into()));
        assert_eq!(lexer.next().unwrap().kind, IRRegister("1".into()));
        assert_eq!(lexer.next().unwrap().kind, IRRegister("123".into()));
        assert_eq!(lexer.next().unwrap().kind, Percent);
        assert_eq!(lexer.next().unwrap().kind, Int("1".into()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn bound_var() {
        let mut lexer = Lexer::new("$1 $2 $sup $ sup");
        assert_eq!(lexer.next().unwrap().kind, BoundVar("1".into()));
        assert_eq!(lexer.next().unwrap().kind, BoundVar("2".into()));
        assert_eq!(lexer.next().unwrap().kind, BoundVar("sup".into()));
        assert_eq!(lexer.next().unwrap().kind, Dollar);
        assert_eq!(lexer.next().unwrap().kind, Identifier("sup".into()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn effect() {
        let mut lexer = Lexer::new("123 'sup");
        assert_eq!(lexer.next().unwrap().kind, Int("123".into()));
        assert_eq!(lexer.next().unwrap().kind, EffectName("sup".into()));
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }
}
