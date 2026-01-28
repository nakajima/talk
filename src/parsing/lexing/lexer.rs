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

            let comment = self.make(LineComment)?;
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
        // Note: ' has already been consumed, self.started points after it
        // We want the span to start after the ' prefix
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

        self.make(TokenKind::EffectName)
    }

    fn string(&mut self) -> Result<Token, LexerError> {
        // opening quote was already eaten by `next()`
        // We keep self.started pointing at the opening quote position
        // The span will include the quotes so the parser can strip them

        loop {
            // pull the next physical character
            let ch = self.advance().ok_or(LexerError::UnexpectedEOF)?;

            match ch {
                '"' => break,
                '\\' => {
                    // skip past escape sequence
                    let esc = self.advance().ok_or(LexerError::UnexpectedEOF)?;
                    match esc {
                        'n' | 't' | 'r' | '"' | '\\' => {}

                        // Unicode escape: \u{1F600}
                        'u' => {
                            self.expect_char('{')?;
                            let _digits = self.take_hex_digits(1..=6)?;
                            self.expect_char('}')?;
                        }

                        '\n' => {
                            self.line += 1;
                            self.col = 0;
                        }

                        other => return Err(LexerError::InvalidEscape(other)),
                    }
                }
                '\n' => {
                    self.line += 1;
                    self.col = 0;
                }
                _ => {}
            }
        }

        // Span includes the quotes: "hello" -> start points at ", end points after "
        self.make(TokenKind::StringLiteral)
    }

    fn identifier(&mut self, _starting_at: u32) -> TokenKind {
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        // Keyword handling - use the source slice for keyword matching
        let string = &self.code[(self.started as usize)..(self.current as usize)];
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

        // Span excludes the @ prefix - start from current position
        self.started = self.current;

        // It's an attribute
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        self.make(TokenKind::Attribute)
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

        // Span excludes the $ prefix - start from current position
        self.started = self.current;

        // It's a bound var
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        self.make(TokenKind::BoundVar)
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

        // Span excludes the % prefix - start from current position
        self.started = self.current;

        // It's a register
        while let Some(ch) = self.peek() {
            if ch.is_numeric() || ch == '?' {
                self.advance();
            } else {
                break;
            }
        }

        self.make(TokenKind::IRRegister)
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

    fn number(&mut self, _starting_at: u32) -> TokenKind {
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
            Float
        } else {
            Int
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

    /// Helper to check both token kind and lexeme
    fn assert_token(source: &str, token: &Token, expected_kind: TokenKind, expected_lexeme: &str) {
        assert_eq!(token.kind, expected_kind);
        assert_eq!(token.lexeme(source), expected_lexeme);
    }

    #[test]
    fn braces() {
        let mut lexer = Lexer::new("{}");
        assert_eq!(lexer.next().unwrap().kind, LeftBrace);
        assert_eq!(lexer.next().unwrap().kind, RightBrace);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn arrow() {
        let source = "-> Int";
        let mut lexer = Lexer::new(source);
        assert_eq!(lexer.next().unwrap().kind, Arrow);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "Int");
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
        let source = "fizz.buzz";
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "fizz");
        assert_eq!(lexer.next().unwrap().kind, Dot);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "buzz");
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn dot_dot() {
        let source = "..R";
        let mut lexer = Lexer::new(source);
        assert_eq!(lexer.next().unwrap().kind, DotDot);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "R");
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn dot_dot_dot() {
        let source = "...obj";
        let mut lexer = Lexer::new(source);
        assert_eq!(lexer.next().unwrap().kind, DotDotDot);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "obj");
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn attribute() {
        let source = "@sup @ sup";
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Attribute, "sup"); // span excludes @
        assert_eq!(lexer.next().unwrap().kind, At);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "sup");
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn identifier() {
        let source = "hello world";
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "hello");
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "world");
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn ints() {
        let source = "123 4_56";
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Int, "123");
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Int, "4_56");
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn floats() {
        let source = "12.3 4.56";
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Float, "12.3");
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Float, "4.56");
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
        let source = "- \"hello world\" + ";
        let mut lexer = Lexer::new(source);
        assert_eq!(lexer.next().unwrap().kind, Minus);
        let tok = lexer.next().unwrap();
        assert_eq!(tok.kind, StringLiteral);
        // String literal span includes quotes
        assert_eq!(tok.lexeme(source), "\"hello world\"");
        assert_eq!(lexer.next().unwrap().kind, Plus);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn strings_with_emoji() {
        let source = "- \"😎😎 hello 🗿\" + ";
        let mut lexer = Lexer::new(source);
        assert_eq!(lexer.next().unwrap().kind, Minus);
        let tok = lexer.next().unwrap();
        assert_eq!(tok.kind, StringLiteral);
        assert_eq!(tok.lexeme(source), "\"😎😎 hello 🗿\"");
        assert_eq!(lexer.next().unwrap().kind, Plus);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn strings_with_escapes() {
        let source = r#""\thello\nworld""#;
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_eq!(tok.kind, StringLiteral);
        // Raw lexeme still has escape sequences
        assert_eq!(tok.lexeme(source), r#""\thello\nworld""#);
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn strings_with_unicode_escape() {
        // 😀 = U+1F600
        let source = r#""smile: \u{1F600}""#;
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_eq!(tok.kind, StringLiteral);
        // Raw lexeme still has escape sequence
        assert_eq!(tok.lexeme(source), r#""smile: \u{1F600}""#);
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
        let source = "_ _sup";
        let mut lexer = Lexer::new(source);
        assert_eq!(lexer.next().unwrap().kind, Underscore);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "_sup");
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
        let source = "%? %1 %123 % 1";
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, IRRegister, "?"); // span excludes %
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, IRRegister, "1");
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, IRRegister, "123");
        assert_eq!(lexer.next().unwrap().kind, Percent);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Int, "1");
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn bound_var() {
        let source = "$1 $2 $sup $ sup";
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, BoundVar, "1"); // span excludes $
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, BoundVar, "2");
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, BoundVar, "sup");
        assert_eq!(lexer.next().unwrap().kind, Dollar);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Identifier, "sup");
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }

    #[test]
    fn effect() {
        let source = "123 'sup";
        let mut lexer = Lexer::new(source);
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, Int, "123");
        let tok = lexer.next().unwrap();
        assert_token(source, &tok, EffectName, "sup"); // span excludes '
        assert_eq!(lexer.next().unwrap().kind, EOF);
    }
}
