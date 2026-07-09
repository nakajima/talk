pub mod keywords;
pub mod lexer;
pub mod token;
pub mod token_kind;

use lexer::LexerError;

/// Process escape sequences in a string literal.
/// The input should NOT include surrounding quotes.
///
/// Enforces the same validity rules as the lexer: unknown escapes and
/// malformed or out-of-range `\u{...}` sequences are errors, never
/// silently dropped or passed through.
pub fn unescape(raw: &str) -> Result<String, LexerError> {
    let mut result = String::with_capacity(raw.len());
    let mut chars = raw.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => result.push('\n'),
                Some('t') => result.push('\t'),
                Some('r') => result.push('\r'),
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('\'') => result.push('\''),
                Some('u') => {
                    // Unicode escape: \u{1F600}
                    if chars.next() != Some('{') {
                        return Err(LexerError::InvalidUnicodeEscape);
                    }
                    let mut hex = String::new();
                    let mut closed = false;
                    for ch in chars.by_ref() {
                        if ch == '}' {
                            closed = true;
                            break;
                        }
                        hex.push(ch);
                    }
                    if !closed || hex.is_empty() || hex.len() > 6 {
                        return Err(LexerError::InvalidUnicodeEscape);
                    }
                    let ch = u32::from_str_radix(&hex, 16)
                        .ok()
                        .and_then(char::from_u32)
                        .ok_or(LexerError::InvalidUnicodeEscape)?;
                    result.push(ch);
                }
                Some('\n') => {
                    // Line continuation - skip the newline
                }
                Some(other) => return Err(LexerError::InvalidEscape(other)),
                None => return Err(LexerError::UnexpectedEOF),
            }
        } else {
            result.push(c);
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unescape_basic() {
        assert_eq!(unescape("hello").unwrap(), "hello");
        assert_eq!(unescape(r"hello\nworld").unwrap(), "hello\nworld");
        assert_eq!(unescape(r"hello\tworld").unwrap(), "hello\tworld");
        assert_eq!(unescape(r"hello\\world").unwrap(), "hello\\world");
        assert_eq!(unescape(r#"hello\"world"#).unwrap(), "hello\"world");
    }

    #[test]
    fn test_unescape_unicode() {
        // 😀 = U+1F600
        assert_eq!(unescape(r"smile: \u{1F600}").unwrap(), "smile: 😀");
    }

    #[test]
    fn test_unescape_rejects_invalid_unicode() {
        assert_eq!(
            unescape(r"\u{110000}"),
            Err(LexerError::InvalidUnicodeEscape)
        );
        assert_eq!(unescape(r"\u{D800}"), Err(LexerError::InvalidUnicodeEscape));
        assert_eq!(unescape(r"\u{"), Err(LexerError::InvalidUnicodeEscape));
        assert_eq!(unescape(r"\u{}"), Err(LexerError::InvalidUnicodeEscape));
        assert_eq!(
            unescape(r"\u{0000041}"),
            Err(LexerError::InvalidUnicodeEscape)
        );
        assert_eq!(unescape(r"\uXX"), Err(LexerError::InvalidUnicodeEscape));
    }

    #[test]
    fn test_unescape_rejects_unknown_escape() {
        assert_eq!(unescape(r"\q"), Err(LexerError::InvalidEscape('q')));
        assert_eq!(unescape("\\"), Err(LexerError::UnexpectedEOF));
    }
}
