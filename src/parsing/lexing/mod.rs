pub mod keywords;
pub mod lexer;
pub mod token;
pub mod token_kind;

/// Process escape sequences in a string literal.
/// The input should include surrounding quotes.
pub fn unescape(raw: &str) -> String {
    // Strip surrounding quotes
    let inner = if raw.len() >= 2 {
        &raw[1..raw.len() - 1]
    } else {
        raw
    };

    let mut result = String::with_capacity(inner.len());
    let mut chars = inner.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => result.push('\n'),
                Some('t') => result.push('\t'),
                Some('r') => result.push('\r'),
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('u') => {
                    // Unicode escape: \u{1F600}
                    if chars.next() == Some('{') {
                        let mut hex = String::new();
                        while let Some(&ch) = chars.peek() {
                            if ch == '}' {
                                chars.next();
                                break;
                            }
                            hex.push(chars.next().unwrap());
                        }
                        if let Ok(cp) = u32::from_str_radix(&hex, 16) {
                            if let Some(ch) = char::from_u32(cp) {
                                result.push(ch);
                            }
                        }
                    }
                }
                Some('\n') => {
                    // Line continuation - skip the newline
                }
                Some(other) => {
                    result.push('\\');
                    result.push(other);
                }
                None => result.push('\\'),
            }
        } else {
            result.push(c);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unescape_basic() {
        assert_eq!(unescape(r#""hello""#), "hello");
        assert_eq!(unescape(r#""hello\nworld""#), "hello\nworld");
        assert_eq!(unescape(r#""hello\tworld""#), "hello\tworld");
        assert_eq!(unescape(r#""hello\\world""#), "hello\\world");
        assert_eq!(unescape(r#""hello\"world""#), "hello\"world");
    }

    #[test]
    fn test_unescape_unicode() {
        // 😀 = U+1F600
        assert_eq!(unescape(r#""smile: \u{1F600}""#), "smile: 😀");
    }
}
