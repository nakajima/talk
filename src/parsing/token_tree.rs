//! Balanced token trees (ADR 0043): the capture primitive the future
//! macro system receives its input through. A tree is a judgment-free
//! view of the token stream — newlines stay in place (the parser, not
//! the capture, decides where they matter), comments never appear (the
//! preserving lexer accumulates them on a side channel, outside the
//! stream), and groups keep their actual delimiter tokens so both
//! spans stay observable. Capture is strict: unbalanced input is an
//! error, never a best-effort tree.

use crate::lexer::Lexer;
use crate::token::Token;
use crate::token_kind::TokenKind;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Delimiter {
    Paren,
    Bracket,
    Brace,
}

impl Delimiter {
    pub fn open_text(self) -> &'static str {
        match self {
            Self::Paren => "(",
            Self::Bracket => "[",
            Self::Brace => "{",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenTree {
    Token(Token),
    Group(Group),
}

/// A delimited group: its actual open/close tokens (exact spans) plus
/// the interior. The delimiter tokens are not repeated in `children`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Group {
    pub delimiter: Delimiter,
    pub open: Token,
    pub close: Token,
    pub children: Vec<TokenTree>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenTreeError {
    /// The source failed to lex.
    Lex { message: String },
    /// A closer with no group open.
    UnexpectedCloser { close: Token },
    /// A closer that does not match the innermost open group.
    MismatchedCloser { open: Token, close: Token },
    /// The innermost group was still open at end of input.
    Unclosed { open: Token },
    /// A non-source sentinel token reached capture.
    GeneratedToken { token: Token },
}

impl TokenTreeError {
    pub fn code(&self) -> &'static str {
        match self {
            Self::Lex { .. } => "tokentree.lex",
            Self::UnexpectedCloser { .. } => "tokentree.unexpected-closer",
            Self::MismatchedCloser { .. } => "tokentree.mismatched-closer",
            Self::Unclosed { .. } => "tokentree.unclosed",
            Self::GeneratedToken { .. } => "tokentree.generated-token",
        }
    }
}

impl std::fmt::Display for TokenTreeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Lex { message } => write!(f, "{message}"),
            Self::UnexpectedCloser { close } => {
                write!(
                    f,
                    "closer at {}..{} has no open group",
                    close.start, close.end
                )
            }
            Self::MismatchedCloser { open, close } => write!(
                f,
                "closer at {}..{} does not match the group opened at {}..{}",
                close.start, close.end, open.start, open.end
            ),
            Self::Unclosed { open } => {
                write!(f, "group opened at {}..{} is never closed", open.start, open.end)
            }
            Self::GeneratedToken { token } => write!(
                f,
                "generated token at {}..{} cannot appear in captured source",
                token.start, token.end
            ),
        }
    }
}

/// Group a token slice into balanced trees. `EOF` sentinels end the
/// input; every other token lands in a tree.
pub fn group(tokens: &[Token]) -> Result<Vec<TokenTree>, TokenTreeError> {
    let mut stack: Vec<(Token, Delimiter, Vec<TokenTree>)> = Vec::new();
    let mut current: Vec<TokenTree> = Vec::new();

    for token in tokens {
        let open = |delimiter| Some(delimiter);
        let opened = match token.kind {
            TokenKind::EOF => break,
            TokenKind::Generated => {
                return Err(TokenTreeError::GeneratedToken {
                    token: token.clone(),
                });
            }
            TokenKind::LeftParen => open(Delimiter::Paren),
            TokenKind::LeftBracket => open(Delimiter::Bracket),
            TokenKind::LeftBrace => open(Delimiter::Brace),
            _ => None,
        };
        if let Some(delimiter) = opened {
            stack.push((token.clone(), delimiter, std::mem::take(&mut current)));
            continue;
        }

        let closed = match token.kind {
            TokenKind::RightParen => Some(Delimiter::Paren),
            TokenKind::RightBracket => Some(Delimiter::Bracket),
            TokenKind::RightBrace => Some(Delimiter::Brace),
            _ => None,
        };
        if let Some(delimiter) = closed {
            let Some((open, expected, parent)) = stack.pop() else {
                return Err(TokenTreeError::UnexpectedCloser {
                    close: token.clone(),
                });
            };
            if expected != delimiter {
                return Err(TokenTreeError::MismatchedCloser {
                    open,
                    close: token.clone(),
                });
            }
            let children = std::mem::replace(&mut current, parent);
            current.push(TokenTree::Group(Group {
                delimiter,
                open,
                close: token.clone(),
                children,
            }));
            continue;
        }

        current.push(TokenTree::Token(token.clone()));
    }

    if let Some((open, _, _)) = stack.pop() {
        return Err(TokenTreeError::Unclosed { open });
    }
    Ok(current)
}

/// Lex `source` (comments dropped — the default trivia policy) and
/// group the whole stream.
pub fn capture(source: &str) -> Result<Vec<TokenTree>, TokenTreeError> {
    let mut lexer = Lexer::new(source);
    let mut tokens = Vec::new();
    loop {
        match lexer.next() {
            Ok(token) if token.kind == TokenKind::EOF => break,
            Ok(token) => tokens.push(token),
            Err(error) => {
                return Err(TokenTreeError::Lex {
                    message: error.message(),
                });
            }
        }
    }
    group(&tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(trees: &[TokenTree]) -> Vec<String> {
        trees
            .iter()
            .map(|tree| match tree {
                TokenTree::Token(token) => format!("{:?}", token.kind),
                TokenTree::Group(group) => {
                    format!("Group{}[{}]", group.delimiter.open_text(), group.children.len())
                }
            })
            .collect()
    }

    #[test]
    fn groups_keep_their_delimiter_tokens() {
        let trees = capture("(a)").expect("balanced");
        let [TokenTree::Group(group)] = trees.as_slice() else {
            panic!("expected one group, got {:?}", kinds(&trees));
        };
        assert_eq!(group.delimiter, Delimiter::Paren);
        assert_eq!((group.open.start, group.open.end), (0, 1));
        assert_eq!((group.close.start, group.close.end), (2, 3));
        assert_eq!(group.children.len(), 1);
    }

    #[test]
    fn newlines_stay_inside_groups() {
        let trees = capture("foo(\n\ta,\n\tb\n)").expect("balanced");
        let Some(TokenTree::Group(group)) = trees.last() else {
            panic!("expected trailing group, got {:?}", kinds(&trees));
        };
        assert!(
            group
                .children
                .iter()
                .any(|tree| matches!(tree, TokenTree::Token(token) if token.kind == TokenKind::Newline)),
            "newline tokens must survive capture: {:?}",
            kinds(&group.children)
        );
    }

    #[test]
    fn imbalance_is_strict_with_both_spans() {
        let unexpected = capture(")").expect_err("bare closer");
        assert_eq!(unexpected.code(), "tokentree.unexpected-closer");

        let mismatched = capture("(]").expect_err("mismatched closer");
        let TokenTreeError::MismatchedCloser { open, close } = &mismatched else {
            panic!("expected mismatch, got {mismatched:?}");
        };
        assert_eq!((open.start, close.start), (0, 1));

        let unclosed = capture("([").expect_err("unclosed");
        let TokenTreeError::Unclosed { open } = &unclosed else {
            panic!("expected unclosed, got {unclosed:?}");
        };
        // The innermost unclosed group is reported.
        assert_eq!(open.start, 1);
    }
}
