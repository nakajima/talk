use crate::highlighter::{self, Higlighter};
use async_lsp::lsp_types::{Position, Range, SemanticToken, SemanticTokenType};

pub const TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::COMMENT,
    SemanticTokenType::ENUM_MEMBER,
    SemanticTokenType::ENUM,
    SemanticTokenType::FUNCTION,
    SemanticTokenType::INTERFACE,
    SemanticTokenType::KEYWORD,
    SemanticTokenType::METHOD,
    SemanticTokenType::NUMBER,
    SemanticTokenType::OPERATOR,
    SemanticTokenType::PARAMETER,
    SemanticTokenType::PROPERTY,
    SemanticTokenType::STRING,
    SemanticTokenType::STRUCT,
    SemanticTokenType::TYPE_PARAMETER,
    SemanticTokenType::TYPE,
    SemanticTokenType::VARIABLE,
];

impl highlighter::Kind {
    fn encode(&self) -> SemanticTokenType {
        match self {
            highlighter::Kind::NAMESPACE => SemanticTokenType::NAMESPACE,
            highlighter::Kind::TYPE => SemanticTokenType::TYPE,
            highlighter::Kind::CLASS => SemanticTokenType::CLASS,
            highlighter::Kind::ENUM => SemanticTokenType::ENUM,
            highlighter::Kind::INTERFACE => SemanticTokenType::INTERFACE,
            highlighter::Kind::STRUCT => SemanticTokenType::STRUCT,
            highlighter::Kind::TYPE_PARAMETER => SemanticTokenType::TYPE_PARAMETER,
            highlighter::Kind::PARAMETER => SemanticTokenType::PARAMETER,
            highlighter::Kind::VARIABLE => SemanticTokenType::VARIABLE,
            highlighter::Kind::PROPERTY => SemanticTokenType::PROPERTY,
            highlighter::Kind::ENUM_MEMBER => SemanticTokenType::ENUM_MEMBER,
            highlighter::Kind::EVENT => SemanticTokenType::EVENT,
            highlighter::Kind::FUNCTION => SemanticTokenType::FUNCTION,
            highlighter::Kind::METHOD => SemanticTokenType::METHOD,
            highlighter::Kind::MACRO => SemanticTokenType::MACRO,
            highlighter::Kind::KEYWORD => SemanticTokenType::KEYWORD,
            highlighter::Kind::MODIFIER => SemanticTokenType::MODIFIER,
            highlighter::Kind::COMMENT => SemanticTokenType::COMMENT,
            highlighter::Kind::STRING => SemanticTokenType::STRING,
            highlighter::Kind::NUMBER => SemanticTokenType::NUMBER,
            highlighter::Kind::REGEXP => SemanticTokenType::REGEXP,
            highlighter::Kind::OPERATOR => SemanticTokenType::OPERATOR,
        }
    }
}

struct SemanticTokenCollector<'a> {
    highlighter: Higlighter<'a>,
    source: &'a str,
}

pub fn collect(source: String) -> Vec<SemanticToken> {
    let collector = SemanticTokenCollector::new(&source);

    collector.encode_tokens()
}

impl<'a> SemanticTokenCollector<'a> {
    fn new(source: &'a str) -> Self {
        let highlighter = Higlighter::new(source);
        Self {
            highlighter,
            source,
        }
    }

    fn line_col_for(&self, position: u32) -> Option<Position> {
        if position as usize > self.source.len() {
            return None;
        }

        let before = &self.source[..position as usize];
        let line = before.matches('\n').count(); // Remove the +1 here
        let column = before
            .rfind('\n')
            .map(|i| &before[i + 1..])
            .unwrap_or(before)
            .chars()
            .count(); // Also remove the +1 here

        Some(Position::new(line as u32, column as u32))
    }

    fn get_range_for(&self, start: u32, end: u32) -> Option<(Range, u32)> {
        if let Some(start_pos) = self.line_col_for(start)
            && let Some(end_pos) = self.line_col_for(end)
        {
            Some((Range::new(start_pos, end_pos), end.saturating_sub(start)))
        } else {
            Some((
                Range::new(Position::new(0, 0), Position::new(0, 0)),
                end.saturating_sub(start),
            ))
        }
    }

    // fn range_for(&self, expr_id: &ExprID) -> Option<(Range, u32)> {
    //     let meta = self.source_file.meta.get(expr_id)?;
    //     let range = meta.source_range();

    //     if let Some(start) = self.line_col_for(range.start)
    //         && let Some(end) = self.line_col_for(range.end)
    //     {
    //         Some((
    //             Range::new(start, end),
    //             meta.end.end.saturating_sub(meta.start.start),
    //         ))
    //     } else {
    //         Some((
    //             Range::new(Position::new(0, 0), Position::new(0, 0)),
    //             meta.end.end.saturating_sub(meta.start.start),
    //         ))
    //     }
    // }
    fn encode_tokens(mut self) -> Vec<SemanticToken> {
        let mut tokens = self.highlighter.highlight();

        tokens.sort_by(|a, b| a.start.cmp(&b.start));

        let mut encoded_tokens = Vec::new();
        let mut last_pos = Position::new(0, 0);

        for tok in tokens {
            let Some((range, length)) = self.get_range_for(tok.start, tok.end) else {
                continue;
            };

            let token_type = tok.kind.encode();

            if range.end.character < range.start.character && range.end.line <= range.start.line {
                tracing::error!("Warning: Invalid range detected: {range:?}");
                continue;
            }

            let delta_line = range.start.line - last_pos.line;
            let delta_start = if delta_line == 0 {
                range.start.character - last_pos.character
            } else {
                range.start.character
            };

            let token_type_index = TOKEN_TYPES
                .iter()
                .position(|tt| tt == &token_type)
                .unwrap_or(0) as u32;

            tracing::error!("{range:?} {length:?} {token_type:?}");

            encoded_tokens.push(SemanticToken {
                delta_line,
                delta_start,
                length,
                token_type: token_type_index,
                token_modifiers_bitset: 0,
            });

            last_pos = range.start;
        }

        encoded_tokens
    }
}

#[cfg(test)]
mod tests {
    use async_lsp::lsp_types::{SemanticToken, SemanticTokenType};

    use crate::lsp::semantic_tokens::{SemanticTokenCollector, TOKEN_TYPES};

    fn parsed_tokens_for(code: &'static str) -> Vec<SemanticToken> {
        let semantic_tokens = SemanticTokenCollector::new(code);
        semantic_tokens.encode_tokens()
    }

    fn lexed_tokens_for(code: &'static str) -> Vec<SemanticToken> {
        let semantic_tokens = SemanticTokenCollector::new(code);
        semantic_tokens.encode_tokens()
    }

    fn pos(token_type: SemanticTokenType) -> u32 {
        TOKEN_TYPES.iter().position(|t| *t == token_type).unwrap() as u32
    }

    #[test]
    fn gets_int_tokens() {
        assert!(parsed_tokens_for("123\n1.23").contains(&SemanticToken {
            delta_line: 0,
            delta_start: 0,
            length: 3,
            token_type: pos(SemanticTokenType::NUMBER),
            token_modifiers_bitset: 0
        }));
        assert!(parsed_tokens_for("123\n1.23").contains(&SemanticToken {
            delta_line: 1,
            delta_start: 0,
            length: 4,
            token_type: pos(SemanticTokenType::NUMBER),
            token_modifiers_bitset: 0
        }));
    }

    #[test]
    fn gets_bool() {
        assert!(
            [
                SemanticToken {
                    delta_line: 0,
                    delta_start: 0,
                    length: 4,
                    token_type: pos(SemanticTokenType::KEYWORD),
                    token_modifiers_bitset: 0
                },
                SemanticToken {
                    delta_line: 1,
                    delta_start: 2,
                    length: 5,
                    token_type: pos(SemanticTokenType::KEYWORD),
                    token_modifiers_bitset: 0
                },
                SemanticToken {
                    delta_line: 2,
                    delta_start: 0,
                    length: 4,
                    token_type: pos(SemanticTokenType::KEYWORD),
                    token_modifiers_bitset: 0
                },
            ]
            .iter()
            .all(|e| parsed_tokens_for("true\n  false\n\ntrue").contains(e))
        );
    }

    #[test]
    fn gets_string() {
        assert!(
            [
                SemanticToken {
                    delta_line: 0,
                    delta_start: 0,
                    length: 4,
                    token_type: pos(SemanticTokenType::KEYWORD),
                    token_modifiers_bitset: 0
                },
                SemanticToken {
                    delta_line: 1,
                    delta_start: 0,
                    length: 5,
                    token_type: pos(SemanticTokenType::STRING),
                    token_modifiers_bitset: 0
                },
                SemanticToken {
                    delta_line: 1,
                    delta_start: 0,
                    length: 5,
                    token_type: pos(SemanticTokenType::KEYWORD),
                    token_modifiers_bitset: 0
                },
            ]
            .iter()
            .all(|e| lexed_tokens_for("true\n\"sup\"\nfalse").contains(e)),
            "{:#?}\n{:#?}",
            lexed_tokens_for("true\n\"sup\"\nfalse"),
            vec![
                SemanticToken {
                    delta_line: 0,
                    delta_start: 0,
                    length: 4,
                    token_type: pos(SemanticTokenType::KEYWORD),
                    token_modifiers_bitset: 0
                },
                SemanticToken {
                    delta_line: 1,
                    delta_start: 0,
                    length: 5,
                    token_type: pos(SemanticTokenType::STRING),
                    token_modifiers_bitset: 0
                },
                SemanticToken {
                    delta_line: 1,
                    delta_start: 1,
                    length: 5,
                    token_type: pos(SemanticTokenType::KEYWORD),
                    token_modifiers_bitset: 0
                },
            ]
        );
    }

    #[test]
    fn gets_multiline_string() {
        assert_eq!(
            lexed_tokens_for("\"sup\nhi\""),
            vec![SemanticToken {
                delta_line: 0,
                delta_start: 0,
                length: 8,
                token_type: pos(SemanticTokenType::STRING),
                token_modifiers_bitset: 0
            }]
        )
    }
}
