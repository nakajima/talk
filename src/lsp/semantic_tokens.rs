use async_lsp::lsp_types::{Position, Range, SemanticToken, SemanticTokenType};

use crate::highlighter::{self, HighlightToken, Higlighter};

pub const TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::COMMENT,
    SemanticTokenType::DECORATOR,
    SemanticTokenType::ENUM_MEMBER,
    SemanticTokenType::ENUM,
    SemanticTokenType::FUNCTION,
    SemanticTokenType::INTERFACE,
    SemanticTokenType::KEYWORD,
    SemanticTokenType::METHOD,
    SemanticTokenType::MODIFIER,
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
    fn encode(&self) -> Option<SemanticTokenType> {
        let kind = match self {
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
            highlighter::Kind::DECORATOR => SemanticTokenType::DECORATOR,
        };

        Some(kind)
    }
}

struct SemanticTokenCollector<'a> {
    tokens: Vec<HighlightToken>,
    source: &'a str,
}

pub fn collect(source: String) -> Vec<SemanticToken> {
    let tokens = collect_highlight_tokens(&source);
    let collector = SemanticTokenCollector::new(&source, tokens);

    collector.encode_tokens()
}

fn collect_highlight_tokens(source: &str) -> Vec<HighlightToken> {
    let mut highlighter = Higlighter::new(source);
    let mut tokens = highlighter.highlight();
    tokens.sort_by(|a, b| a.start.cmp(&b.start));
    tokens
}

impl<'a> SemanticTokenCollector<'a> {
    fn new(source: &'a str, tokens: Vec<HighlightToken>) -> Self {
        Self { tokens, source }
    }

    fn line_col_for(&self, position: u32) -> Option<Position> {
        let position = position as usize;
        let before = self.source.get(..position)?;
        let line = before.matches('\n').count();
        let line_start = before.rfind('\n').map(|i| i + 1).unwrap_or(0);
        let column = self
            .source
            .get(line_start..position)?
            .encode_utf16()
            .count();

        Some(Position::new(line as u32, column as u32))
    }

    fn get_range_for(&self, start: u32, end: u32) -> Option<(Range, u32)> {
        if start > end {
            return None;
        }

        let start_pos = self.line_col_for(start)?;
        let end_pos = self.line_col_for(end)?;
        let slice = self.source.get(start as usize..end as usize)?;
        let length = slice.encode_utf16().count() as u32;
        Some((Range::new(start_pos, end_pos), length))
    }

    fn encode_tokens(self) -> Vec<SemanticToken> {
        let mut tokens = self.tokens.clone();
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
                .position(|tt| Some(tt.clone()) == token_type)
                .unwrap_or(0) as u32;

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

    fn tokens_for(code: &'static str) -> Vec<SemanticToken> {
        let tokens = super::collect_highlight_tokens(code);
        let semantic_tokens = SemanticTokenCollector::new(code, tokens);
        semantic_tokens.encode_tokens()
    }

    fn pos(token_type: SemanticTokenType) -> u32 {
        TOKEN_TYPES.iter().position(|t| *t == token_type).unwrap() as u32
    }

    #[test]
    fn gets_int_tokens() {
        assert!(tokens_for("123\n1.23").contains(&SemanticToken {
            delta_line: 0,
            delta_start: 0,
            length: 3,
            token_type: pos(SemanticTokenType::NUMBER),
            token_modifiers_bitset: 0
        }));
        assert!(tokens_for("123\n1.23").contains(&SemanticToken {
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
                    token_type: pos(SemanticTokenType::NUMBER),
                    token_modifiers_bitset: 0
                },
                SemanticToken {
                    delta_line: 1,
                    delta_start: 2,
                    length: 5,
                    token_type: pos(SemanticTokenType::NUMBER),
                    token_modifiers_bitset: 0
                },
                SemanticToken {
                    delta_line: 2,
                    delta_start: 0,
                    length: 4,
                    token_type: pos(SemanticTokenType::NUMBER),
                    token_modifiers_bitset: 0
                },
            ]
            .iter()
            .all(|e| tokens_for("true\n  false\n\ntrue").contains(e))
        );
    }

    #[test]
    fn gets_string() {
        let tokens = tokens_for("false\n\"foo\"\ntrue");
        assert!(
            [
                SemanticToken {
                    delta_line: 0,
                    delta_start: 0,
                    length: 5,
                    token_type: pos(SemanticTokenType::NUMBER),
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
                    length: 4,
                    token_type: pos(SemanticTokenType::NUMBER),
                    token_modifiers_bitset: 0
                },
            ]
            .iter()
            .all(|e| tokens.contains(e))
        );
    }
}
