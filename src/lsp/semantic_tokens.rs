use crate::{Parsed, expr::Expr, parser::ExprID, source_file::SourceFile};
use async_lsp::lsp_types::{Position, Range, SemanticToken, SemanticTokenType};

use super::server::TOKEN_TYPES;

struct SemanticTokenCollector<'a> {
    source_file: &'a SourceFile<Parsed>,
    source: &'a str,
    tokens: Vec<(Range, SemanticTokenType)>,
}

pub fn collect(source_file: &SourceFile<Parsed>, source: &str) -> Vec<SemanticToken> {
    let mut collector = SemanticTokenCollector::new(source_file, source);
    collector.collect_tokens();
    collector.encode_tokens()
}

impl<'a> SemanticTokenCollector<'a> {
    fn new(source_file: &'a SourceFile<Parsed>, source: &'a str) -> Self {
        Self {
            source_file,
            source,
            tokens: vec![],
        }
    }

    fn line_col_for(&self, position: usize) -> Option<Position> {
        if position > self.source.len() {
            return None;
        }

        let before = &self.source[..position];
        let line = before.matches('\n').count(); // Remove the +1 here
        let column = before
            .rfind('\n')
            .map(|i| &before[i + 1..])
            .unwrap_or(before)
            .chars()
            .count(); // Also remove the +1 here

        Some(Position::new(line as u32, column as u32))
    }

    fn range_for(&self, expr_id: &ExprID) -> Range {
        let range = self.source_file.meta[*expr_id as usize].source_range();
        Range::new(
            self.line_col_for(range.start)
                .expect("did not get position"),
            self.line_col_for(range.end).expect("did not get position"),
        )
    }

    fn tokens_from_exprs(&self, exprs: &[ExprID]) -> Vec<(Range, SemanticTokenType)> {
        exprs
            .iter()
            .flat_map(|e| self.tokens_from_expr(e))
            .collect()
    }

    fn tokens_from_expr(&self, expr: &ExprID) -> Vec<(Range, SemanticTokenType)> {
        let mut result = vec![];

        match self.source_file.get(expr).unwrap() {
            Expr::LiteralArray(items) => result.extend(self.tokens_from_exprs(items)),
            Expr::LiteralInt(_) | Expr::LiteralFloat(_) => {
                result.push((self.range_for(expr), SemanticTokenType::NUMBER))
            }
            Expr::LiteralTrue | Expr::LiteralFalse => {
                result.push((self.range_for(expr), SemanticTokenType::KEYWORD))
            }
            Expr::Unary(_token_kind, rhs) => result.extend(self.tokens_from_expr(rhs)),
            Expr::Binary(lhs, _token_kind, rhs) => {
                result.extend(self.tokens_from_exprs(&[*lhs, *rhs]))
            }
            Expr::Tuple(items) => result.extend(self.tokens_from_exprs(items)),
            Expr::Block(items) => result.extend(self.tokens_from_exprs(items)),
            Expr::Call {
                callee,
                type_args,
                args,
            } => {
                result.extend(self.tokens_from_expr(callee));
                result.extend(self.tokens_from_exprs(type_args));
                result.extend(self.tokens_from_exprs(args));
            }
            Expr::Pattern(pattern) => match pattern {
                crate::expr::Pattern::LiteralInt(_) => {
                    result.push((self.range_for(expr), SemanticTokenType::NUMBER))
                }
                crate::expr::Pattern::LiteralFloat(_) => {
                    result.push((self.range_for(expr), SemanticTokenType::NUMBER))
                }
                crate::expr::Pattern::LiteralTrue => {
                    result.push((self.range_for(expr), SemanticTokenType::KEYWORD))
                }
                crate::expr::Pattern::LiteralFalse => {
                    result.push((self.range_for(expr), SemanticTokenType::KEYWORD))
                }
                crate::expr::Pattern::Bind(_name) => {}
                crate::expr::Pattern::Wildcard => {}
                crate::expr::Pattern::Variant { fields, .. } => {
                    result.extend(self.tokens_from_exprs(fields))
                }
            },
            Expr::Return(rhs) => {
                if let Some(rhs) = rhs {
                    result.extend(self.tokens_from_expr(rhs))
                }
            }
            Expr::Struct(_name, items, body) => {
                result.extend(self.tokens_from_exprs(items));
                result.extend(self.tokens_from_expr(body));
            }
            Expr::Property {
                name: _name,
                type_repr,
                default_value,
            } => {
                if let Some(type_repr) = type_repr {
                    result.extend(self.tokens_from_expr(type_repr));
                }
                if let Some(default_value) = default_value {
                    result.extend(self.tokens_from_expr(default_value));
                }
            }
            Expr::TypeRepr(_name, items, _) => result.extend(self.tokens_from_exprs(items)),
            Expr::FuncTypeRepr(items, ret, _) => {
                result.extend(self.tokens_from_exprs(items));
                result.extend(self.tokens_from_expr(ret));
            }
            Expr::TupleTypeRepr(items, _) => {
                result.extend(self.tokens_from_exprs(items));
            }
            Expr::Member(receiver, _) => {
                if let Some(receiver) = receiver {
                    result.extend(self.tokens_from_expr(receiver));
                }
            }
            Expr::Func {
                generics,
                params,
                body,
                ret,
                ..
            } => {
                result.extend(self.tokens_from_exprs(generics));
                result.extend(self.tokens_from_exprs(&params));
                result.extend(self.tokens_from_expr(body));
                if let Some(ret) = ret {
                    result.extend(self.tokens_from_expr(ret));
                }
            }
            Expr::Parameter(_name, ty) => {
                if let Some(ty) = ty {
                    result.extend(self.tokens_from_expr(ty));
                }
            }
            Expr::Let(_name, rhs) => {
                if let Some(rhs) = rhs {
                    result.extend(self.tokens_from_expr(rhs));
                }
            }
            Expr::Assignment(lhs, rhs) => result.extend(self.tokens_from_exprs(&[*lhs, *rhs])),
            Expr::Variable(_name, _) => {}
            Expr::If(cond, then, alt) => {
                result.extend(self.tokens_from_expr(cond));
                result.extend(self.tokens_from_expr(then));
                if let Some(alt) = alt {
                    result.extend(self.tokens_from_expr(alt));
                }
            }
            Expr::Loop(cond, body) => {
                if let Some(cond) = cond {
                    result.extend(self.tokens_from_expr(cond));
                }
                result.extend(self.tokens_from_expr(body));
            }
            Expr::EnumDecl(_name, items, body) => {
                result.extend(self.tokens_from_exprs(items));
                result.extend(self.tokens_from_expr(body));
            }
            Expr::EnumVariant(_name, items) => result.extend(self.tokens_from_exprs(items)),
            Expr::Match(_, items) => result.extend(self.tokens_from_exprs(items)),
            Expr::MatchArm(pattern, body) => {
                result.extend(self.tokens_from_exprs(&[*pattern, *body]))
            }
            Expr::PatternVariant(_name, _name1, items) => {
                result.extend(self.tokens_from_exprs(items))
            }
        };

        result
    }

    fn collect_tokens(&mut self) {
        eprintln!("Starting token collection...");
        self.tokens = self
            .source_file
            .root_ids()
            .iter()
            .flat_map(|id| self.tokens_from_expr(id))
            .collect();
        eprintln!("Collected {} tokens", self.tokens.len());
    }

    fn encode_tokens(mut self) -> Vec<SemanticToken> {
        self.tokens.sort_by(|(a, _), (b, _)| {
            a.start
                .line
                .cmp(&b.start.line)
                .then_with(|| a.start.character.cmp(&b.start.character))
        });

        let mut encoded_tokens = Vec::new();
        let mut last_pos = Position::new(0, 0);

        for (range, token_type) in self.tokens {
            if range.start.line != range.end.line {
                eprintln!("Warning: Skipping multi-line token: {:?}", range);
                continue;
            }

            if range.end.character < range.start.character {
                eprintln!("Warning: Invalid range detected: {:?}", range);
                continue;
            }

            let delta_line = range.start.line - last_pos.line;
            let delta_start = if delta_line == 0 {
                range.start.character - last_pos.character
            } else {
                range.start.character
            };
            let length = range.end.character - range.start.character;

            let token_type_index =
                TOKEN_TYPES.iter().position(|tt| tt == &token_type).unwrap() as u32;

            encoded_tokens.push(SemanticToken {
                delta_line,
                delta_start,
                length,
                token_type: token_type_index,
                token_modifiers_bitset: 0,
            });

            last_pos = range.start;
        }

        eprintln!("Encoded {} tokens", encoded_tokens.len());
        encoded_tokens
    }
}

#[cfg(test)]
mod tests {
    use async_lsp::lsp_types::{SemanticToken, SemanticTokenType};

    use crate::{
        lsp::{semantic_tokens::SemanticTokenCollector, server::TOKEN_TYPES},
        parser::parse,
    };

    fn tokens_for(code: &'static str) -> Vec<SemanticToken> {
        let parsed = parse(code, 0).unwrap();
        let mut semantic_tokens = SemanticTokenCollector::new(&parsed, code);
        semantic_tokens.collect_tokens();
        semantic_tokens.encode_tokens()
    }

    fn pos(token_type: SemanticTokenType) -> u32 {
        TOKEN_TYPES.iter().position(|t| *t == token_type).unwrap() as u32
    }

    #[test]
    fn gets_int_tokens() {
        assert_eq!(
            tokens_for("123\n1.23"),
            vec![
                SemanticToken {
                    delta_line: 0,
                    delta_start: 0,
                    length: 3,
                    token_type: pos(SemanticTokenType::NUMBER),
                    token_modifiers_bitset: 0
                },
                SemanticToken {
                    delta_line: 1,
                    delta_start: 0,
                    length: 4,
                    token_type: pos(SemanticTokenType::NUMBER),
                    token_modifiers_bitset: 0
                }
            ]
        );
    }

    #[test]
    fn gets_bool() {
        assert_eq!(
            tokens_for("true\n  false\n\ntrue"),
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
        );
    }
}
