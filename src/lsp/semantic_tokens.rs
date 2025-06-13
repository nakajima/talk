use std::collections::HashMap;

use crate::{
    Typed,
    expr::{Expr, Pattern},
    lexing::token::Token,
    name::Name,
    source_file::SourceFile,
    symbol_table::{SymbolInfo, SymbolKind, SymbolTable},
    token_kind::TokenKind as TalkTokenKind,
};
use async_lsp::lsp_types::{Position, Range, SemanticToken, SemanticTokenType};

use super::server::TOKEN_TYPES;

struct SemanticTokenCollector<'a> {
    source_file: &'a SourceFile<Typed>,
    symbol_table: &'a SymbolTable,
    source: &'a str,
    tokens: Vec<(Range, SemanticTokenType)>,
    line_starts: Vec<usize>,
}

pub fn collect(
    source_file: &SourceFile<Typed>,
    symbol_table: &SymbolTable,
    source: &str,
) -> Vec<SemanticToken> {
    let mut collector = SemanticTokenCollector::new(source_file, symbol_table, source);
    collector.collect_tokens();
    collector.encode_tokens()
}

impl<'a> SemanticTokenCollector<'a> {
    fn new(
        source_file: &'a SourceFile<Typed>,
        symbol_table: &'a SymbolTable,
        source: &'a str,
    ) -> Self {
        let line_starts = std::iter::once(0)
            .chain(source.match_indices('\n').map(|(i, _)| i + 1))
            .collect();

        Self {
            source_file,
            symbol_table,
            source,
            tokens: vec![],
            line_starts,
        }
    }

    fn collect_tokens(&mut self) {
        eprintln!("Starting token collection...");
        for (expr_id, typed_expr) in self.source_file.typed_exprs() {
            let meta = &self.source_file.meta[*expr_id as usize];
            match &typed_expr.expr {
                Expr::Variable(name, ..)
                | Expr::Parameter(name, ..)
                | Expr::Let(name, ..)
                | Expr::Property { name, .. }
                | Expr::EnumVariant(name, ..) => {
                    self.add_token_for_name(name, meta.start.start, meta.start.end);
                }
                Expr::Func {
                    name: Some(name), ..
                }
                | Expr::EnumDecl(name, ..)
                | Expr::Struct(name, ..) => {
                    self.add_token_for_name_in_decl(name, meta);
                }
                Expr::Pattern(Pattern::Bind(name)) => {
                    self.add_token_for_name(name, meta.start.start, meta.start.end);
                }
                _ => {}
            }
        }
        eprintln!("Collected {} tokens", self.tokens.len());
    }

    fn add_token_for_name(&mut self, name: &Name, start: usize, end: usize) {
        if let Name::Resolved(symbol_id, name_str) = name {
            if let Some(symbol_info) = self.symbol_table.get(symbol_id) {
                if let Some(token_type) = self.token_type_from_symbol(symbol_info) {
                    // Ensure we don't include trailing newlines
                    let actual_end = if name_str.is_empty() {
                        end
                    } else {
                        start + name_str.len()
                    };
                    let range = self.range_from_char_span(start, actual_end);
                    self.tokens.push((range, token_type));
                }
            }
        }
    }

    fn add_token_for_name_in_decl(&mut self, name: &Name, meta: &crate::expr::ExprMeta) {
        if let Name::Resolved(symbol_id, name_str) = name {
            let expr_source = &self.source[meta.start.start..meta.end.end];
            if let Some(byte_pos) = expr_source.find(name_str) {
                let start = meta.start.start + byte_pos;
                let end = start + name_str.len();
                self.add_token_for_name(name, start, end);
            } else if let Some(symbol_info) = self.symbol_table.get(symbol_id) {
                if let Some(token_type) = self.token_type_from_symbol(symbol_info) {
                    // Fallback for names that might be tricky to find, like operators
                    let range = self.range_from_char_span(meta.start.start, meta.start.end);
                    self.tokens.push((range, token_type));
                }
            }
        }
    }

    fn token_type_from_symbol(&self, symbol_info: &SymbolInfo) -> Option<SemanticTokenType> {
        match symbol_info.kind {
            SymbolKind::Func => Some(SemanticTokenType::FUNCTION),
            SymbolKind::Param => Some(SemanticTokenType::PARAMETER),
            SymbolKind::Local | SymbolKind::PatternBind => Some(SemanticTokenType::VARIABLE),
            SymbolKind::Enum => Some(SemanticTokenType::ENUM),
            SymbolKind::EnumVariant(_) => Some(SemanticTokenType::ENUM_MEMBER),
            SymbolKind::Struct => Some(SemanticTokenType::STRUCT),
            SymbolKind::BuiltinType => Some(SemanticTokenType::TYPE),
            SymbolKind::CustomType => Some(SemanticTokenType::TYPE),
            SymbolKind::TypeParameter => Some(SemanticTokenType::TYPE_PARAMETER),
            SymbolKind::BuiltinFunc => Some(SemanticTokenType::FUNCTION),
            SymbolKind::VariantConstructor => Some(SemanticTokenType::ENUM_MEMBER),
        }
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
            // Skip tokens that span multiple lines
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

    fn range_from_token(&self, token: &Token) -> Range {
        self.range_from_char_span(token.start, token.end)
    }

    fn range_from_char_span(&self, start: usize, end: usize) -> Range {
        Range {
            start: self.pos_from_char_offset(start),
            end: self.pos_from_char_offset(end),
        }
    }

    fn pos_from_char_offset(&self, offset: usize) -> Position {
        let mut line = 0;
        let mut line_start = 0;
        for (i, l_start) in self.line_starts.iter().enumerate() {
            if *l_start > offset {
                break;
            }
            line = i;
            line_start = *l_start;
        }

        let line_content = &self.source[line_start..offset];
        let character = line_content.chars().count();

        Position {
            line: line as u32,
            character: character as u32,
        }
    }
}
