use async_lsp::lsp_types::{Position, Range, SemanticTokensResult, TextDocumentContentChangeEvent};
use std::sync::Arc;

use crate::{
    ast::{AST, NameResolved},
    name_resolution::name_resolver::ResolvedNames,
    types::type_session::Types,
};

pub struct DocumentAnalysis {
    pub version: i32,
    pub ast: AST<NameResolved>,
    pub resolved_names: ResolvedNames,
    pub types: Option<Types>,
}

pub struct Document {
    pub version: i32,
    pub text: String,
    pub last_edited_tick: i32,
    pub semantic_tokens: Option<SemanticTokensResult>,
    pub analysis: Option<Arc<DocumentAnalysis>>,
}

impl Document {
    pub fn apply_changes(&mut self, changes: &[TextDocumentContentChangeEvent]) {
        for change in changes {
            match (&change.range, &change.text) {
                (None, new_text) => {
                    // Full content replacement
                    self.text = new_text.clone();
                }
                (Some(range), new_text) => {
                    // Minimal UTF-16 aware range edit
                    let (start, end) = (
                        utf16_position_to_byte_offset(&self.text, range.start),
                        utf16_position_to_byte_offset(&self.text, range.end),
                    );
                    if let (Some(start), Some(end)) = (start, end) {
                        self.text.replace_range(start..end, new_text);
                    } else {
                        // Fallback: if mapping fails, replace whole text
                        self.text = new_text.clone();
                    }
                }
            }
        }
    }

    pub fn byte_offset(&self, pos: Position) -> Option<usize> {
        utf16_position_to_byte_offset(&self.text, pos)
    }

    pub fn position_of_byte_offset(&self, byte_offset: usize) -> Option<Position> {
        byte_offset_to_utf16_position(&self.text, byte_offset)
    }

    pub fn range_of_byte_span(&self, start: u32, end: u32) -> Option<Range> {
        let start = byte_offset_to_utf16_position(&self.text, start as usize)?;
        let end = byte_offset_to_utf16_position(&self.text, end as usize)?;
        Some(Range::new(start, end))
    }
}

// LSP Positions are UTF-16 code unit based. Convert to byte offsets for Rust strings.
fn utf16_position_to_byte_offset(text: &str, pos: Position) -> Option<usize> {
    let mut current_line: u32 = 0;
    let mut byte_index: usize = 0;

    for line in text.split_inclusive('\n') {
        if current_line == pos.line {
            // Walk this line to find the column in utf-16 code units
            let mut col_units: u32 = 0;
            for (offset, ch) in line.char_indices() {
                if col_units == pos.character {
                    return Some(byte_index + offset);
                }
                col_units += utf16_len(ch) as u32;
            }
            // End of line ⇒ clamp to line end
            return Some(byte_index + line.len());
        }
        byte_index += line.len();
        current_line += 1;
    }
    // Beyond last line ⇒ clamp to text end
    if current_line == pos.line {
        return Some(text.len());
    }
    None
}

fn utf16_len(ch: char) -> usize {
    if (ch as u32) < 0x10000 { 1 } else { 2 }
}

fn byte_offset_to_utf16_position(text: &str, byte_offset: usize) -> Option<Position> {
    if byte_offset > text.len() {
        return None;
    }

    let before = text.get(..byte_offset)?;
    let line = before.matches('\n').count() as u32;
    let line_start = before.rfind('\n').map(|i| i + 1).unwrap_or(0);
    let col_slice = text.get(line_start..byte_offset)?;
    let col = col_slice.encode_utf16().count() as u32;

    Some(Position::new(line, col))
}
