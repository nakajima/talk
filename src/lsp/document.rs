use async_lsp::lsp_types::{Position, Range, SemanticTokensResult, TextDocumentContentChangeEvent};

use crate::common::line_index::LineIndex;

pub struct Document {
    pub version: i32,
    pub text: String,
    pub semantic_tokens: Option<SemanticTokensResult>,
    /// Cached line-start offsets for every position conversion (CLEAN-07);
    /// rebuilt when the text changes.
    line_index: LineIndex,
}

impl Document {
    pub fn new(version: i32, text: String) -> Self {
        let line_index = LineIndex::new(&text);
        Self {
            version,
            text,
            semantic_tokens: None,
            line_index,
        }
    }

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
                        self.byte_offset(range.start),
                        self.byte_offset(range.end),
                    );
                    if let (Some(start), Some(end)) = (start, end)
                        && start <= end
                    {
                        self.text.replace_range(start..end, new_text);
                    } else {
                        // Fallback: if mapping fails, replace whole text
                        self.text = new_text.clone();
                    }
                }
            }
        }
        self.line_index = LineIndex::new(&self.text);
    }

    pub fn line_index(&self) -> &LineIndex {
        &self.line_index
    }

    pub fn byte_offset(&self, pos: Position) -> Option<usize> {
        self.line_index
            .byte_offset_for_utf16_position(&self.text, pos.line, pos.character)
    }

    pub fn position_of_byte_offset(&self, byte_offset: usize) -> Option<Position> {
        let (line, character) = self
            .line_index
            .utf16_position_of_byte_offset(&self.text, byte_offset)?;
        Some(Position::new(line, character))
    }

    pub fn range_of_byte_span(&self, start: u32, end: u32) -> Option<Range> {
        let start = self.position_of_byte_offset(start as usize)?;
        let end = self.position_of_byte_offset(end as usize)?;
        Some(Range::new(start, end))
    }
}
