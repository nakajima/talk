//! A cached per-document line index (CLEAN-07): the byte offsets of
//! every line start, built once and reused by every position
//! conversion. One protocol-neutral implementation replaces the
//! independent UTF-16 and line/column converters that lived in
//! `common/text.rs`, `lsp/document.rs`, and `lsp/server.rs`; each
//! conversion is a binary search over the line starts plus at most a
//! scan of the target line.
//!
//! Two conventions meet here, so both live on the type with explicit
//! names:
//!
//! - 1-based `(line, col)` for CLI/wasm rendering (`line_info_*`,
//!   `byte_offset_for_line_column_utf8`), and
//! - 0-based `(line, character)` in UTF-16 code units for LSP
//!   (`utf16_position_of_byte_offset`, `byte_offset_for_utf16_position`).

use crate::common::text::clamp_to_char_boundary;

#[derive(Clone, Debug)]
pub struct LineIndex {
    /// Byte offset of each line's start; `line_starts[0]` is always 0.
    line_starts: Vec<u32>,
}

impl LineIndex {
    pub fn new(text: &str) -> Self {
        let mut line_starts = vec![0];
        for (index, byte) in text.bytes().enumerate() {
            if byte == b'\n' {
                line_starts.push(index as u32 + 1);
            }
        }
        Self { line_starts }
    }

    pub fn line_count(&self) -> u32 {
        self.line_starts.len() as u32
    }

    pub fn line_start(&self, line: u32) -> Option<u32> {
        self.line_starts.get(line as usize).copied()
    }

    /// The 0-based line containing `byte_offset`.
    fn line_of(&self, byte_offset: u32) -> u32 {
        match self.line_starts.binary_search(&byte_offset) {
            Ok(line) => line as u32,
            Err(next) => next as u32 - 1,
        }
    }

    /// The byte range of `line`'s text, excluding its newline.
    fn line_bounds(&self, text: &str, line_start: usize) -> (usize, usize) {
        let line_end = text[line_start..]
            .find('\n')
            .map(|index| line_start + index)
            .unwrap_or(text.len());
        (line_start, line_end)
    }

    /// 1-based `(line, col)` in UTF-8 chars plus the line's byte
    /// bounds: the CLI/wasm diagnostic rendering shape.
    pub fn line_info_utf8(&self, text: &str, byte_offset: u32) -> (u32, u32, usize, usize) {
        let offset = clamp_to_char_boundary(text, byte_offset as usize);
        let line = self.line_of(offset as u32);
        let (line_start, line_end) =
            self.line_bounds(text, self.line_starts[line as usize] as usize);
        let col = text[line_start..offset].chars().count() as u32 + 1;
        (line + 1, col, line_start, line_end)
    }

    /// 1-based `(line, col)` in UTF-16 code units plus the line's byte
    /// bounds.
    pub fn line_info_utf16(&self, text: &str, byte_offset: u32) -> (u32, u32, usize, usize) {
        let offset = clamp_to_char_boundary(text, byte_offset as usize);
        let line = self.line_of(offset as u32);
        let (line_start, line_end) =
            self.line_bounds(text, self.line_starts[line as usize] as usize);
        let col = text[line_start..offset].encode_utf16().count() as u32 + 1;
        (line + 1, col, line_start, line_end)
    }

    /// The byte offset of a 1-based `(line, column)` in UTF-8 chars.
    /// A column past the line's end clamps to the line end; a line past
    /// the text's end returns `None`.
    pub fn byte_offset_for_line_column_utf8(
        &self,
        text: &str,
        line: u32,
        column: u32,
    ) -> Option<u32> {
        if line == 0 || column == 0 {
            return None;
        }
        let line_start = *self.line_starts.get(line as usize - 1)? as usize;
        let (_, line_end) = self.line_bounds(text, line_start);

        let mut col = 1u32;
        let mut offset = line_start;
        for ch in text[line_start..line_end].chars() {
            if col == column {
                return Some(offset as u32);
            }
            offset += ch.len_utf8();
            col += 1;
        }
        Some(offset as u32)
    }

    /// The 0-based `(line, character)` in UTF-16 code units for a byte
    /// offset: the LSP position shape. `None` beyond the text's end or
    /// mid-character.
    pub fn utf16_position_of_byte_offset(
        &self,
        text: &str,
        byte_offset: usize,
    ) -> Option<(u32, u32)> {
        if byte_offset > text.len() {
            return None;
        }
        // A mid-character offset is not a valid position.
        text.get(..byte_offset)?;
        let line = self.line_of(byte_offset as u32);
        let line_start = self.line_starts[line as usize] as usize;
        let character = text.get(line_start..byte_offset)?.encode_utf16().count() as u32;
        Some((line, character))
    }

    /// The byte offset of a 0-based `(line, character)` in UTF-16 code
    /// units. LSP clients may send positions past the line or document
    /// end; those clamp exactly like the previous line-scanning
    /// implementation: mid-line overshoot lands on the newline,
    /// one-past-the-last-line lands on the text end, further out is
    /// `None`.
    pub fn byte_offset_for_utf16_position(
        &self,
        text: &str,
        line: u32,
        character: u32,
    ) -> Option<usize> {
        // The number of `split_inclusive('\n')` segments the old
        // implementation iterated; it defines where clamping stops.
        let segment_count = if text.is_empty() {
            0
        } else if text.ends_with('\n') {
            self.line_starts.len() - 1
        } else {
            self.line_starts.len()
        };

        let line = line as usize;
        if line == segment_count {
            return Some(text.len());
        }
        if line > segment_count {
            return None;
        }

        let line_start = self.line_starts[line] as usize;
        // The segment includes its newline: an overshot character
        // clamps past it, matching the old behavior.
        let segment_end = text[line_start..]
            .find('\n')
            .map(|index| line_start + index + 1)
            .unwrap_or(text.len());
        let segment = &text[line_start..segment_end];

        let mut col_units = 0u32;
        for (offset, ch) in segment.char_indices() {
            if col_units == character {
                return Some(line_start + offset);
            }
            col_units += if (ch as u32) < 0x10000 { 1 } else { 2 };
        }
        Some(line_start + segment.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_info_counts_lines_and_columns() {
        let text = "ab\ncd\nef";
        let index = LineIndex::new(text);
        assert_eq!(index.line_info_utf8(text, 0), (1, 1, 0, 2));
        assert_eq!(index.line_info_utf8(text, 3), (2, 1, 3, 5));
        assert_eq!(index.line_info_utf8(text, 7), (3, 2, 6, 8));
    }

    #[test]
    fn line_info_counts_utf16_units_for_astral_chars() {
        let text = "a\u{1F600}b\nx";
        let index = LineIndex::new(text);
        // Past the emoji: one char column but two UTF-16 units further.
        let offset = "a\u{1F600}".len() as u32;
        assert_eq!(index.line_info_utf8(text, offset).1, 3);
        assert_eq!(index.line_info_utf16(text, offset).1, 4);
    }

    #[test]
    fn byte_offset_for_line_column_resolves_and_clamps() {
        let text = "ab\ncde\n";
        let index = LineIndex::new(text);
        assert_eq!(index.byte_offset_for_line_column_utf8(text, 1, 1), Some(0));
        assert_eq!(index.byte_offset_for_line_column_utf8(text, 2, 3), Some(5));
        // Column past the line's end clamps to the line end.
        assert_eq!(index.byte_offset_for_line_column_utf8(text, 2, 99), Some(6));
        // The empty line after a trailing newline is still a line.
        assert_eq!(index.byte_offset_for_line_column_utf8(text, 3, 1), Some(7));
        // Past that is not a position.
        assert_eq!(index.byte_offset_for_line_column_utf8(text, 4, 1), None);
        assert_eq!(index.byte_offset_for_line_column_utf8(text, 0, 1), None);
    }

    #[test]
    fn utf16_positions_round_trip() {
        let text = "ab\nc\u{1F600}d\nef\n";
        let index = LineIndex::new(text);
        for offset in 0..=text.len() {
            if !text.is_char_boundary(offset) {
                continue;
            }
            let (line, character) = index
                .utf16_position_of_byte_offset(text, offset)
                .expect("position");
            let back = index
                .byte_offset_for_utf16_position(text, line, character)
                .expect("byte offset");
            assert_eq!(back, offset, "offset {offset}");
        }
    }

    #[test]
    fn utf16_position_rejects_mid_character_and_past_end() {
        let text = "a\u{1F600}";
        let index = LineIndex::new(text);
        assert_eq!(index.utf16_position_of_byte_offset(text, 2), None);
        assert_eq!(
            index.utf16_position_of_byte_offset(text, text.len() + 1),
            None
        );
    }

    #[test]
    fn utf16_byte_offset_clamps_like_the_lsp() {
        // A character past the line's UTF-16 length lands on (and past)
        // the line's newline.
        let text = "ab\ncd\n";
        let index = LineIndex::new(text);
        assert_eq!(index.byte_offset_for_utf16_position(text, 0, 99), Some(3));
        // One line past the last lands on the text end.
        assert_eq!(index.byte_offset_for_utf16_position(text, 2, 0), Some(6));
        assert_eq!(index.byte_offset_for_utf16_position(text, 2, 10), Some(6));
        // Further out is not a position.
        assert_eq!(index.byte_offset_for_utf16_position(text, 3, 0), None);
    }

    #[test]
    fn utf16_byte_offset_without_trailing_newline() {
        let text = "ab\ncd";
        let index = LineIndex::new(text);
        assert_eq!(index.byte_offset_for_utf16_position(text, 1, 99), Some(5));
        assert_eq!(index.byte_offset_for_utf16_position(text, 2, 0), Some(5));
        assert_eq!(index.byte_offset_for_utf16_position(text, 3, 0), None);
    }

    #[test]
    fn utf16_byte_offset_in_empty_text() {
        let text = "";
        let index = LineIndex::new(text);
        assert_eq!(index.byte_offset_for_utf16_position(text, 0, 0), Some(0));
        assert_eq!(index.byte_offset_for_utf16_position(text, 0, 10), Some(0));
        assert_eq!(index.byte_offset_for_utf16_position(text, 1, 0), None);
    }

    #[test]
    fn utf16_position_at_line_boundaries() {
        let text = "ab\ncd";
        let index = LineIndex::new(text);
        assert_eq!(index.utf16_position_of_byte_offset(text, 2), Some((0, 2)));
        assert_eq!(index.utf16_position_of_byte_offset(text, 3), Some((1, 0)));
        assert_eq!(index.utf16_position_of_byte_offset(text, 5), Some((1, 2)));
    }
}
