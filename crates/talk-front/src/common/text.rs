pub fn clamp_to_char_boundary(text: &str, mut idx: usize) -> usize {
    if idx > text.len() {
        idx = text.len();
    }
    while idx > 0 && !text.is_char_boundary(idx) {
        idx -= 1;
    }
    idx
}

/// One-shot line/column lookup: builds a line index for this call.
/// Callers converting several offsets into the same text should build
/// the `LineIndex` once and use it directly.
pub fn line_info_for_offset(text: &str, byte_offset: u32) -> (u32, u32, usize, usize) {
    crate::common::line_index::LineIndex::new(text).line_info_utf8(text, byte_offset)
}

pub fn line_info_for_offset_utf16(text: &str, byte_offset: u32) -> (u32, u32, usize, usize) {
    crate::common::line_index::LineIndex::new(text).line_info_utf16(text, byte_offset)
}

pub fn byte_offset_for_line_column_utf8(text: &str, line: u32, column: u32) -> Option<u32> {
    crate::common::line_index::LineIndex::new(text)
        .byte_offset_for_line_column_utf8(text, line, column)
}
