pub fn clamp_to_char_boundary(text: &str, mut idx: usize) -> usize {
    if idx > text.len() {
        idx = text.len();
    }
    while idx > 0 && !text.is_char_boundary(idx) {
        idx -= 1;
    }
    idx
}

pub fn line_info_for_offset(text: &str, byte_offset: u32) -> (u32, u32, usize, usize) {
    let offset = clamp_to_char_boundary(text, byte_offset as usize);
    let mut line: u32 = 1;
    let mut last_line_start = 0usize;

    for (idx, ch) in text.char_indices() {
        if idx >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            last_line_start = idx + ch.len_utf8();
        }
    }

    let line_end = text[offset..]
        .find('\n')
        .map(|idx| offset + idx)
        .unwrap_or(text.len());
    let col = text[last_line_start..offset].chars().count() as u32 + 1;
    (line, col, last_line_start, line_end)
}
