use crate::{diagnostic::Position, file_store::FileID};

#[derive(Default, Debug, Eq, PartialEq, Hash, Clone)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
    pub file_id: FileID,
}

impl Span {
    pub fn contains(&self, position: &Position) -> bool {
        if position.line < self.start_line || position.line > self.end_line {
            return false;
        }

        if position.line == self.start_line && position.line == self.end_line {
            return self.start_col <= position.col && self.end_col >= position.col;
        }

        true
    }

    pub fn contains_span(&self, span: &Span) -> bool {
        self.start <= span.start && self.end >= span.end
    }
}
