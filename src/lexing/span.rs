use std::path::PathBuf;

use crate::diagnostic::Position;
use serde::{Serialize, Deserialize};

#[derive(Default, Debug, Eq, PartialEq, Hash, Clone, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
    pub path: PathBuf,
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

    pub fn length(&self) -> u32 {
        self.end - self.start
    }

    pub fn contains_span(&self, span: &Span) -> bool {
        self.start <= span.start && self.end >= span.end
    }
}
