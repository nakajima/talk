use crate::token::Token;
use std::ops::Range;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NodeMeta {
    pub start: Token,
    pub end: Token,
    pub identifiers: Vec<Token>,
}

impl NodeMeta {
    pub fn generated() -> Self {
        Self {
            start: Token::GENERATED,
            end: Token::GENERATED,
            identifiers: vec![],
        }
    }

    pub fn excerpt(&self, _label: String, in_source: &str) -> String {
        in_source
            .chars()
            .skip(self.start.start as usize)
            .take((self.end.end - self.start.start.saturating_sub(1)) as usize)
            .collect()
    }

    pub fn span(&self) -> (usize, usize) {
        (
            self.start.start as usize,
            self.end.end.saturating_sub(self.start.start) as usize,
        )
    }

    pub fn source_range(&self) -> Range<u32> {
        self.start.start..self.end.end
    }
}
