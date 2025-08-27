use std::u32;

#[derive(Clone, Copy, Debug, Eq)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const ANY: Span = Span {
        start: u32::MAX,
        end: u32::MAX,
    };
}

#[cfg(test)]
impl PartialEq for Span {
    fn eq(&self, other: &Self) -> bool {
        if self.start == u32::MAX || other.start == u32::MAX {
            true
        } else {
            self.start == other.start && self.end == other.end
        }
    }
}

#[cfg(not(test))]
impl PartialEq for Span {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.end == other.end
    }
}
