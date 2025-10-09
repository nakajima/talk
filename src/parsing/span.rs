use crate::node_id::FileID;

#[derive(Clone, Copy, Eq)]
pub struct Span {
    pub file_id: FileID,
    pub start: u32,
    pub end: u32,
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl Span {
    pub const SYNTHESIZED: Span = Span {
        file_id: FileID::SYNTHESIZED,
        start: u32::MAX - 1,
        end: u32::MAX - 1,
    };
    pub const ANY: Span = Span {
        file_id: FileID(u32::MAX),
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
