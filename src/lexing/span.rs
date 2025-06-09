use crate::file_store::FileID;

pub struct Span {
    pub start: usize,
    pub end: usize,
    pub file_id: FileID,
}
