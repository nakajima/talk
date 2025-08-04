use crate::types::ty::Ty;

#[derive(Debug)]
pub enum Direction {
    Left,
    Right,
}

pub type Label = String;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct RowCombination {
    pub left: Row,
    pub right: Row,
    pub goal: Row,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct RowVar(pub u32);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum Row {
    Open(RowVar),
    Closed(ClosedRow),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct ClosedRow {
    // Sorted lexographically
    pub fields: Vec<Label>,
    // One type for each field in fields
    pub values: Vec<Ty>,
}
