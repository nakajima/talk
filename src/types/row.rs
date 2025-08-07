use std::fmt::Display;

use derive_visitor::DriveMut;

use crate::types::{ty::Ty, type_var::TypeVar, type_var_context::RowVar};

#[derive(Debug)]
pub enum Direction {
    Left,
    Right,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Label {
    String(String),
    Int(u32),
}

impl<T: Into<String>> From<T> for Label {
    fn from(value: T) -> Self {
        Label::String(value.into())
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Label::String(string) => write!(f, "{string}"),
            Label::Int(i) => write!(f, "{i}"),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct RowCombination {
    pub left: Row,
    pub right: Row,
    pub goal: Row,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, DriveMut, PartialOrd, Ord)]
pub enum Row {
    Open(#[drive(skip)] RowVar),
    Closed(ClosedRow),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, DriveMut, PartialOrd, Ord)]
pub struct ClosedRow {
    // Sorted lexographically
    #[drive(skip)]
    pub fields: Vec<Label>,
    // One type for each field in fields
    pub values: Vec<Ty>,
}
