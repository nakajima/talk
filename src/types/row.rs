use std::collections::BTreeMap;

use crate::{
    label::Label,
    types::{
        ty::Ty,
        type_operations::{UnificationSubstitutions, apply, apply_row},
        type_session::TypeDefKind,
    },
};

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct RowMetaId(pub u32);
impl From<u32> for RowMetaId {
    fn from(value: u32) -> Self {
        RowMetaId(value)
    }
}

impl std::fmt::Debug for RowMetaId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "π{}", self.0)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct RowParamId(pub u32);
impl From<u32> for RowParamId {
    fn from(value: u32) -> Self {
        RowParamId(value)
    }
}

pub type ClosedRow = BTreeMap<Label, Ty>;

// TODO: Add Level to Var once we support open rows
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Row {
    Empty(TypeDefKind),
    Extend { row: Box<Row>, label: Label, ty: Ty },
    Param(RowParamId),
    Var(RowMetaId),
}

impl Row {
    pub fn close(&self) -> ClosedRow {
        close(self, ClosedRow::default())
    }
}

fn close(row: &Row, mut closed_row: ClosedRow) -> ClosedRow {
    match row {
        Row::Empty(..) => closed_row,
        Row::Var(_) => panic!("Cannot close var"),
        Row::Param(_) => panic!("Cannot close param"),
        Row::Extend { row, label, ty } => {
            closed_row.insert(label.clone(), ty.clone());
            close(row, closed_row)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RowTail {
    Empty,
    Var(RowMetaId),
    Param(RowParamId),
}

pub fn normalize_row(
    mut row: Row,
    subs: &mut UnificationSubstitutions,
) -> (BTreeMap<Label, Ty>, RowTail) {
    let mut map = BTreeMap::new();
    loop {
        row = apply_row(row, subs);
        match row {
            Row::Extend {
                row: rest,
                label,
                ty,
            } => {
                map.insert(label, apply(ty, subs));
                row = *rest;
            }
            Row::Empty(..) => break (map, RowTail::Empty),
            Row::Var(id) => break (map, RowTail::Var(subs.canon_row(id))),
            Row::Param(id) => break (map, RowTail::Param(id)),
        }
    }
}
