use std::collections::BTreeMap;

use indexmap::IndexMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    types::{
        infer_ty::InferTy,
        row::Row,
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

pub type ClosedRow<T> = IndexMap<Label, T>;

// TODO: Add Level to Var once we support open rows
#[derive(PartialEq, Eq, Hash, Clone)]
pub enum InferRow {
    Empty(TypeDefKind),
    Extend {
        row: Box<InferRow>,
        label: Label,
        ty: InferTy,
    },
    Param(RowParamId),
    Var(RowMetaId),
}

impl From<InferRow> for Row {
    fn from(value: InferRow) -> Self {
        match value {
            InferRow::Empty(t) => Row::Empty(t),
            InferRow::Param(param) => Row::Param(param),
            InferRow::Extend { box row, label, ty } => Row::Extend {
                row: Box::new(row.into()),
                label,
                ty: ty.into(),
            },
            row => panic!("Row cannot contain vars: {row:?}"),
        }
    }
}

impl From<Row> for InferRow {
    fn from(value: Row) -> Self {
        match value {
            Row::Empty(t) => InferRow::Empty(t),
            Row::Param(param) => InferRow::Param(param),
            Row::Extend { box row, label, ty } => InferRow::Extend {
                row: Box::new(row.into()),
                label,
                ty: ty.into(),
            },
        }
    }
}

impl InferRow {
    pub fn close(&self) -> ClosedRow<InferTy> {
        close(self, ClosedRow::default())
    }

    pub fn map<F: FnMut(InferTy) -> InferTy>(&self, f: &mut F) -> InferRow {
        match self.clone() {
            InferRow::Extend { row, label, ty } => InferRow::Extend {
                row: row.map(f).into(),
                label,
                ty: f(ty),
            },
            ty => ty,
        }
    }

    pub fn import(self, module_id: ModuleId) -> InferRow {
        if let InferRow::Extend { row, label, ty } = self {
            InferRow::Extend {
                row: row.import(module_id).into(),
                label,
                ty: ty.import(module_id),
            }
        } else {
            self
        }
    }
}

fn close(row: &InferRow, mut closed_row: ClosedRow<InferTy>) -> ClosedRow<InferTy> {
    match row {
        InferRow::Empty(..) => closed_row,
        InferRow::Var(_) => panic!("Cannot close var"),
        InferRow::Param(_) => panic!("Cannot close param"),
        InferRow::Extend { row, label, ty } => {
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
    mut row: InferRow,
    subs: &mut UnificationSubstitutions,
) -> (BTreeMap<Label, InferTy>, RowTail) {
    let mut map = BTreeMap::new();
    loop {
        row = apply_row(row, subs);
        match row {
            InferRow::Extend {
                row: rest,
                label,
                ty,
            } => {
                map.insert(label, apply(ty, subs));
                row = *rest;
            }
            InferRow::Empty(..) => break (map, RowTail::Empty),
            InferRow::Var(id) => break (map, RowTail::Var(subs.canon_row(id))),
            InferRow::Param(id) => break (map, RowTail::Param(id)),
        }
    }
}

impl std::fmt::Debug for InferRow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferRow::Empty(..) => write!(f, "{{}}"),
            InferRow::Extend { .. } => {
                write!(f, "{:?}", self.close())
            }
            InferRow::Param(id) => write!(f, "rowparam{id:?}"),
            InferRow::Var(id) => write!(f, "rowvar{id:?}"),
        }
    }
}
