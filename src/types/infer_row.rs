use std::collections::BTreeMap;

use derive_visitor::{Drive, DriveMut};
use ena::unify::UnifyKey;
use indexmap::IndexMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    types::{
        infer_ty::{InferTy, Level, format_row},
        row::Row,
        scheme::ForAll,
        ty::SomeType,
        type_operations::UnificationSubstitutions,
        type_session::TypeSession,
    },
};

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct RowMetaId(pub u32);
impl From<u32> for RowMetaId {
    fn from(value: u32) -> Self {
        RowMetaId(value)
    }
}

impl UnifyKey for RowMetaId {
    type Value = Level;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "meta"
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
#[derive(PartialEq, Eq, Hash, Clone, Drive, DriveMut)]
pub enum InferRow {
    Empty,
    Extend {
        row: Box<InferRow>,
        #[drive(skip)]
        label: Label,
        ty: InferTy,
    },
    Param(#[drive(skip)] RowParamId),
    Var(#[drive(skip)] RowMetaId),
}

impl From<InferRow> for Row {
    fn from(value: InferRow) -> Self {
        match value {
            InferRow::Empty => Row::Empty,
            InferRow::Param(param) => Row::Param(param),
            InferRow::Extend { box row, label, ty } => Row::Extend {
                row: Box::new(row.into()),
                label,
                ty: ty.into(),
            },
            // In error cases, row Vars may not be resolved. Default to Empty.
            InferRow::Var(_) => Row::Empty,
        }
    }
}

impl From<Row> for InferRow {
    fn from(value: Row) -> Self {
        match value {
            Row::Empty => InferRow::Empty,
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

    pub fn collect_metas(&self) -> Vec<InferTy> {
        let mut result = vec![];
        match self {
            InferRow::Param(..) | InferRow::Empty => (),
            InferRow::Extend { row, ty, .. } => {
                result.extend(row.collect_metas());
                result.extend(ty.collect_metas());
            }
            InferRow::Var(var) => {
                result.push(InferTy::Record(InferRow::Var(*var).into())); // This is a hack
            }
        }
        result
    }

    pub fn contains_var(&self) -> bool {
        match self {
            Self::Param(..) | Self::Empty => false,
            Self::Var(..) => true,
            Self::Extend { row, ty, .. } => row.contains_var() || ty.contains_var(),
        }
    }

    pub fn collect_foralls(&self) -> Vec<ForAll> {
        let mut result = vec![];
        match self {
            Self::Empty => (),
            Self::Var(..) => (),
            Self::Param(id) => {
                result.push(ForAll::Row(*id));
            }
            Self::Extend { row, ty, .. } => {
                result.extend(ty.collect_foralls());
                result.extend(row.collect_foralls());
            }
        }
        result
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

#[allow(clippy::panic)]
fn close(row: &InferRow, mut closed_row: ClosedRow<InferTy>) -> ClosedRow<InferTy> {
    match row {
        InferRow::Empty => closed_row,
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
    session: &mut TypeSession,
) -> (BTreeMap<Label, InferTy>, RowTail) {
    let mut map = BTreeMap::new();
    loop {
        row = session.apply_row(row, subs);
        match row {
            InferRow::Extend {
                row: rest,
                label,
                ty,
            } => {
                map.insert(label, session.apply(ty, subs));
                row = *rest;
            }
            InferRow::Empty => break (map, RowTail::Empty),
            InferRow::Var(id) => break (map, RowTail::Var(session.canon_row(id))),
            InferRow::Param(id) => break (map, RowTail::Param(id)),
        }
    }
}

impl std::fmt::Debug for InferRow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferRow::Empty => write!(f, "{{}}"),
            InferRow::Extend { .. } => {
                write!(f, "{:?}", format_row(self))
            }
            InferRow::Param(id) => write!(f, "rowparam{id:?}"),
            InferRow::Var(id) => write!(f, "rowvar{id:?}"),
        }
    }
}
