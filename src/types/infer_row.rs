use std::collections::BTreeMap;

use derive_visitor::{Drive, DriveMut};
use ena::unify::UnifyKey;
use indexmap::IndexMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    types::{
        infer_ty::{Infer, InferTy, InnerTy, Level, TypePhase, format_row},
        predicate::Predicate,
        row::Row,
        scheme::ForAll,
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

pub type InferRow = InnerRow<Infer>;

// TODO: Add Level to Var once we support open rows
#[derive(PartialEq, Eq, Hash, Clone, Drive, DriveMut)]
pub enum InnerRow<Phase: TypePhase> {
    Empty,
    Extend {
        row: Box<InnerRow<Phase>>,
        #[drive(skip)]
        label: Label,
        ty: InnerTy<Phase>,
    },
    Param(#[drive(skip)] RowParamId),
    Var(#[drive(skip)] Phase::RowVar),
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

impl<Phase: TypePhase> InnerRow<Phase> {
    pub fn close(&self) -> ClosedRow<Self> {
        close(self, ClosedRow::default())
    }

    fn contains_type_params(&self) -> bool {
        match self {
            InnerRow::Empty => false,
            InnerRow::Extend { row, ty, .. } => {
                row.contains_type_params() || ty.contains_type_params()
            }
            InnerRow::Param(..) => true,
            InnerRow::Var(_) => false,
        }
    }

    pub fn collect_metas(&self) -> Vec<InnerTy<Phase>> {
        let mut result = vec![];
        match self {
            Self::Param(..) | Self::Empty => (),
            Self::Extend { row, ty, .. } => {
                result.extend(row.collect_metas());
                result.extend(ty.collect_metas());
            }
            Self::Var(var) => {
                result.push(InnerTy::<Phase>::Record(Self::Var(*var).into())); // This is a hack
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

    pub fn collect_param_predicates(&self) -> Vec<Predicate<Phase>> {
        let mut result = vec![];
        match self {
            Self::Empty | Self::Var(..) | Self::Param(..) => (),
            Self::Extend { row, ty, .. } => {
                result.extend(ty.collect_param_predicates());
                result.extend(row.collect_param_predicates());
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

impl<T: TypePhase> std::fmt::Debug for InnerRow<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "{{}}"),
            Self::Extend { .. } => {
                write!(f, "{:?}", format_row(self))
            }
            Self::Param(id) => write!(f, "rowparam{id:?}"),
            Self::Var(id) => write!(f, "rowvar{id:?}"),
        }
    }
}
