use derive_visitor::{Drive, DriveMut};
use futures::never::Never;
use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name_resolution::symbol::Symbol,
    types::{
        effect_signature::EffectSignature,
        importable::Importable,
        infer_ty::{InferTy, Unfinalizable},
        metas::{Meta, RowMetaId},
        scheme::ForAll,
        ty::{SomeType, Ty, TypeTraversable},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, substitute},
        type_session::TypeSession,
    },
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct RowParamId(pub u32);
impl From<u32> for RowParamId {
    fn from(value: u32) -> Self {
        RowParamId(value)
    }
}

pub type ClosedRow<T: RowType> = IndexMap<T::ID, T::Value>;

pub trait RowType:
    std::fmt::Debug + PartialEq + Eq + std::hash::Hash + Clone + Drive + DriveMut
{
    type ID: Importable
        + std::fmt::Debug
        + PartialEq
        + Eq
        + std::hash::Hash
        + Clone
        + PartialOrd
        + Ord;
    type Value: RowValue
        + TypeTraversable
        + Importable
        + std::fmt::Debug
        + PartialEq
        + Eq
        + std::hash::Hash
        + Clone
        + PartialOrd
        + Drive
        + DriveMut;
    type Ty: SomeType + std::fmt::Debug + PartialEq + Eq + std::hash::Hash + Clone + PartialOrd;
    type Var: std::fmt::Debug + PartialEq + Eq + std::hash::Hash + Clone + Copy + PartialOrd + Ord;
}

pub trait RowValue {
    fn apply(self, session: &mut TypeSession, substitutions: &mut UnificationSubstitutions)
    -> Self;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Drive, DriveMut)]
pub struct Extend<T: RowType> {
    pub row: Box<Row<T>>,
    #[drive(skip)]
    pub id: T::ID,
    pub value: T::Value,
}

impl<T: RowType> Importable for Extend<T> {
    fn import(self, module_id: ModuleId) -> Self {
        Extend {
            row: Box::new(self.row.import(module_id)),
            id: self.id.import(module_id),
            value: self.value.import(module_id),
        }
    }
}

pub trait InferRowType: RowType<Var = RowMetaId> {
    type FinalizesTo;
}
pub trait FinalizedRowType: RowType<Var = Never> {
    type FinalizesFrom;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Drive, DriveMut)]
pub enum Row<T: RowType> {
    Empty,
    Var(#[drive(skip)] T::Var),
    Param(#[drive(skip)] RowParamId),
    Extend(Extend<T>),
}

impl<T: InferRowType> TypeTraversable for Row<T> {
    type T = InferTy;

    fn collect_foralls(&self) -> indexmap::IndexSet<super::scheme::ForAll> {
        let mut result = IndexSet::default();
        match self {
            Self::Var(..) | Self::Empty => (),
            Self::Param(id) => {
                result.insert(ForAll::Row(*id));
            }
            Self::Extend(extend) => {
                result.extend(extend.row.collect_foralls());
                result.extend(extend.value.collect_foralls());
            }
        }
        result
    }

    fn collect_metas(&self) -> IndexSet<super::metas::Meta> {
        let mut result = IndexSet::default();
        match self {
            Self::Param(..) | Self::Empty => (),
            Self::Var(id) => {
                result.insert(Meta::Row((*id).into()));
            }
            Self::Extend(extend) => {
                result.extend(extend.row.collect_metas());
                result.extend(extend.value.collect_metas());
            }
        }
        result
    }

    fn contains_meta(&self, meta: Meta) -> bool {
        match self {
            Self::Param(..) | Self::Empty => false,
            Self::Var(id) => Meta::Row(*id) == meta,
            Self::Extend(extend) => {
                extend.value.contains_meta(meta) || extend.row.contains_meta(meta)
            }
        }
    }
}

impl<T: RowType> Row<T> {
    pub fn close(&self) -> ClosedRow<T> {
        close(self, ClosedRow::<T>::default())
    }
}

impl<T: RowType> Importable for Row<T> {
    fn import(self, module_id: ModuleId) -> Self {
        match self {
            Self::Empty => self,
            Self::Var(..) => self,
            Self::Param(..) => self,
            Self::Extend(extend) => Self::Extend(extend.import(module_id)),
        }
    }
}

impl Unfinalizable for Row<FinalizedRow> {
    type From = Row<InferRow>;

    fn unfinalize(self, session: &mut TypeSession) -> Result<Self::From, TypeError> {
        Ok(match self {
            Self::Var(..) => unreachable!(),
            Self::Param(id) => Row::Param(id),
            Self::Empty => Row::Empty,
            Self::Extend(extend) => Row::Extend(Extend {
                row: extend.row.unfinalize(session)?.into(),
                id: extend.id,
                value: extend.value.unfinalize(session)?,
            }),
        })
    }
}

impl Row<InferRow> {
    fn apply(
        self,
        session: &mut TypeSession,
        substitutions: &mut UnificationSubstitutions,
    ) -> Self {
        match self {
            Self::Param(..) | Self::Empty => self,
            Self::Var(ref id) => substitutions.row.get(id).cloned().unwrap_or(self),
            Self::Extend(extend) => Self::Extend(Extend {
                row: extend.row.apply(session, substitutions).into(),
                id: extend.id,
                value: extend.value.apply(session, substitutions),
            }),
        }
    }

    pub fn substitute(self, substitutions: &FxHashMap<InferTy, InferTy>) -> Self {
        match self {
            Self::Param(..) | Self::Empty | Self::Var(..) => self,
            Self::Extend(extend) => Self::Extend(Extend {
                row: extend.row.substitute(substitutions).into(),
                id: extend.id,
                value: substitute(extend.value, substitutions).into(),
            }),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Drive, DriveMut, PartialOrd)]
pub struct InferRow {}
impl RowType for InferRow {
    type ID = Label;
    type Value = InferTy;
    type Ty = InferTy;
    type Var = RowMetaId;
}

impl InferRowType for InferRow {
    type FinalizesTo = FinalizedRow;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Drive, DriveMut)]
pub struct FinalizedRow {}
impl RowType for FinalizedRow {
    type ID = Label;
    type Value = Ty;
    type Ty = Ty;
    type Var = Never;
}
impl FinalizedRowType for FinalizedRow {
    type FinalizesFrom = InferRow;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, Drive, DriveMut)]
pub struct InferEffectRow {}
impl RowType for InferEffectRow {
    type ID = Symbol;
    type Value = EffectSignature<InferTy>;
    type Ty = InferTy;
    type Var = RowMetaId;
}
impl InferRowType for InferEffectRow {
    type FinalizesTo = EffectRow;
}
impl From<EffectRow> for InferEffectRow {
    fn from(_value: EffectRow) -> Self {
        InferEffectRow {}
    }
}
impl From<InferEffectRow> for EffectRow {
    fn from(_value: InferEffectRow) -> Self {
        EffectRow {}
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, Drive, DriveMut)]
pub struct EffectRow {}
impl RowType for EffectRow {
    type ID = Symbol;
    type Value = EffectSignature<Ty>;
    type Ty = Ty;
    type Var = Never;
}
impl FinalizedRowType for EffectRow {
    type FinalizesFrom = InferEffectRow;
}

fn close<T: RowType>(row: &Row<T>, mut closed_row: ClosedRow<T>) -> ClosedRow<T> {
    #[allow(clippy::panic)]
    match row {
        Row::Empty => closed_row,
        Row::Var(..) | Row::Param(_) => panic!("Cannot close param: {row:?}"),
        Row::Extend(extend) => {
            closed_row.insert(extend.id.clone(), extend.value.clone());
            close(&extend.row, closed_row)
        }
    }
}

#[cfg(test)]
pub mod tests {}
