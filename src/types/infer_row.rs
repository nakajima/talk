use std::collections::BTreeMap;

use derive_visitor::{Drive, DriveMut};
use ena::unify::UnifyKey;
use indexmap::IndexMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    types::{
        infer_ty::{Level, Ty},
        predicate::Predicate,
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

pub type ClosedRow = IndexMap<Label, Ty>;

/// Unified row representation - used for both inference and final types.
/// The Var variant is only used during inference and should be resolved before codegen.
#[derive(PartialEq, Eq, Hash, Clone, Drive, DriveMut)]
pub enum Row {
    Empty,
    Extend {
        row: Box<Row>,
        #[drive(skip)]
        label: Label,
        ty: Ty,
    },
    Param(#[drive(skip)] RowParamId),
    /// Meta (unification) row variable - used during inference
    Var(#[drive(skip)] RowMetaId),
}

impl Row {
    pub fn close(&self) -> ClosedRow {
        close_generic(self, ClosedRow::default())
    }

    pub fn contains_type_params(&self) -> bool {
        match self {
            Row::Empty => false,
            Row::Extend { row, ty, .. } => row.contains_type_params() || ty.contains_type_params(),
            Row::Param(..) => true,
            Row::Var(_) => false,
        }
    }

    pub fn collect_metas(&self) -> Vec<Ty> {
        let mut result = vec![];
        match self {
            Self::Param(..) | Self::Empty => (),
            Self::Extend { row, ty, .. } => {
                result.extend(row.collect_metas());
                result.extend(ty.collect_metas());
            }
            Self::Var(var) => {
                result.push(Ty::Record(None, Self::Var(*var).into())); // This is a hack
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

    /// Visit all types and rows in this row, returning early if the visitor returns true.
    pub fn visit_ty(
        &self,
        ty_visitor: &mut impl FnMut(&Ty) -> bool,
        row_visitor: &mut impl FnMut(&Row) -> bool,
    ) -> bool {
        if row_visitor(self) {
            return true;
        }
        match self {
            Self::Extend { row, ty, .. } => {
                ty.visit(ty_visitor, row_visitor) || row.visit_ty(ty_visitor, row_visitor)
            }
            _ => false,
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

    pub fn collect_param_predicates(&self) -> Vec<Predicate> {
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

    pub fn import(self, module_id: ModuleId) -> Self {
        if let Row::Extend { row, label, ty } = self {
            Row::Extend {
                row: row.import(module_id).into(),
                label,
                ty: ty.import(module_id),
            }
        } else {
            self
        }
    }

    pub fn collect_specializations(
        &self,
        concrete: &Row,
    ) -> Result<Specializations, crate::types::type_error::TypeError> {
        let mut result = Specializations::default();
        match (self, concrete) {
            (Row::Empty, Row::Empty) => (),
            (Row::Param(id), other) => {
                if !matches!(other, Row::Param(..)) {
                    result.row.insert(*id, other.clone());
                }
            }
            (
                Row::Extend {
                    row: lhs_row,
                    ty: lhs_ty,
                    ..
                },
                Row::Extend {
                    row: rhs_row,
                    ty: rhs_ty,
                    ..
                },
            ) => {
                result.ty.extend(lhs_ty.collect_specializations(rhs_ty)?.ty);
                result
                    .row
                    .extend(lhs_row.collect_specializations(rhs_row)?.row);
            }
            _ => return Err(crate::types::type_error::TypeError::SpecializationMismatch),
        }
        Ok(result)
    }
}

#[allow(clippy::panic)]
fn close_generic(row: &Row, mut closed_row: ClosedRow) -> ClosedRow {
    match row {
        Row::Empty => closed_row,
        Row::Var(_) => panic!("Cannot close var"),
        Row::Param(_) => panic!("Cannot close param"),
        Row::Extend { row, label, ty } => {
            closed_row.insert(label.clone(), ty.clone());
            close_generic(row, closed_row)
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
    session: &mut TypeSession,
) -> (BTreeMap<Label, Ty>, RowTail) {
    let mut map = BTreeMap::new();
    loop {
        row = session.apply_row(&row, subs);
        match row {
            Row::Extend {
                row: rest,
                label,
                ty,
            } => {
                map.insert(label, session.apply(&ty, subs));
                row = *rest;
            }
            Row::Empty => break (map, RowTail::Empty),
            Row::Var(id) => break (map, RowTail::Var(session.canon_row(id))),
            Row::Param(id) => break (map, RowTail::Param(id)),
        }
    }
}

impl std::fmt::Debug for Row {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "{{}}"),
            Self::Extend { row, label, ty } => {
                write!(f, "{{ {label}: {ty:?} | {row:?} }}")
            }
            Self::Param(id) => write!(f, "rowparam{id:?}"),
            Self::Var(id) => write!(f, "rowvar{id:?}"),
        }
    }
}

// Specializations moved from ty.rs since it's needed here
use crate::name_resolution::symbol::Symbol;

#[derive(Default, Debug, Clone, PartialEq)]
pub struct Specializations {
    pub ty: IndexMap<Symbol, Ty>,
    pub row: IndexMap<RowParamId, Row>,
}

impl Specializations {
    pub fn is_empty(&self) -> bool {
        self.ty.is_empty() && self.row.is_empty()
    }

    pub fn extend(&mut self, other: Specializations) {
        self.ty.extend(
            other
                .ty
                .into_iter()
                .filter(|(_, v)| !matches!(v, Ty::Param(..))),
        );
        self.row.extend(
            other
                .row
                .into_iter()
                .filter(|(_, v)| !matches!(v, Row::Param(..))),
        );
    }

    pub fn apply(&self, ty: Ty) -> Ty {
        ty.mapping(
            &mut |t| {
                if let Ty::Param(id, _) = t
                    && let Some(replacement) = self.ty.get(&id)
                {
                    replacement.clone()
                } else {
                    t
                }
            },
            &mut |r| {
                if let Row::Param(id) = r
                    && let Some(replacement) = self.row.get(&id)
                {
                    replacement.clone()
                } else {
                    r
                }
            },
        )
    }
}

impl Ty {
    pub fn collect_specializations(
        &self,
        concrete: &Self,
    ) -> Result<Specializations, crate::types::type_error::TypeError> {
        let mut result = Specializations::default();
        match (self, concrete) {
            (Self::Primitive(..), Self::Primitive(..)) => (),
            (Self::Param(id, _), other) => {
                if !matches!(other, Self::Param(..)) {
                    result.ty.insert(*id, other.clone());
                }
            }
            (
                Self::Constructor {
                    params: lhs_params,
                    ret: lhs_ret,
                    ..
                },
                Self::Constructor {
                    params: rhs_params,
                    ret: rhs_ret,
                    ..
                },
            ) => {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    result.ty.extend(lhs.collect_specializations(rhs)?.ty);
                }

                result
                    .ty
                    .extend(lhs_ret.collect_specializations(rhs_ret)?.ty);
            }
            (
                Self::Constructor {
                    params: _constructor_params,
                    ret: box _constructor_ret,
                    ..
                },
                Self::Func(_func_params, _func_ret, _),
            )
            | (
                Self::Func(_func_params, _func_ret, _),
                Self::Constructor {
                    params: _constructor_params,
                    ret: box _constructor_ret,
                    ..
                },
            ) => (),
            (
                Self::Func(lhs_param, lhs_ret, lhs_effects),
                Self::Func(rhs_param, rhs_ret, rhs_effects),
            ) => {
                result
                    .ty
                    .extend(lhs_param.collect_specializations(rhs_param)?.ty);
                result
                    .ty
                    .extend(lhs_ret.collect_specializations(rhs_ret)?.ty);
                result
                    .row
                    .extend(lhs_effects.collect_specializations(rhs_effects)?.row)
            }
            (Self::Tuple(lhs_items), Self::Tuple(rhs_items)) => {
                for (lhs, rhs) in lhs_items.iter().zip(rhs_items) {
                    result.ty.extend(lhs.collect_specializations(rhs)?.ty);
                }
            }
            (Self::Record(.., lhs_row), Self::Record(.., rhs_row)) => {
                result
                    .row
                    .extend(lhs_row.collect_specializations(rhs_row)?.row);
            }
            (
                Self::Nominal {
                    type_args: lhs_args,
                    ..
                },
                Self::Nominal {
                    type_args: rhs_args,
                    ..
                },
            ) => {
                for (lhs, rhs) in lhs_args.iter().zip(rhs_args) {
                    result.ty.extend(lhs.collect_specializations(rhs)?.ty);
                }
            }
            tup => {
                tracing::error!("{tup:?}");
                return Err(crate::types::type_error::TypeError::SpecializationMismatch);
            }
        }
        Ok(result)
    }
}
