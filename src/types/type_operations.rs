use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::types::{
    dsu::DSU,
    row::{Row, RowMetaId, RowParamId},
    ty::{Level, MetaId, Ty, TypeParamId},
    type_error::TypeError,
};

#[derive(Clone)]
pub struct UnificationSubstitutions {
    pub row: FxHashMap<RowMetaId, Row>,
    pub ty: FxHashMap<MetaId, Ty>,
    ty_dsu: DSU<MetaId>,
    row_dsu: DSU<RowMetaId>,
    meta_levels: FxHashMap<MetaId, Level>,
}

#[derive(Clone, Debug, Default)]
pub struct InstantiationSubstitutions {
    pub row: FxHashMap<RowParamId, RowMetaId>,
    pub ty: FxHashMap<TypeParamId, MetaId>,
}

impl std::fmt::Debug for UnificationSubstitutions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Subs(ty: {:?}, row: {:?}, ty_dsu: {:?}",
            self.ty, self.row, self.ty_dsu
        )
    }
}

impl UnificationSubstitutions {
    pub fn new(meta_levels: FxHashMap<MetaId, Level>) -> Self {
        Self {
            row: Default::default(),
            ty: Default::default(),
            ty_dsu: Default::default(),
            row_dsu: Default::default(),
            meta_levels,
        }
    }

    #[inline]
    pub fn canon_meta(&mut self, id: MetaId) -> MetaId {
        self.ty_dsu.find(id)
    }
    #[inline]
    pub fn canon_row(&mut self, id: RowMetaId) -> RowMetaId {
        self.row_dsu.find(id)
    }
    #[inline]
    pub fn link_meta(&mut self, a: MetaId, b: MetaId) -> MetaId {
        self.ty_dsu.union(a, b)
    }
    #[inline]
    pub fn link_row(&mut self, a: RowMetaId, b: RowMetaId) -> RowMetaId {
        self.row_dsu.union(a, b)
    }
}

fn occurs_in_row(id: MetaId, row: &Row) -> bool {
    match row {
        Row::Empty => false,
        Row::Var(_) => false,
        Row::Param(_) => false,
        Row::Extend { row, ty, .. } => occurs_in(id, ty) || occurs_in_row(id, row),
    }
}

// Helper: occurs check
fn occurs_in(id: MetaId, ty: &Ty) -> bool {
    match ty {
        Ty::MetaVar { id: mid, .. } => *mid == id,
        Ty::Func(a, b) => occurs_in(id, a) || occurs_in(id, b),
        Ty::Tuple(items) => items.iter().any(|t| occurs_in(id, t)),
        Ty::Record(row) => occurs_in_row(id, row),
        Ty::TypeApplication(f, x) => occurs_in(id, f) || occurs_in(id, x),
        Ty::Hole(..) => false,
        Ty::Param(..) => false,
        Ty::Rigid(..) => false,
        Ty::Primitive(..) => false,
        Ty::TypeConstructor { .. } => false,
    }
}

// Unify rows. Returns true if progress was made.
#[instrument(level = tracing::Level::DEBUG)]
fn unify_rows(
    lhs: &Row,
    rhs: &Row,
    substitutions: &mut UnificationSubstitutions,
) -> Result<bool, TypeError> {
    match (lhs, rhs) {
        (Row::Empty, Row::Empty) => Ok(false),
        (Row::Var(lhs_id), Row::Var(rhs_id)) if lhs_id == rhs_id => Ok(false),
        (Row::Var(lhs_id), Row::Var(rhs_id)) => {
            let ra = substitutions.canon_row(*lhs_id);
            let rb = substitutions.canon_row(*rhs_id);
            if ra != rb {
                let keep = substitutions.link_row(ra, rb);
                let lose = if keep == ra { rb } else { ra };
                if let Some(v) = substitutions.row.remove(&lose) {
                    substitutions.row.entry(keep).or_insert(v);
                }
                Ok(true)
            } else {
                Ok(false)
            }
        }
        (Row::Var(id), row) | (row, Row::Var(id)) => {
            // TODO: Occurs check for rows
            substitutions.row.insert(*id, row.clone());
            Ok(true)
        }
        (
            Row::Extend {
                row: lhs_row,
                label: lhs_label,
                ty: lhs_ty,
            },
            Row::Extend {
                row: rhs_row,
                label: rhs_label,
                ty: rhs_ty,
            },
        ) => {
            if lhs_label == rhs_label {
                // Same label, unify the types and continue with the rows
                let ty_unified = unify(lhs_ty, rhs_ty, substitutions)?;
                let row_unified = unify_rows(lhs_row, rhs_row, substitutions)?;
                Ok(ty_unified || row_unified)
            } else {
                // Different labels - need to check if we can reorder
                // For now, let's just fail
                Err(TypeError::InvalidUnification(
                    Ty::Record(Box::new(lhs.clone())),
                    Ty::Record(Box::new(rhs.clone())),
                ))
            }
        }
        _ => Err(TypeError::InvalidUnification(
            Ty::Record(Box::new(lhs.clone())),
            Ty::Record(Box::new(rhs.clone())),
        )),
    }
}

// Unify types. Returns true if progress was made.
#[instrument(level = tracing::Level::DEBUG)]
pub(super) fn unify(
    lhs: &Ty,
    rhs: &Ty,
    substitutions: &mut UnificationSubstitutions,
) -> Result<bool, TypeError> {
    let lhs = apply(lhs.clone(), substitutions);
    let rhs = apply(rhs.clone(), substitutions);
    match (&lhs, &rhs) {
        (Ty::Primitive(lhs), Ty::Primitive(rhs)) => {
            if lhs == rhs {
                Ok(false)
            } else {
                Err(TypeError::InvalidUnification(
                    Ty::Primitive(*lhs),
                    Ty::Primitive(*rhs),
                ))
            }
        }
        (Ty::Tuple(lhs), Ty::Tuple(rhs)) => {
            let mut did_change = false;
            for (lhs, rhs) in lhs.iter().zip(rhs) {
                did_change |= unify(lhs, rhs, substitutions)?;
            }
            Ok(did_change)
        }
        (Ty::Rigid(lhs), Ty::Rigid(rhs)) if lhs == rhs => Ok(false),
        (Ty::Func(lhs_param, lhs_ret), Ty::Func(rhs_param, rhs_ret)) => {
            let param = unify(lhs_param, rhs_param, substitutions)?;
            let ret = unify(lhs_ret, rhs_ret, substitutions)?;
            Ok(param || ret)
        }
        (
            Ty::TypeApplication(box lhs_rec, box lhs_arg),
            Ty::TypeApplication(box rhs_rec, box rhs_arg),
        ) => {
            let rec = unify(lhs_rec, rhs_rec, substitutions)?;
            let arg = unify(lhs_arg, rhs_arg, substitutions)?;
            Ok(rec || arg)
        }
        (
            Ty::MetaVar {
                id: lhs_id,
                level: _,
            },
            Ty::MetaVar {
                id: rhs_id,
                level: _,
            },
        ) => {
            let ra = substitutions.canon_meta(*lhs_id);
            let rb = substitutions.canon_meta(*rhs_id);
            if ra != rb {
                let keep = substitutions.link_meta(ra, rb);
                // if the losing rep had a binding, keep it by moving once:
                let lose = if keep == ra { rb } else { ra };
                if let Some(v) = substitutions.ty.remove(&lose) {
                    substitutions.ty.entry(keep).or_insert(v);
                }
                Ok(true)
            } else {
                Ok(false)
            }
        }
        (ty, Ty::MetaVar { id, .. }) | (Ty::MetaVar { id, .. }, ty) => {
            if occurs_in(*id, ty) {
                return Err(TypeError::OccursCheck(ty.clone())); // or your preferred variant
            }

            substitutions.ty.insert(*id, ty.clone());

            Ok(true)
        }
        (Ty::Record(lhs_row), Ty::Record(rhs_row)) => unify_rows(lhs_row, rhs_row, substitutions),
        (_, Ty::Rigid(_)) | (Ty::Rigid(_), _) => Err(TypeError::InvalidUnification(lhs, rhs)),
        _ => Err(TypeError::InvalidUnification(lhs, rhs)),
    }
}

#[instrument(ret)]
pub(super) fn substitute_row(row: Row, substitutions: &FxHashMap<Ty, Ty>) -> Row {
    match row {
        Row::Empty => row,
        Row::Var(..) => row,
        Row::Param(..) => row,
        Row::Extend { row, label, ty } => Row::Extend {
            row: Box::new(substitute_row(*row, substitutions)),
            label,
            ty: substitute(ty, substitutions),
        },
    }
}

#[instrument(ret)]
pub(super) fn substitute(ty: Ty, substitutions: &FxHashMap<Ty, Ty>) -> Ty {
    if let Some(subst) = substitutions.get(&ty) {
        return subst.clone();
    }
    match ty {
        Ty::Param(..) => ty,
        Ty::Hole(..) => ty,
        Ty::Rigid(..) => ty,
        Ty::MetaVar { .. } => ty,
        Ty::Primitive(..) => ty,
        Ty::TypeConstructor { .. } => todo!(),
        Ty::Func(params, ret) => Ty::Func(
            Box::new(substitute(*params, substitutions)),
            Box::new(substitute(*ret, substitutions)),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .into_iter()
                .map(|t| substitute(t, substitutions))
                .collect(),
        ),
        Ty::Record(row) => Ty::Record(Box::new(substitute_row(*row, substitutions))),
        Ty::TypeApplication(box lhs, box rhs) => Ty::TypeApplication(
            substitute(lhs, substitutions).into(),
            substitute(rhs, substitutions).into(),
        ),
    }
}

#[instrument(level = tracing::Level::TRACE, ret)]
pub(super) fn apply_row(row: Row, substitutions: &mut UnificationSubstitutions) -> Row {
    match row {
        Row::Empty => Row::Empty,
        Row::Var(id) => {
            let rep = substitutions.canon_row(id);
            if let Some(bound) = substitutions.row.get(&rep).cloned() {
                apply_row(bound, substitutions)
            } else {
                Row::Var(rep)
            }
        }
        Row::Param(_) => row,
        Row::Extend { row, label, ty } => Row::Extend {
            row: Box::new(apply_row(*row, substitutions)),
            label,
            ty: apply(ty, substitutions),
        },
    }
}

#[instrument(level = tracing::Level::TRACE, ret)]
pub(super) fn apply(ty: Ty, substitutions: &mut UnificationSubstitutions) -> Ty {
    match ty {
        Ty::Param(..) => ty,
        Ty::Hole(..) => ty,
        Ty::Rigid(..) => ty,
        Ty::MetaVar { id, .. } => {
            let rep = substitutions.canon_meta(id);
            if let Some(bound) = substitutions.ty.get(&rep).cloned() {
                apply(bound, substitutions) // keep collapsing
            } else {
                Ty::MetaVar {
                    id: rep,
                    level: *substitutions
                        .meta_levels
                        .get(&id)
                        .expect("did not get level"),
                } // normalize id to the representative
            }
        }
        Ty::Primitive(..) => ty,
        Ty::TypeConstructor { .. } => todo!(),
        Ty::Func(params, ret) => Ty::Func(
            Box::new(apply(*params, substitutions)),
            Box::new(apply(*ret, substitutions)),
        ),
        Ty::Tuple(items) => Ty::Tuple(items.into_iter().map(|t| apply(t, substitutions)).collect()),
        Ty::Record(row) => Ty::Record(Box::new(apply_row(*row, substitutions))),
        Ty::TypeApplication(box lhs, box rhs) => Ty::TypeApplication(
            apply(lhs, substitutions).into(),
            apply(rhs, substitutions).into(),
        ),
    }
}

#[instrument(level = tracing::Level::TRACE, ret)]
pub(super) fn instantiate_row(
    row: Row,
    substitutions: &InstantiationSubstitutions,
    level: Level,
) -> Row {
    match row {
        Row::Empty => row,
        Row::Var(..) => row,
        Row::Param(id) => {
            if let Some(row_meta) = substitutions.row.get(&id) {
                Row::Var(*row_meta)
            } else {
                row
            }
        }
        Row::Extend { row, label, ty } => Row::Extend {
            row: Box::new(instantiate_row(*row, substitutions, level)),
            label,
            ty: instantiate_ty(ty, substitutions, level),
        },
    }
}

#[instrument(ret)]
pub(super) fn instantiate_ty(
    ty: Ty,
    substitutions: &InstantiationSubstitutions,
    level: Level,
) -> Ty {
    match ty {
        Ty::Param(param) => {
            if let Some(meta) = substitutions.ty.get(&param) {
                Ty::MetaVar { id: *meta, level }
            } else {
                ty
            }
        }
        Ty::Hole(..) => ty,
        Ty::Rigid(..) => ty,
        Ty::MetaVar { .. } => ty,
        Ty::Primitive(..) => ty,
        Ty::TypeConstructor { .. } => todo!(),
        Ty::Func(params, ret) => Ty::Func(
            Box::new(instantiate_ty(*params, substitutions, level)),
            Box::new(instantiate_ty(*ret, substitutions, level)),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .into_iter()
                .map(|t| instantiate_ty(t, substitutions, level))
                .collect(),
        ),
        Ty::Record(row) => Ty::Record(Box::new(instantiate_row(*row, substitutions, level))),
        Ty::TypeApplication(box lhs, box rhs) => Ty::TypeApplication(
            instantiate_ty(lhs, substitutions, level).into(),
            instantiate_ty(rhs, substitutions, level).into(),
        ),
    }
}
