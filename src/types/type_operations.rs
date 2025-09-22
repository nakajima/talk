use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    label::Label,
    types::{
        dsu::DSU,
        passes::inference_pass::{Meta, curry},
        row::{Row, RowMetaId, RowParamId, RowTail, normalize_row},
        ty::{Level, Ty, TypeParamId, UnificationVarId},
        type_error::TypeError,
        type_session::TypeDefKind,
        vars::Vars,
    },
};

#[derive(Clone, Default)]
pub struct UnificationSubstitutions {
    pub row: FxHashMap<RowMetaId, Row>,
    pub ty: FxHashMap<UnificationVarId, Ty>,
    ty_dsu: DSU<UnificationVarId>,
    row_dsu: DSU<RowMetaId>,
    pub meta_levels: FxHashMap<Meta, Level>,
}

#[derive(Clone, Debug, Default)]
pub struct InstantiationSubstitutions {
    pub row: FxHashMap<RowParamId, RowMetaId>,
    pub ty: FxHashMap<TypeParamId, UnificationVarId>,
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
    pub fn new(meta_levels: FxHashMap<Meta, Level>) -> Self {
        Self {
            row: Default::default(),
            ty: Default::default(),
            ty_dsu: Default::default(),
            row_dsu: Default::default(),
            meta_levels,
        }
    }

    #[inline]
    pub fn canon_meta(&mut self, id: UnificationVarId) -> UnificationVarId {
        self.ty_dsu.find(id)
    }
    #[inline]
    pub fn canon_row(&mut self, id: RowMetaId) -> RowMetaId {
        self.row_dsu.find(id)
    }
    #[inline]
    pub fn link_meta(&mut self, a: UnificationVarId, b: UnificationVarId) -> UnificationVarId {
        self.ty_dsu.union(a, b)
    }
    #[inline]
    pub fn link_row(&mut self, a: RowMetaId, b: RowMetaId) -> RowMetaId {
        self.row_dsu.union(a, b)
    }
}

fn occurs_in_row(id: UnificationVarId, row: &Row) -> bool {
    match row {
        Row::Empty(..) => false,
        Row::Var(_) => false,
        Row::Param(_) => false,
        Row::Extend { row, ty, .. } => occurs_in(id, ty) || occurs_in_row(id, row),
    }
}

// Helper: occurs check
fn occurs_in(id: UnificationVarId, ty: &Ty) -> bool {
    match ty {
        Ty::UnificationVar { id: mid, .. } => *mid == id,
        Ty::Func(a, b) => occurs_in(id, a) || occurs_in(id, b),
        Ty::Tuple(items) => items.iter().any(|t| occurs_in(id, t)),
        Ty::Record(row) => occurs_in_row(id, row),
        Ty::Nominal { .. } => false,
        Ty::Hole(..) => false,
        Ty::Param(..) => false,
        Ty::Rigid(..) => false,
        Ty::Primitive(..) => false,
        Ty::Constructor { params, .. } => params.iter().any(|t| occurs_in(id, t)),
    }
}

fn row_occurs(target: RowMetaId, row: &Row, subs: &mut UnificationSubstitutions) -> bool {
    match apply_row(row.clone(), subs) {
        Row::Empty(..) | Row::Param(_) => false,
        Row::Var(id) => subs.canon_row(id) == subs.canon_row(target),
        Row::Extend { row, ty, .. } => {
            row_occurs(target, &row, subs)
                || matches!(apply(ty.clone(), subs), Ty::Record(r) if row_occurs(target, &r, subs))
        }
    }
}

// Unify rows. Returns true if progress was made.
#[instrument(level = tracing::Level::DEBUG)]
fn unify_rows(
    kind: TypeDefKind,
    lhs: &Row,
    rhs: &Row,
    subs: &mut UnificationSubstitutions,
    vars: &mut Vars,
) -> Result<bool, TypeError> {
    let (mut lhs_fields, lhs_tail) = normalize_row(lhs.clone(), subs);
    let (mut rhs_fields, rhs_tail) = normalize_row(rhs.clone(), subs);

    // Check to see if one side is closed and the other is a var. If so,
    // just unify the var as the other side
    if let (closed, RowTail::Empty, _, RowTail::Var(var))
    | (_, RowTail::Var(var), closed, RowTail::Empty) =
        (&lhs_fields, &lhs_tail, &rhs_fields, &rhs_tail)
    {
        tracing::debug!("unifying closed row with row var");
        let mut acc = Row::Empty(kind);
        for (label, ty) in closed.iter().rev() {
            acc = Row::Extend {
                row: Box::new(acc),
                label: label.clone(),
                ty: ty.clone(),
            };
        }

        let var = subs.canon_row(*var);
        subs.row.insert(var, acc);

        return Ok(true);
    }

    // unify common labels
    let mut changed = false;
    for k in lhs_fields.keys().cloned().collect::<Vec<_>>() {
        if let Some(rv) = rhs_fields.remove(&k) {
            let lv = lhs_fields.remove(&k).unwrap();
            changed |= unify(&lv, &rv, subs, vars)?;
        }
    }

    // helper: extend a Var tail with leftover fields (prepend over a fresh tail)
    let mut extend_var_tail =
        |tail_id: RowMetaId, fields: BTreeMap<Label, Ty>| -> Result<bool, TypeError> {
            if fields.is_empty() {
                return Ok(false);
            }
            let fresh = vars.row_metas.next_id();
            let mut acc = Row::Var(fresh);
            for (label, ty) in fields.into_iter().rev() {
                acc = Row::Extend {
                    row: Box::new(acc),
                    label,
                    ty,
                };
            }
            if row_occurs(tail_id, &acc, subs) {
                return Err(TypeError::OccursCheck(Ty::Record(Box::new(acc))));
            }

            let can = subs.canon_row(tail_id);
            subs.row.insert(can, acc);
            Ok(true)
        };

    // LHS leftovers must be absorbed by RHS tail
    if !lhs_fields.is_empty() {
        match rhs_tail {
            RowTail::Var(id) => {
                changed |= extend_var_tail(id, lhs_fields)?;
            }
            RowTail::Empty => {
                return Err(TypeError::InvalidUnification(
                    Ty::Record(Box::new(lhs.clone())),
                    Ty::Record(Box::new(rhs.clone())),
                ));
            }
            RowTail::Param(_) => {
                return Err(TypeError::InvalidUnification(
                    Ty::Record(Box::new(lhs.clone())),
                    Ty::Record(Box::new(rhs.clone())),
                ));
            }
        }
    }

    // RHS leftovers must be absorbed by LHS tail
    if !rhs_fields.is_empty() {
        match lhs_tail {
            RowTail::Var(id) => {
                changed |= extend_var_tail(id, rhs_fields)?;
            }
            RowTail::Empty => {
                return Err(TypeError::InvalidUnification(
                    Ty::Record(Box::new(lhs.clone())),
                    Ty::Record(Box::new(rhs.clone())),
                ));
            }
            RowTail::Param(_) => {
                return Err(TypeError::InvalidUnification(
                    Ty::Record(Box::new(lhs.clone())),
                    Ty::Record(Box::new(rhs.clone())),
                ));
            }
        }
    }

    // unify tails when both are metas/params (cheap)
    match (lhs_tail, rhs_tail) {
        (RowTail::Var(a), RowTail::Var(b)) if subs.canon_row(a) != subs.canon_row(b) => {
            let can_a = subs.canon_row(a);
            let can_b = subs.canon_row(b);
            subs.link_row(can_a, can_b);
            changed = true;
        }
        (RowTail::Param(a), RowTail::Param(b)) if a == b => {}
        (RowTail::Param(_), RowTail::Param(_)) => {
            return Err(TypeError::InvalidUnification(
                Ty::Record(Box::new(lhs.clone())),
                Ty::Record(Box::new(rhs.clone())),
            ));
        }
        _ => {}
    }

    Ok(changed)
}

// Unify types. Returns true if progress was made.
#[instrument(level = tracing::Level::DEBUG)]
pub(super) fn unify(
    lhs: &Ty,
    rhs: &Ty,
    substitutions: &mut UnificationSubstitutions,
    vars: &mut Vars,
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
                did_change |= unify(lhs, rhs, substitutions, vars)?;
            }
            Ok(did_change)
        }
        (Ty::Rigid(lhs), Ty::Rigid(rhs)) if lhs == rhs => Ok(false),
        (Ty::Param(lhs), Ty::Param(rhs)) if lhs == rhs => Ok(false),
        (
            Ty::Constructor {
                params, box ret, ..
            },
            Ty::Func(func_param, func_ret),
        )
        | (
            Ty::Func(func_param, func_ret),
            Ty::Constructor {
                params, box ret, ..
            },
        ) => unify(
            &curry(params.clone(), ret.clone()),
            &Ty::Func(func_param.clone(), func_ret.clone()),
            substitutions,
            vars,
        ),
        (
            Ty::Nominal {
                id: lhs_id,
                row: box lhs_row,
            },
            Ty::Nominal {
                id: rhs_id,
                row: box rhs_row,
            },
        ) => {
            if lhs_id != rhs_id {
                return Err(TypeError::InvalidUnification(lhs, rhs));
            }

            // Pick the correct row kind (Enum vs Struct) from the rows themselves.
            fn row_kind(r: &Row) -> Option<TypeDefKind> {
                match r {
                    Row::Empty(k) => Some(*k),
                    Row::Extend { row, .. } => row_kind(row),
                    Row::Var(_) | Row::Param(_) => None,
                }
            }
            let kind = row_kind(lhs_row)
                .or_else(|| row_kind(rhs_row))
                .unwrap_or(TypeDefKind::Struct);
            unify_rows(kind, lhs_row, rhs_row, substitutions, vars)
        }
        (Ty::Func(lhs_param, lhs_ret), Ty::Func(rhs_param, rhs_ret)) => {
            let param = unify(lhs_param, rhs_param, substitutions, vars)?;
            let ret = unify(lhs_ret, rhs_ret, substitutions, vars)?;
            Ok(param || ret)
        }
        (
            Ty::UnificationVar {
                id: lhs_id,
                level: _,
            },
            Ty::UnificationVar {
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
        (ty, Ty::UnificationVar { id, .. }) | (Ty::UnificationVar { id, .. }, ty) => {
            if occurs_in(*id, ty) {
                return Err(TypeError::OccursCheck(ty.clone())); // or your preferred variant
            }

            substitutions.ty.insert(*id, ty.clone());

            Ok(true)
        }
        (Ty::Record(lhs_row), Ty::Record(rhs_row)) => {
            unify_rows(TypeDefKind::Struct, lhs_row, rhs_row, substitutions, vars)
        }

        (_, Ty::Rigid(_)) | (Ty::Rigid(_), _) => Err(TypeError::InvalidUnification(lhs, rhs)),
        _ => {
            tracing::error!("attempted to unify {lhs:?} <> {rhs:?}");
            Err(TypeError::InvalidUnification(lhs, rhs))
        }
    }
}

#[instrument(ret)]
pub(super) fn substitute_row(row: Row, substitutions: &FxHashMap<Ty, Ty>) -> Row {
    match row {
        Row::Empty(..) => row,
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
        Ty::UnificationVar { .. } => ty,
        Ty::Primitive(..) => ty,
        Ty::Constructor {
            type_id,
            params,
            ret,
        } => Ty::Constructor {
            type_id,
            params: params
                .into_iter()
                .map(|p| substitute(p, substitutions))
                .collect(),
            ret: Box::new(substitute(*ret, substitutions)),
        },
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
        Ty::Nominal { id, box row } => Ty::Nominal {
            id,
            row: Box::new(substitute_row(row, substitutions)),
        },
    }
}

pub(super) fn apply_row(row: Row, substitutions: &mut UnificationSubstitutions) -> Row {
    match row {
        Row::Empty(kind) => Row::Empty(kind),
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

pub(super) fn apply(ty: Ty, substitutions: &mut UnificationSubstitutions) -> Ty {
    match ty {
        Ty::Param(..) => ty,
        Ty::Hole(..) => ty,
        Ty::Rigid(..) => ty,
        Ty::UnificationVar { id, .. } => {
            let rep = substitutions.canon_meta(id);
            if let Some(bound) = substitutions.ty.get(&rep).cloned() {
                apply(bound, substitutions) // keep collapsing
            } else {
                Ty::UnificationVar {
                    id: rep,
                    level: *substitutions
                        .meta_levels
                        .get(&Meta::Ty(id))
                        .unwrap_or_else(|| {
                            panic!(
                                "did not get level for {id:?} {:?}",
                                substitutions.meta_levels
                            )
                        }),
                } // normalize id to the representative
            }
        }
        Ty::Constructor {
            type_id,
            params,
            ret,
        } => Ty::Constructor {
            type_id,
            params: params
                .into_iter()
                .map(|p| apply(p, substitutions))
                .collect(),
            ret: Box::new(apply(*ret, substitutions)),
        },
        Ty::Primitive(..) => ty,
        Ty::Func(params, ret) => Ty::Func(
            Box::new(apply(*params, substitutions)),
            Box::new(apply(*ret, substitutions)),
        ),
        Ty::Tuple(items) => Ty::Tuple(items.into_iter().map(|t| apply(t, substitutions)).collect()),
        Ty::Record(row) => Ty::Record(Box::new(apply_row(*row, substitutions))),
        Ty::Nominal { id, box row } => Ty::Nominal {
            id,
            row: Box::new(apply_row(row, substitutions)),
        },
    }
}

pub fn apply_mult(tys: Vec<Ty>, substitutions: &mut UnificationSubstitutions) -> Vec<Ty> {
    tys.into_iter().map(|ty| apply(ty, substitutions)).collect()
}

#[instrument(level = tracing::Level::TRACE, ret)]
pub(super) fn instantiate_row(
    row: Row,
    substitutions: &InstantiationSubstitutions,
    level: Level,
) -> Row {
    match row {
        Row::Empty(..) => row,
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

pub(super) fn instantiate_ty(
    ty: Ty,
    substitutions: &InstantiationSubstitutions,
    level: Level,
) -> Ty {
    if substitutions.row.is_empty() && substitutions.ty.is_empty() {
        return ty;
    }

    let _s =
        tracing::trace_span!("instantiate_ty ty={ty:?} subs={substitutions:?} level={level:?}")
            .entered();
    match ty {
        Ty::Param(param) => {
            if let Some(meta) = substitutions.ty.get(&param) {
                Ty::UnificationVar { id: *meta, level }
            } else {
                ty
            }
        }
        Ty::Hole(..) => ty,
        Ty::Rigid(..) => ty,
        Ty::UnificationVar { .. } => ty,
        Ty::Primitive(..) => ty,
        Ty::Constructor {
            type_id,
            params,
            ret,
        } => Ty::Constructor {
            type_id,
            params: params
                .into_iter()
                .map(|p| instantiate_ty(p, substitutions, level))
                .collect(),
            ret: Box::new(instantiate_ty(*ret, substitutions, level)),
        },
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
        Ty::Nominal { id, box row } => Ty::Nominal {
            id,
            row: Box::new(instantiate_row(row, substitutions, level)),
        },
    }
}
