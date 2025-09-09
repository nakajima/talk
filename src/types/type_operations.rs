use rustc_hash::FxHashMap;
use tracing::{Level, instrument};

use crate::types::{
    passes::inference_pass::Substitutions,
    row::Row,
    ty::{MetaId, Ty},
    type_error::TypeError,
};

fn occurs_in_row(id: MetaId, row: &Row) -> bool {
    match row {
        Row::Empty => false,
        Row::Var(_) => false,
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
#[instrument(level = Level::DEBUG)]
fn unify_rows(lhs: &Row, rhs: &Row, substitutions: &mut Substitutions) -> Result<bool, TypeError> {
    match (lhs, rhs) {
        (Row::Empty, Row::Empty) => Ok(false),
        (Row::Var(lhs_id), Row::Var(rhs_id)) if lhs_id == rhs_id => Ok(false),
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
#[instrument(level = Level::DEBUG)]
pub(super) fn unify(
    lhs: &Ty,
    rhs: &Ty,
    substitutions: &mut Substitutions,
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
                level: lhs_level,
            },
            Ty::MetaVar {
                id: rhs_id,
                level: rhs_level,
            },
        ) => {
            let picked = itertools::max([lhs_id, rhs_id]).unwrap();
            let not_picked = itertools::min([lhs_id, rhs_id]).unwrap();

            substitutions.ty.insert(
                *not_picked,
                Ty::MetaVar {
                    id: *picked,
                    level: if picked == lhs_id {
                        *lhs_level
                    } else {
                        *rhs_level
                    },
                },
            );

            Ok(true)
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
        Row::Empty => row.clone(),
        Row::Var(..) => row.clone(),
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

#[instrument(level = Level::TRACE, ret)]
pub(super) fn apply_row(row: Row, substitutions: &Substitutions) -> Row {
    match row {
        Row::Empty => Row::Empty,
        Row::Var(var) => substitutions.row.get(&var).unwrap_or(&row).clone(),
        Row::Extend { row, label, ty } => Row::Extend {
            row: Box::new(apply_row(*row, substitutions)),
            label,
            ty: apply(ty, substitutions),
        },
    }
}

#[instrument(level = Level::TRACE, ret)]
pub(super) fn apply(ty: Ty, substitutions: &Substitutions) -> Ty {
    match ty {
        Ty::Param(..) => ty,
        Ty::Hole(..) => ty,
        Ty::Rigid(..) => ty,
        Ty::MetaVar { id, .. } => match substitutions.ty.get(&id) {
            Some(found @ Ty::MetaVar { id: found_id, .. }) => {
                if *found_id == id {
                    ty
                } else {
                    apply(found.clone(), substitutions)
                }
            }
            Some(found) => {
                // Recursively apply substitutions to handle transitive substitutions
                match found {
                    // Don't recurse on primitives or other simple types
                    Ty::Primitive(_) | Ty::Param(_) | Ty::Rigid(_) | Ty::Hole(_) => found.clone(),
                    // For complex types, recursively apply
                    _ => apply(found.clone(), substitutions),
                }
            }
            None => ty,
        },
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
