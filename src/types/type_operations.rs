use tracing::instrument;

use crate::types::{passes::inference_pass::Substitutions, ty::Ty, type_error::TypeError};

#[instrument]
pub(super) fn unify(
    lhs: &Ty,
    rhs: &Ty,
    substitutions: &mut Substitutions,
) -> Result<bool, TypeError> {
    let lhs = apply(lhs.clone(), substitutions);
    let rhs = apply(rhs.clone(), substitutions);

    // Hole(NodeID),
    // Rigid(DeclId),
    // MetaVar { id: MetaId, level: Level },
    // Primitive(Primitive),
    // TypeConstructor { name: Name, kind: TypeDefKind },
    // TypeApplication(Box<Ty>, Box<Ty>),
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

            substitutions.insert(
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
            substitutions.insert(*id, ty.clone());
            Ok(true)
        }
        (_, Ty::Rigid(_)) | (Ty::Rigid(_), _) => Err(TypeError::InvalidUnification(lhs, rhs)),
        _ => todo!("lhs: {lhs:?} {rhs:?}"),
    }
}

#[instrument(ret)]
pub(super) fn apply(ty: Ty, substitutions: &Substitutions) -> Ty {
    match ty {
        Ty::Hole(..) => ty,
        Ty::Rigid(..) => ty,
        Ty::MetaVar { id, .. } => match substitutions.get(&id) {
            Some(found @ Ty::MetaVar { id: found_id, .. }) => {
                if *found_id == id {
                    ty
                } else {
                    apply(found.clone(), substitutions)
                }
            }
            Some(found) => found.clone(),
            None => ty,
        },
        Ty::Primitive(..) => ty,
        Ty::TypeConstructor { .. } => todo!(),
        Ty::Func(params, ret) => Ty::Func(
            Box::new(apply(*params, substitutions)),
            Box::new(apply(*ret, substitutions)),
        ),
        Ty::Tuple(items) => Ty::Tuple(items.into_iter().map(|t| apply(t, substitutions)).collect()),
        Ty::TypeApplication(box lhs, box rhs) => Ty::TypeApplication(
            apply(lhs, substitutions).into(),
            apply(rhs, substitutions).into(),
        ),
    }
}
