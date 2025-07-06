use std::collections::HashMap;

use ena::unify::InPlaceUnificationTable;

use crate::{
    SymbolID,
    constraint_solver::ConstraintSolver,
    parser::ExprID,
    ty::Ty,
    type_checker::Scheme,
    type_constraint::TypeConstraint,
    type_defs::protocol_def::Conformance,
    type_var_id::{TypeVarID, TypeVarKind},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    Equality(ExprID, Ty, Ty),
    MemberAccess(ExprID, Ty, String, Ty), // receiver_ty, member_name, result_ty
    UnqualifiedMember(ExprID, String, Ty), // member name, expected type
    InitializerCall {
        expr_id: ExprID,
        initializes_id: SymbolID,
        args: Vec<Ty>,
        func_ty: Ty,
        result_ty: Ty,
    },
    VariantMatch {
        expr_id: ExprID,
        scrutinee_ty: Ty, // The type of the value being matched (the `expected` type)
        variant_name: String,
        // The list of fresh TypeVars created for each field in the pattern.
        field_tys: Vec<Ty>,
    },
    InstanceOf {
        scheme: Scheme,
        expr_id: ExprID,
        ty: Ty,
        symbol_id: SymbolID,
    },
    ConformsTo {
        expr_id: ExprID,
        ty: Ty,
        conformance: Conformance,
    },
    Satisfies {
        expr_id: ExprID,
        ty: Ty,
        constraints: Vec<TypeConstraint>,
    },
    Retry(Box<Constraint>, usize),
}

pub type Substitutions = HashMap<TypeVarID, Ty>;

impl Constraint {
    pub fn expr_id(&self) -> &ExprID {
        match self {
            Self::Equality(id, _, _) => id,
            Self::MemberAccess(id, _, _, _) => id,
            Self::UnqualifiedMember(id, _, _) => id,
            Self::InitializerCall { expr_id, .. } => expr_id,
            Self::VariantMatch { expr_id, .. } => expr_id,
            Self::InstanceOf { expr_id, .. } => expr_id,
            Self::ConformsTo { expr_id, .. } => expr_id,
            Self::Satisfies { expr_id, .. } => expr_id,
            Self::Retry(c, _) => c.expr_id(),
        }
    }

    pub fn contains_ty(&self, ty: &Ty) -> bool {
        self.contains(|t| t == ty)
    }

    pub fn contains<F: Fn(&Ty) -> bool>(&self, f: F) -> bool {
        match self {
            Constraint::Equality(_, ty, ty1) => f(ty) || f(ty1),
            Constraint::MemberAccess(_, ty, _, ty1) => f(ty) || f(ty1),
            Constraint::UnqualifiedMember(_, _, ty) => f(ty),
            Constraint::InitializerCall {
                args,
                func_ty,
                result_ty,
                ..
            } => args.iter().any(&f) || f(func_ty) || f(result_ty),
            Constraint::VariantMatch {
                scrutinee_ty,
                field_tys,
                ..
            } => f(scrutinee_ty) || field_tys.iter().any(f),
            Constraint::InstanceOf { scheme, ty, .. } => f(&scheme.ty) || f(ty),
            Constraint::Satisfies { ty, .. } => f(ty),
            Constraint::ConformsTo {
                ty, conformance, ..
            } => f(ty) || conformance.associated_types.iter().any(f),
            _ => false,
        }
    }

    pub fn contains_canonical_type_parameter(&self) -> bool {
        match self {
            Constraint::Equality(_, ty, ty1) => {
                has_canonical_type_var(ty) || has_canonical_type_var(ty1)
            }
            Constraint::MemberAccess(_, ty, _, ty1) => {
                has_canonical_type_var(ty) || has_canonical_type_var(ty1)
            }
            Constraint::UnqualifiedMember(_, _, ty) => has_canonical_type_var(ty),
            Constraint::InitializerCall {
                args,
                func_ty,
                result_ty,
                ..
            } => {
                args.iter().any(has_canonical_type_var)
                    || has_canonical_type_var(func_ty)
                    || has_canonical_type_var(result_ty)
            }
            Constraint::VariantMatch {
                scrutinee_ty,
                field_tys,
                ..
            } => {
                has_canonical_type_var(scrutinee_ty) || field_tys.iter().any(has_canonical_type_var)
            }
            Constraint::InstanceOf { scheme, ty, .. } => {
                has_canonical_type_var(&scheme.ty) || has_canonical_type_var(ty)
            }
            Constraint::Satisfies { ty, .. } => has_canonical_type_var(ty),
            Constraint::ConformsTo { conformance, .. } => conformance
                .associated_types
                .iter()
                .any(has_canonical_type_var),
            _ => false,
        }
    }

    pub fn needs_solving(&self) -> bool {
        match self {
            Constraint::Equality(_, ty, ty1) => ty != ty1,
            Constraint::InstanceOf { scheme, ty, .. } => {
                !scheme.unbound_vars.is_empty() || &scheme.ty != ty
            }
            _ => true,
        }
    }

    pub fn replacing(&self, substitutions: &InPlaceUnificationTable<TypeVarID>) -> Constraint {
        match self {
            Constraint::Equality(id, ty, ty1) => Constraint::Equality(
                *id,
                ConstraintSolver::apply(ty, substitutions, 0),
                ConstraintSolver::apply(ty1, substitutions, 0),
            ),
            Constraint::MemberAccess(id, ty, name, ty1) => Constraint::MemberAccess(
                *id,
                ConstraintSolver::apply(ty, substitutions, 0),
                name.clone(),
                ConstraintSolver::apply(ty1, substitutions, 0),
            ),
            Constraint::UnqualifiedMember(id, name, ty) => Constraint::UnqualifiedMember(
                *id,
                name.clone(),
                ConstraintSolver::apply(ty, substitutions, 0),
            ),
            Constraint::InitializerCall {
                expr_id,
                initializes_id,
                args,
                func_ty,
                result_ty,
            } => Constraint::InitializerCall {
                expr_id: *expr_id,
                initializes_id: *initializes_id,
                args: args
                    .iter()
                    .map(|a| ConstraintSolver::apply(a, substitutions, 0))
                    .collect(),
                func_ty: ConstraintSolver::apply(func_ty, substitutions, 0),
                result_ty: ConstraintSolver::apply(result_ty, substitutions, 0),
            },
            Constraint::VariantMatch {
                expr_id,
                scrutinee_ty,
                variant_name,
                field_tys,
            } => Constraint::VariantMatch {
                expr_id: *expr_id,
                scrutinee_ty: ConstraintSolver::apply(scrutinee_ty, substitutions, 0),
                variant_name: variant_name.clone(),
                field_tys: field_tys
                    .iter()
                    .map(|ty| ConstraintSolver::apply(ty, substitutions, 0))
                    .collect(),
            },
            Constraint::InstanceOf {
                expr_id,
                ty,
                symbol_id,
                scheme,
            } => Constraint::InstanceOf {
                expr_id: *expr_id,
                ty: ConstraintSolver::apply(ty, substitutions, 0),
                symbol_id: *symbol_id,
                scheme: Scheme {
                    ty: ConstraintSolver::apply(&scheme.ty, substitutions, 0),
                    unbound_vars: scheme.unbound_vars.clone(),
                },
            },
            Constraint::ConformsTo {
                expr_id,
                ty,
                conformance,
            } => Constraint::ConformsTo {
                expr_id: *expr_id,
                ty: ConstraintSolver::apply(ty, substitutions, 0),
                conformance: Conformance {
                    protocol_id: conformance.protocol_id,
                    associated_types: conformance
                        .associated_types
                        .iter()
                        .map(|t| ConstraintSolver::apply(t, substitutions, 0))
                        .collect(),
                },
            },
            Constraint::Satisfies {
                expr_id,
                ty,
                constraints,
            } => Constraint::Satisfies {
                expr_id: *expr_id,
                ty: ConstraintSolver::apply(ty, substitutions, 0),
                constraints: constraints.clone(),
            },
            Constraint::Retry(c, retries) => {
                Constraint::Retry(c.replacing(substitutions).clone().into(), *retries)
            }
        }
    }
}

fn has_canonical_type_var(ty: &Ty) -> bool {
    if matches!(ty, Ty::CanonicalTypeVar(_, _)) {
        return true;
    }

    false
}
