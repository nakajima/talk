use derive_visitor::{Drive, Visitor};

use crate::{
    SymbolID,
    conformance::Conformance,
    parsing::expr_id::ExprID,
    row::RowConstraint,
    substitutions::Substitutions,
    ty::Ty2,
    type_checker::Scheme,
    type_var_context::TypeVarContext2,
    type_var_id::{TypeVarID, TypeVarKind},
};

#[derive(Visitor)]
#[visitor(Ty2(enter))]
struct TypeVarVisitor {
    contains_type_var: bool,
}

impl TypeVarVisitor {
    fn enter_ty_2(&mut self, ty: &Ty2) {
        if self.contains_type_var {
            return;
        }

        self.contains_type_var = matches!(ty, Ty2::TypeVar(_))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint2 {
    Equality(ExprID, Ty2, Ty2),
    MemberAccess(ExprID, Ty2, String, Ty2), // receiver_ty, member_name, result_ty
    UnqualifiedMember(ExprID, String, Ty2), // member name, expected type
    InitializerCall {
        expr_id: ExprID,
        initializes_id: SymbolID,
        args: Vec<Ty2>,
        func_ty: Ty2,
        result_ty: Ty2,
        type_args: Vec<Ty2>,
    },
    VariantMatch {
        expr_id: ExprID,
        scrutinee_ty: Ty2, // The type of the value being matched (the `expected` type)
        variant_name: String,
        // The list of fresh TypeVars created for each field in the pattern.
        field_tys: Vec<Ty2>,
    },
    InstanceOf {
        scheme: Scheme,
        expr_id: ExprID,
        ty: Ty2,
        symbol_id: SymbolID,
    },
    ConformsTo {
        expr_id: ExprID,
        ty: Ty2,
        conformance: Conformance,
    },
    /// Row-specific constraint
    Row {
        expr_id: ExprID,
        constraint: RowConstraint,
    },
    Retry(Box<Constraint2>, usize),
}

impl Constraint2 {
    pub fn expr_id(&self) -> &ExprID {
        match self {
            Self::Equality(id, _, _) => id,
            Self::MemberAccess(id, _, _, _) => id,
            Self::UnqualifiedMember(id, _, _) => id,
            Self::InitializerCall { expr_id, .. } => expr_id,
            Self::VariantMatch { expr_id, .. } => expr_id,
            Self::InstanceOf { expr_id, .. } => expr_id,
            Self::ConformsTo { expr_id, .. } => expr_id,
            Self::Row { expr_id, .. } => expr_id,
            Self::Retry(c, _) => c.expr_id(),
        }
    }

    pub fn contains_ty(&self, ty: &Ty2) -> bool {
        self.contains(|t| t == ty)
    }

    pub fn contains<F: Fn(&Ty2) -> bool>(&self, f: F) -> bool {
        match self {
            Constraint2::Equality(_, ty, ty1) => f(ty) || f(ty1),
            Constraint2::MemberAccess(_, ty, _, ty1) => f(ty) || f(ty1),
            Constraint2::UnqualifiedMember(_, _, ty) => f(ty),
            Constraint2::InitializerCall {
                args,
                func_ty,
                result_ty,
                ..
            } => args.iter().any(&f) || f(func_ty) || f(result_ty),
            Constraint2::VariantMatch {
                scrutinee_ty,
                field_tys,
                ..
            } => f(scrutinee_ty) || field_tys.iter().any(f),
            Constraint2::InstanceOf { scheme, ty, .. } => f(&scheme.ty()) || f(ty),
            Constraint2::ConformsTo {
                ty, conformance, ..
            } => f(ty) || conformance.associated_types.iter().any(f),
            Constraint2::Row { constraint, .. } => {
                use crate::row::RowConstraint;
                match constraint {
                    RowConstraint::HasField { field_ty, .. } => f(field_ty),
                    RowConstraint::HasRow { row, .. } => {
                        row.fields.values().any(|field| f(&field.ty))
                    }
                    RowConstraint::HasExactRow { row, .. } => {
                        row.fields.values().any(|field| f(&field.ty))
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    pub fn contains_canonical_type_parameter(&self) -> bool {
        match self {
            Constraint2::Equality(_, ty, ty1) => {
                has_canonical_type_var(ty) || has_canonical_type_var(ty1)
            }
            Constraint2::MemberAccess(_, ty, _, ty1) => {
                has_canonical_type_var(ty) || has_canonical_type_var(ty1)
            }
            Constraint2::UnqualifiedMember(_, _, ty) => has_canonical_type_var(ty),
            Constraint2::InitializerCall {
                args,
                func_ty,
                result_ty,
                ..
            } => {
                args.iter().any(has_canonical_type_var)
                    || has_canonical_type_var(func_ty)
                    || has_canonical_type_var(result_ty)
            }
            Constraint2::VariantMatch {
                scrutinee_ty,
                field_tys,
                ..
            } => {
                has_canonical_type_var(scrutinee_ty) || field_tys.iter().any(has_canonical_type_var)
            }
            Constraint2::InstanceOf { scheme, ty, .. } => {
                has_canonical_type_var(&scheme.ty()) || has_canonical_type_var(ty)
            }
            Constraint2::ConformsTo { conformance, .. } => conformance
                .associated_types
                .iter()
                .any(has_canonical_type_var),
            _ => false,
        }
    }

    pub fn needs_solving(&self) -> bool {
        match self {
            Constraint2::Equality(_, ty, ty1) => ty != ty1,
            Constraint2::InstanceOf { scheme, ty, .. } => {
                !scheme.unbound_vars().is_empty() || &scheme.ty() != ty
            }
            _ => true,
        }
    }

    pub fn is_impossible(&self) -> bool {
        match self {
            Constraint2::Equality(_, lhs, rhs) => {
                let mut visitor = TypeVarVisitor {
                    contains_type_var: false,
                };

                lhs.drive(&mut visitor);
                rhs.drive(&mut visitor);

                if visitor.contains_type_var {
                    return false;
                }

                lhs.equal_to(rhs)
            }
            _ => false, // TODO
        }
    }

    pub fn replacing(
        &self,
        substitutions: &mut Substitutions,
        context: &mut TypeVarContext2,
    ) -> Constraint2 {
        match self {
            Constraint2::Equality(id, ty, ty1) => Constraint2::Equality(
                *id,
                substitutions.apply(ty, 0, context),
                substitutions.apply(ty1, 0, context),
            ),
            Constraint2::MemberAccess(id, ty, name, ty1) => Constraint2::MemberAccess(
                *id,
                substitutions.apply(ty, 0, context),
                name.clone(),
                substitutions.apply(ty1, 0, context),
            ),
            Constraint2::UnqualifiedMember(id, name, ty) => Constraint2::UnqualifiedMember(
                *id,
                name.clone(),
                substitutions.apply(ty, 0, context),
            ),
            Constraint2::InitializerCall {
                expr_id,
                initializes_id,
                args,
                func_ty,
                result_ty,
                type_args,
            } => Constraint2::InitializerCall {
                expr_id: *expr_id,
                initializes_id: *initializes_id,
                args: args
                    .iter()
                    .map(|a| substitutions.apply(a, 0, context))
                    .collect(),
                func_ty: substitutions.apply(func_ty, 0, context),
                result_ty: substitutions.apply(result_ty, 0, context),
                type_args: substitutions.apply_multiple(type_args, 0, context),
            },
            Constraint2::VariantMatch {
                expr_id,
                scrutinee_ty,
                variant_name,
                field_tys,
            } => Constraint2::VariantMatch {
                expr_id: *expr_id,
                scrutinee_ty: substitutions.apply(scrutinee_ty, 0, context),
                variant_name: variant_name.clone(),
                field_tys: field_tys
                    .iter()
                    .map(|ty| substitutions.apply(ty, 0, context))
                    .collect(),
            },
            Constraint2::InstanceOf {
                expr_id,
                ty,
                symbol_id,
                scheme,
            } => Constraint2::InstanceOf {
                expr_id: *expr_id,
                ty: substitutions.apply(ty, 0, context),
                symbol_id: *symbol_id,
                scheme: Scheme::new(
                    substitutions.apply(&scheme.ty(), 0, context),
                    scheme.unbound_vars().clone(),
                    scheme.constraints().clone(),
                ),
            },
            Constraint2::ConformsTo {
                expr_id,
                ty,
                conformance,
            } => Constraint2::ConformsTo {
                expr_id: *expr_id,
                ty: substitutions.apply(ty, 0, context),
                conformance: Conformance {
                    protocol_id: conformance.protocol_id,
                    associated_types: conformance
                        .associated_types
                        .iter()
                        .map(|t| substitutions.apply(t, 0, context))
                        .collect(),
                },
            },
            Constraint2::Retry(c, retries) => {
                Constraint2::Retry(c.replacing(substitutions, context).clone().into(), *retries)
            }
            Constraint2::Row {
                expr_id,
                constraint,
            } => {
                use crate::row::RowConstraint;
                // Apply substitutions to types within row constraints
                let new_constraint = match constraint {
                    RowConstraint::HasField {
                        type_var,
                        label,
                        field_ty,
                        metadata,
                    } => RowConstraint::HasField {
                        type_var: type_var.clone(),
                        label: label.clone(),
                        field_ty: substitutions.apply(field_ty, 0, context),
                        metadata: metadata.clone(),
                    },
                    RowConstraint::HasRow {
                        type_var,
                        row,
                        extension,
                    } => {
                        let new_row = row.substitute(substitutions);
                        RowConstraint::HasRow {
                            type_var: type_var.clone(),
                            row: new_row,
                            extension: extension.clone(),
                        }
                    }
                    RowConstraint::HasExactRow { type_var, row } => {
                        let new_row = row.substitute(substitutions);
                        RowConstraint::HasExactRow {
                            type_var: type_var.clone(),
                            row: new_row,
                        }
                    }
                    other => other.clone(),
                };
                Constraint2::Row {
                    expr_id: *expr_id,
                    constraint: new_constraint,
                }
            }
        }
    }
}

fn has_canonical_type_var(ty: &Ty2) -> bool {
    if matches!(
        ty,
        Ty2::TypeVar(TypeVarID {
            kind: TypeVarKind::CanonicalTypeParameter(_),
            ..
        })
    ) {
        return true;
    }

    false
}
