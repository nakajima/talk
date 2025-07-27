use derive_visitor::{Drive, Visitor};

use crate::{
    SymbolID,
    conformance::Conformance,
    parsing::expr_id::ExprID,
    row::RowConstraint,
    substitutions::Substitutions,
    ty::Ty,
    type_checker::Scheme,
    type_var_context::TypeVarContext,
    type_var_id::{TypeVarID, TypeVarKind},
};

#[derive(Visitor)]
#[visitor(Ty(enter))]
struct TypeVarVisitor {
    contains_type_var: bool,
}

impl TypeVarVisitor {
    fn enter_ty(&mut self, ty: &Ty) {
        if self.contains_type_var {
            return;
        }

        self.contains_type_var = matches!(ty, Ty::TypeVar(_))
    }
}

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
        type_args: Vec<Ty>,
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
    /// Row-specific constraint
    Row {
        expr_id: ExprID,
        constraint: RowConstraint,
    },
    Retry(Box<Constraint>, usize),
}

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
            Self::Row { expr_id, .. } => expr_id,
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
            Constraint::InstanceOf { scheme, ty, .. } => f(&scheme.ty()) || f(ty),
            Constraint::ConformsTo {
                ty, conformance, ..
            } => f(ty) || conformance.associated_types.iter().any(f),
            Constraint::Row { constraint, .. } => {
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
                has_canonical_type_var(&scheme.ty()) || has_canonical_type_var(ty)
            }
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
                !scheme.unbound_vars().is_empty() || &scheme.ty() != ty
            }
            _ => true,
        }
    }

    pub fn is_impossible(&self) -> bool {
        match self {
            Constraint::Equality(_, lhs, rhs) => {
                let mut visitor = TypeVarVisitor {
                    contains_type_var: false,
                };

                lhs.drive(&mut visitor);
                rhs.drive(&mut visitor);

                if visitor.contains_type_var {
                    return false;
                }

                lhs != rhs
            }
            _ => false, // TODO
        }
    }

    pub fn replacing(
        &self,
        substitutions: &mut Substitutions,
        context: &mut TypeVarContext,
    ) -> Constraint {
        match self {
            Constraint::Equality(id, ty, ty1) => Constraint::Equality(
                *id,
                substitutions.apply(ty, 0, context),
                substitutions.apply(ty1, 0, context),
            ),
            Constraint::MemberAccess(id, ty, name, ty1) => Constraint::MemberAccess(
                *id,
                substitutions.apply(ty, 0, context),
                name.clone(),
                substitutions.apply(ty1, 0, context),
            ),
            Constraint::UnqualifiedMember(id, name, ty) => Constraint::UnqualifiedMember(
                *id,
                name.clone(),
                substitutions.apply(ty, 0, context),
            ),
            Constraint::InitializerCall {
                expr_id,
                initializes_id,
                args,
                func_ty,
                result_ty,
                type_args,
            } => Constraint::InitializerCall {
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
            Constraint::VariantMatch {
                expr_id,
                scrutinee_ty,
                variant_name,
                field_tys,
            } => Constraint::VariantMatch {
                expr_id: *expr_id,
                scrutinee_ty: substitutions.apply(scrutinee_ty, 0, context),
                variant_name: variant_name.clone(),
                field_tys: field_tys
                    .iter()
                    .map(|ty| substitutions.apply(ty, 0, context))
                    .collect(),
            },
            Constraint::InstanceOf {
                expr_id,
                ty,
                symbol_id,
                scheme,
            } => Constraint::InstanceOf {
                expr_id: *expr_id,
                ty: substitutions.apply(ty, 0, context),
                symbol_id: *symbol_id,
                scheme: Scheme::new(
                    substitutions.apply(&scheme.ty(), 0, context),
                    scheme.unbound_vars().clone(),
                    scheme.constraints().clone(),
                ),
            },
            Constraint::ConformsTo {
                expr_id,
                ty,
                conformance,
            } => Constraint::ConformsTo {
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
            Constraint::Retry(c, retries) => {
                Constraint::Retry(c.replacing(substitutions, context).clone().into(), *retries)
            }
            Constraint::Row {
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
                Constraint::Row {
                    expr_id: *expr_id,
                    constraint: new_constraint,
                }
            }
        }
    }
}

fn has_canonical_type_var(ty: &Ty) -> bool {
    if matches!(
        ty,
        Ty::TypeVar(TypeVarID {
            kind: TypeVarKind::CanonicalTypeParameter(_),
            ..
        })
    ) {
        return true;
    }

    false
}
