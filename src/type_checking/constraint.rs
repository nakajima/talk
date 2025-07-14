use crate::{
    SymbolID,
    parser::ExprID,
    substitutions::Substitutions,
    ty::Ty,
    type_checker::Scheme,
    type_defs::protocol_def::Conformance,
    type_var_context::TypeVarContext,
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
        protocol_ty: Ty,
        ty: Ty,
        conformance: Conformance,
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
