use std::fmt::{self, Display};

use crate::{
    expr_id::ExprID,
    types::{
        row::{Label, RowCombination},
        ty::{Primitive, Ty},
        type_var::TypeVar,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, derive_visitor::DriveMut)]
pub enum ConstraintKind {
    Equals(Ty, Ty),
    Call {
        callee: Ty,
        type_args: Vec<Ty>,
        args: Vec<Ty>,
        returning: Ty,
    },
    LiteralPrimitive(Ty, #[drive(skip)] Primitive),
    RowCombine(#[drive(skip)] ExprID, #[drive(skip)] RowCombination),
    RowClosed {
        record: Ty,
    },
    HasField {
        record: Ty,
        #[drive(skip)]
        label: Label,
        ty: Ty,
        #[drive(skip)]
        index: Option<usize>,
    },
}

impl ConstraintKind {
    pub fn contains_canonical_var(&self) -> bool {
        match self {
            ConstraintKind::Equals(lhs, rhs) => {
                lhs.contains_canonical_var() || rhs.contains_canonical_var()
            }
            ConstraintKind::Call {
                callee,
                type_args,
                args,
                returning,
            } => {
                callee.contains_canonical_var()
                    || type_args.iter().any(|a| a.contains_canonical_var())
                    || args.iter().any(|a| a.contains_canonical_var())
                    || returning.contains_canonical_var()
            }
            ConstraintKind::RowClosed { record } => record.contains_canonical_var(),
            ConstraintKind::LiteralPrimitive(ty, ..) => ty.contains_canonical_var(),
            ConstraintKind::HasField { record, ty, .. } => {
                record.contains_canonical_var() || ty.contains_canonical_var()
            }
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => {
                todo!()
            }
        }
    }

    pub fn instantiate(
        &self,
        context: &mut crate::types::type_var_context::TypeVarContext,
        substitutions: &mut std::collections::BTreeMap<TypeVar, TypeVar>,
    ) -> ConstraintKind {
        match self {
            ConstraintKind::Equals(lhs, rhs) => ConstraintKind::Equals(
                lhs.instantiate(context, substitutions),
                rhs.instantiate(context, substitutions),
            ),
            ConstraintKind::Call {
                callee,
                type_args,
                args,
                returning,
            } => ConstraintKind::Call {
                callee: callee.instantiate(context, substitutions),
                type_args: type_args
                    .iter()
                    .map(|t| t.instantiate(context, substitutions))
                    .collect(),
                args: args
                    .iter()
                    .map(|t| t.instantiate(context, substitutions))
                    .collect(),
                returning: returning.instantiate(context, substitutions),
            },
            ConstraintKind::LiteralPrimitive(ty, prim) => {
                ConstraintKind::LiteralPrimitive(ty.instantiate(context, substitutions), *prim)
            }
            ConstraintKind::RowClosed { record } => ConstraintKind::RowClosed {
                record: record.instantiate(context, substitutions),
            },
            ConstraintKind::HasField {
                record,
                label,
                ty,
                index,
            } => ConstraintKind::HasField {
                record: record.instantiate(context, substitutions),
                label: label.clone(),
                ty: ty.instantiate(context, substitutions),
                index: *index,
            },
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => todo!(),
        }
    }
}

impl Display for ConstraintKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstraintKind::Equals(lhs, rhs) => {
                write!(f, "{lhs} = {rhs}")
            }
            ConstraintKind::Call {
                callee,
                type_args,
                args,
                returning,
            } => {
                write!(f, "call {}({})", callee, args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", "))?;
                if !type_args.is_empty() {
                    write!(f, "<{}>)", type_args.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(", "))?;
                }
                write!(f, " -> {returning}")
            }
            ConstraintKind::LiteralPrimitive(ty, prim) => {
                write!(f, "{ty} : {prim:?}")
            }
            ConstraintKind::RowClosed { record } => {
                write!(f, "row_closed({record})")
            }
            ConstraintKind::HasField {
                record,
                label,
                ty,
                index,
            } => {
                write!(f, "{record}.{label:?} : {ty}")?;
                if let Some(idx) = index {
                    write!(f, " [idx:{idx}]")?;
                }
                Ok(())
            }
            ConstraintKind::RowCombine(id, combination) => {
                write!(f, "row_combine({id}, {combination:?})")
            }
        }
    }
}
