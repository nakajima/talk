use std::fmt::{self, Display};

use crate::{
    expr_id::ExprID,
    types::{
        row::{ClosedRow, Label, Row, RowCombination},
        ty::{Primitive, Ty, TypeParameter},
        type_var::TypeVar,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, derive_visitor::DriveMut, PartialOrd, Ord)]
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
        #[drive(skip)]
        record: Row,
    },
    HasField {
        record: Row,
        #[drive(skip)]
        label: Label,
        ty: Ty,
        #[drive(skip)]
        index: Option<usize>,
    },
    TyHasField {
        receiver: Ty,
        #[drive(skip)]
        label: Label,
        ty: Ty,
        #[drive(skip)]
        index: Option<usize>,
    },
}

impl ConstraintKind {
    pub fn canonical_vars(&self) -> Vec<TypeVar> {
        match self {
            ConstraintKind::Equals(ty, ty1) => {
                let mut result = vec![];
                result.extend(ty.canonical_type_vars());
                result.extend(ty1.canonical_type_vars());
                result
            }
            ConstraintKind::Call {
                callee,
                type_args,
                args,
                returning,
            } => {
                let mut result = vec![];
                result.extend(callee.canonical_type_vars());
                for arg in type_args {
                    result.extend(arg.canonical_type_vars());
                }
                for arg in args {
                    result.extend(arg.canonical_type_vars());
                }
                result.extend(returning.canonical_type_vars());
                result
            }
            ConstraintKind::LiteralPrimitive(ty, _) => ty.canonical_type_vars(),
            ConstraintKind::RowCombine(_, _row_combination) => vec![],
            ConstraintKind::RowClosed { record } => record.canonical_type_vars(),
            ConstraintKind::HasField { record, ty, .. } => {
                let mut result = vec![];
                result.extend(record.canonical_type_vars());
                result.extend(ty.canonical_type_vars());
                result
            }
            ConstraintKind::TyHasField { receiver, ty, .. } => {
                let mut result = vec![];
                result.extend(receiver.canonical_type_vars());
                result.extend(ty.canonical_type_vars());
                result
            }
        }
    }

    pub fn contains_scheme(&self) -> bool {
        match self {
            ConstraintKind::Equals(lhs, rhs) => {
                matches!(lhs, Ty::Scheme(..)) || matches!(rhs, Ty::Scheme(..))
            }
            ConstraintKind::Call {
                callee,
                type_args,
                args,
                returning,
            } => {
                matches!(callee, Ty::Scheme(..))
                    || type_args.iter().any(|a| matches!(a, Ty::Scheme(..)))
                    || args.iter().any(|a| matches!(a, Ty::Scheme(..)))
                    || matches!(returning, Ty::Scheme(..))
            }
            ConstraintKind::RowClosed { record: row } => match row {
                Row::Open(_row) => false,
                Row::Closed(ClosedRow { values, .. }) => {
                    values.iter().any(|t| matches!(t, Ty::Scheme(..)))
                }
            },
            ConstraintKind::LiteralPrimitive(ty, ..) => matches!(ty, Ty::Scheme(..)),
            ConstraintKind::HasField { ty, .. } => matches!(ty, Ty::Scheme(..)),
            ConstraintKind::TyHasField { receiver, ty, .. } => {
                matches!(receiver, Ty::Scheme(..)) || matches!(ty, Ty::Scheme(..))
            }
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => {
                todo!()
            }
        }
    }
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
            ConstraintKind::RowClosed { record: row } => match row {
                Row::Open(row) => false,
                Row::Closed(ClosedRow { values, .. }) => {
                    values.iter().any(|t| t.contains_canonical_var())
                }
            },
            ConstraintKind::LiteralPrimitive(ty, ..) => ty.contains_canonical_var(),
            ConstraintKind::HasField { ty, .. } => ty.contains_canonical_var(),
            ConstraintKind::TyHasField { receiver, ty, .. } => {
                receiver.contains_canonical_var() || ty.contains_canonical_var()
            }
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => {
                todo!()
            }
        }
    }

    #[deprecated]
    pub fn instantiate(
        &self,
        _context: &mut crate::types::type_var_context::TypeVarContext,
        _substitutions: &mut std::collections::BTreeMap<TypeParameter, TypeVar>,
    ) -> ConstraintKind {
        ConstraintKind::LiteralPrimitive(Ty::Void, Primitive::Void)
    }
}

impl Display for ConstraintKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstraintKind::Equals(lhs, rhs) => {
                write!(f, "EQUALS {lhs} = {rhs}")
            }
            ConstraintKind::Call {
                callee,
                type_args,
                args,
                returning,
            } => {
                write!(
                    f,
                    "call {}({})",
                    callee,
                    args.iter()
                        .map(|a| a.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
                if !type_args.is_empty() {
                    write!(
                        f,
                        "<{}>)",
                        type_args
                            .iter()
                            .map(|t| t.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                write!(f, " -> {returning}")
            }
            ConstraintKind::LiteralPrimitive(ty, prim) => {
                write!(f, "LITERAL {ty} : {prim:?}")
            }
            ConstraintKind::RowClosed { record } => {
                write!(f, "row_closed({record:?})")
            }
            ConstraintKind::HasField {
                record,
                label,
                ty,
                index,
            } => {
                write!(f, "{record:?}.{label:?} : {ty}")?;
                if let Some(idx) = index {
                    write!(f, " [idx:{idx}]")?;
                }
                Ok(())
            }
            ConstraintKind::TyHasField {
                receiver,
                label,
                ty,
                index,
            } => {
                write!(f, "{receiver:?}.{label:?} : {ty}")?;
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
