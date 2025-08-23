use std::fmt::{self, Display};

use crate::{
    expr_id::ExprID,
    types::{
        row::{ClosedRow, Label, Row, RowCombination},
        ty::{Primitive, Ty, TypeParameter},
        type_var::TypeVar,
    },
};

#[derive(Clone, Debug, PartialEq, Eq, Hash, derive_visitor::DriveMut, PartialOrd, Ord)]
pub enum ConstraintKind {
    Equals(Ty, Ty),
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
    /// Returns true if the constraint contains any non-canonical type variables
    /// that won't be substituted during instantiation
    pub fn contains_non_canonical_var(&self) -> bool {
        match self {
            ConstraintKind::Equals(lhs, rhs) => {
                lhs.contains_non_canonical_var() || rhs.contains_non_canonical_var()
            }
            ConstraintKind::RowClosed { record } => record.contains_non_canonical_var(),
            ConstraintKind::LiteralPrimitive(ty, ..) => ty.contains_non_canonical_var(),
            ConstraintKind::HasField { record, ty, .. } => {
                record.contains_non_canonical_var() || ty.contains_non_canonical_var()
            }
            ConstraintKind::TyHasField { receiver, ty, .. } => {
                receiver.contains_non_canonical_var() || ty.contains_non_canonical_var()
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
            ConstraintKind::RowClosed { record: row } => match row {
                Row::Open(row) => row.is_canonical(),
                Row::Closed(ClosedRow { values, .. }) => {
                    values.iter().any(|t| t.contains_canonical_var())
                }
            },
            ConstraintKind::LiteralPrimitive(ty, ..) => ty.contains_canonical_var(),
            ConstraintKind::HasField { record, ty, .. } => {
                ty.contains_canonical_var() || record.contains_canonical_var()
            }
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

impl std::fmt::Display for ConstraintKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstraintKind::Equals(ty, ty1) => write!(f, "Equals [{ty}] = [{ty1}]"),
            ConstraintKind::LiteralPrimitive(ty, primitive) => {
                write!(f, "Lit [{ty} :: {primitive:?}]")
            }
            ConstraintKind::RowCombine(expr_id, row_combination) => todo!(),
            ConstraintKind::RowClosed { record } => write!(f, "RowClosed ⟨{record:?}⟩"),
            ConstraintKind::HasField {
                record,
                label,
                ty,
                index,
            } => write!(f, "HasField [{record:?}.{label} : {ty} {index:?}]"),
            ConstraintKind::TyHasField {
                receiver,
                label,
                ty,
                index,
            } => write!(f, "TyHasField [⊤ {receiver}.{label} : {ty} {index:?}]"),
        }
    }
}
