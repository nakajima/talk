use std::hash::Hash;

use crate::{
    expr_id::ExprID,
    type_checker::TypeError,
    types::{
        constraint_set::ConstraintId,
        row::RowCombination,
        ty::{Primitive, Ty},
        type_var::TypeVar,
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintState {
    Pending,
    Waiting,
    Solved,
    Error(TypeError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintCause {
    Annotation(ExprID),
    Assignment(ExprID),
    FuncReturn(ExprID),
    PrimitiveLiteral(ExprID, Primitive),
    RecordLiteral,
    Hoisted,
    Variable,
    Call,
    MemberAccess,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    pub id: ConstraintId,
    pub expr_id: ExprID,
    pub cause: ConstraintCause,
    pub kind: ConstraintKind,
    pub parent: Option<ConstraintId>,
    pub children: Vec<ConstraintId>,
    pub state: ConstraintState,
}

impl Hash for Constraint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Constraint {
    pub fn type_vars(&self) -> Vec<TypeVar> {
        match &self.kind {
            ConstraintKind::Equals(lhs, rhs) => {
                [lhs, rhs].iter().flat_map(|t| t.type_vars()).collect()
            }
            ConstraintKind::LiteralPrimitive(ty, _) => ty.type_vars(),
            ConstraintKind::Call {
                callee,
                args,
                returning,
                type_args,
            } => {
                let mut res = vec![];
                res.extend(callee.type_vars());
                res.extend(args.iter().flat_map(|t| t.type_vars()));
                res.extend(type_args.iter().flat_map(|t| t.type_vars()));
                res.extend(returning.type_vars());
                res
            }
            #[allow(clippy::todo)]
            ConstraintKind::HasField { ty, .. } => {
                let mut res = vec![];
                res.extend(ty.type_vars());
                res
            }
            ConstraintKind::RowClosed { record } => record.type_vars(),
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => {
                todo!()
            }
        }
    }

    pub fn priority(&self) -> usize {
        0
    }

    pub fn is_solved(&self) -> bool {
        self.state == ConstraintState::Solved
    }
}

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
        #[drive(skip)] label: String,
        ty: Ty,
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
            ConstraintKind::HasField { record, ty, .. } => record.contains_canonical_var() || ty.contains_canonical_var(),
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
                type_args: type_args.iter().map(|t| t.instantiate(context, substitutions)).collect(),
                args: args.iter().map(|t| t.instantiate(context, substitutions)).collect(),
                returning: returning.instantiate(context, substitutions),
            },
            ConstraintKind::LiteralPrimitive(ty, prim) => ConstraintKind::LiteralPrimitive(
                ty.instantiate(context, substitutions),
                *prim,
            ),
            ConstraintKind::RowClosed { record } => ConstraintKind::RowClosed {
                record: record.instantiate(context, substitutions),
            },
            ConstraintKind::HasField { record, label, ty } => ConstraintKind::HasField {
                record: record.instantiate(context, substitutions),
                label: label.clone(),
                ty: ty.instantiate(context, substitutions),
            },
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => todo!(),
        }
    }
}
