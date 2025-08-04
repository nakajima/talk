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
    Hoisted,
    Variable,
    Call,
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
            ConstraintKind::RowCombine(..) => {
                todo!()
            }
        }
    }

    pub fn priority(&self) -> usize {
        0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintKind {
    Equals(Ty, Ty),
    Call {
        callee: Ty,
        type_args: Vec<Ty>,
        args: Vec<Ty>,
        returning: Ty,
    },
    LiteralPrimitive(Ty, Primitive),
    RowCombine(ExprID, RowCombination),
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
            ConstraintKind::LiteralPrimitive(ty, ..) => ty.contains_canonical_var(),
            ConstraintKind::RowCombine(..) => todo!(),
        }
    }
}
