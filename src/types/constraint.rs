use crate::{
    expr_id::ExprID,
    types::{
        row::RowCombination,
        ty::{Primitive, Ty},
        type_var::TypeVar,
    },
};

#[derive(Debug, Clone)]
pub enum ConstraintState {
    Pending,
    Waiting,
    Success,
    Error,
}

#[derive(Debug, Clone)]
pub enum ConstraintCauseKind {
    Annotation(ExprID),
}

#[derive(Debug, Clone)]
pub struct ConstraintCause {
    pub kind: ConstraintCauseKind,
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub expr_id: ExprID,
    pub cause: ConstraintCause,
    pub kind: ConstraintKind,
    pub parent: Option<Box<Self>>,
    pub state: ConstraintState,
}

impl Constraint {
    pub fn type_vars(&self) -> Vec<TypeVar> {
        match &self.kind {
            ConstraintKind::PrimitiveLiteral(_, ty, _) => ty.type_vars(),
            ConstraintKind::RowCombine(..) => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ConstraintKind {
    PrimitiveLiteral(ExprID, Ty, Primitive),
    RowCombine(ExprID, RowCombination),
}
