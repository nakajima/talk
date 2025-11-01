use crate::{
    span::Span,
    types::{constraints::constraint::ConstraintCause, infer_ty::InferTy},
};

#[derive(Debug, Clone, PartialEq)]
pub struct Equals {
    pub lhs: InferTy,
    pub rhs: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}
