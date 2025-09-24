use crate::{
    span::Span,
    types::{constraints::constraint::ConstraintCause, ty::Ty},
};

#[derive(Debug, Clone)]
pub struct Equals {
    pub lhs: Ty,
    pub rhs: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}
