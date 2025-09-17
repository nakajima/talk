use crate::{
    label::Label,
    span::Span,
    types::{constraint::ConstraintCause, row::Row, ty::Ty},
};

#[derive(Debug, Clone)]
pub struct HasField {
    pub row: Row,
    pub label: Label,
    pub ty: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}
