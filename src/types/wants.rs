use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    span::Span,
    types::{
        constraint::{Constraint, ConstraintCause},
        constraints::{
            call::Call, construction::Construction, equals::Equals, has_field::HasField,
            member::Member,
        },
        row::Row,
        ty::Ty,
    },
};

#[derive(Debug, Default)]
pub struct Wants(pub Vec<Constraint>);
impl Wants {
    pub fn iter(&self) -> std::slice::Iter<'_, Constraint> {
        self.0.iter()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn drain(&mut self) -> std::vec::Drain<'_, Constraint> {
        self.0.drain(..)
    }

    pub fn push(&mut self, constraint: Constraint) {
        tracing::debug!("constraining {constraint:?}");
        self.0.push(constraint)
    }

    pub fn construction(
        &mut self,
        callee: Ty,
        args: Vec<Ty>,
        returns: Ty,
        type_symbol: Symbol,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining constructor {callee:?}({args:?}) = {type_symbol:?}");
        self.0.push(Constraint::Construction(Construction {
            callee,
            args,
            returns,
            type_symbol,
            cause,
            span,
        }))
    }

    pub fn call(
        &mut self,
        callee: Ty,
        args: Vec<Ty>,
        returns: Ty,
        receiver: Option<Ty>,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining call {callee:?}({args:?}) = {returns:?}");
        self.0.push(Constraint::Call(Call {
            callee,
            args,
            returns,
            receiver,
            cause,
            span,
        }))
    }

    pub fn equals(&mut self, lhs: Ty, rhs: Ty, cause: ConstraintCause, span: Span) {
        tracing::debug!("constraining equals {lhs:?} = {rhs:?}");
        self.0.push(Constraint::Equals(Equals {
            lhs,
            rhs,
            cause,
            span,
        }));
    }

    pub fn member(
        &mut self,
        receiver: Ty,
        label: Label,
        ty: Ty,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining member {receiver:?}.{label:?} <> {ty:?}");
        self.0.push(Constraint::Member(Member {
            receiver,
            label,
            ty,
            cause,
            span,
        }))
    }

    pub fn _has_field(
        &mut self,
        row: Row,
        label: Label,
        ty: Ty,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining has_field {row:?}.{label:?} <> {ty:?}");
        self.0.push(Constraint::HasField(HasField {
            row,
            label,
            ty,
            cause,
            span,
        }))
    }
}
