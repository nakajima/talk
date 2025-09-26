use std::collections::VecDeque;

use crate::{
    label::Label,
    name_resolution::symbol::{Symbol, TypeId},
    span::Span,
    types::{
        constraints::{
            call::Call,
            conforms::Conforms,
            constraint::{Constraint, ConstraintCause},
            construction::Construction,
            equals::Equals,
            has_field::HasField,
            member::Member,
        },
        row::Row,
        ty::Ty,
    },
};

#[derive(Debug, Default)]
pub struct Wants {
    pub simple: VecDeque<Constraint>,
    pub defer: VecDeque<Constraint>,
}

impl Wants {
    pub fn pop(&mut self) -> Option<Constraint> {
        self.simple.pop_front().or_else(|| self.defer.pop_front())
    }

    pub fn is_empty(&self) -> bool {
        self.simple.is_empty() && self.defer.is_empty()
    }

    pub fn to_vec(self) -> Vec<Constraint> {
        self.simple.into_iter().chain(self.defer).collect()
    }

    pub fn push(&mut self, constraint: Constraint) {
        tracing::debug!("constraining {constraint:?}");
        match &constraint {
            Constraint::Call(..) => self.defer.push_back(constraint),
            Constraint::Equals(..) => self.simple.push_back(constraint),
            Constraint::HasField(..) => self.simple.push_back(constraint),
            Constraint::Member(..) => self.defer.push_back(constraint),
            Constraint::Construction(..) => self.defer.push_back(constraint),
            Constraint::Conforms(..) => self.defer.push_back(constraint),
        }
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
        self.defer.push_back(Constraint::Construction(Construction {
            callee,
            args,
            returns,
            type_symbol,
            cause,
            span,
        }))
    }

    pub fn conforms(&mut self, type_id: TypeId, protocol_id: TypeId, span: Span) {
        tracing::debug!("constraining conforms {type_id:?} < {protocol_id:?}");
        self.defer.push_back(Constraint::Conforms(Conforms {
            type_id,
            protocol_id,
            span,
        }));
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
        self.defer.push_back(Constraint::Call(Call {
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
        self.simple.push_back(Constraint::Equals(Equals {
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
        self.defer.push_back(Constraint::Member(Member {
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
        self.simple.push_back(Constraint::HasField(HasField {
            row,
            label,
            ty,
            cause,
            span,
        }))
    }
}
