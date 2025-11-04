use std::collections::VecDeque;

use indexmap::IndexSet;

use crate::{
    label::Label,
    name_resolution::symbol::{AssociatedTypeId, ProtocolId, Symbol},
    node_id::NodeID,
    span::Span,
    types::{
        constraints::{
            associated_equals::AssociatedEquals,
            call::Call,
            conforms::Conforms,
            constraint::{Constraint, ConstraintCause},
            construction::Construction,
            equals::Equals,
            has_field::HasField,
            member::Member,
        },
        infer_row::InferRow,
        infer_ty::InferTy,
        predicate::Predicate,
    },
};

#[derive(Debug, Default)]
pub struct Wants {
    pub simple: VecDeque<Constraint>,
    pub defer: VecDeque<Constraint>,
    pub givens: IndexSet<Predicate<InferTy>>,
}

impl Wants {
    pub fn given(&mut self, predicate: Predicate<InferTy>) {
        self.givens.insert(predicate);
    }

    pub fn extend(&mut self, other: Wants) {
        self.simple.extend(other.simple);
        self.defer.extend(other.defer);
    }

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
            Constraint::AssociatedEquals(..) => self.defer.push_back(constraint),
            Constraint::TypeMember(..) => self.defer.push_back(constraint),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn construction(
        &mut self,
        callee_id: NodeID,
        callee: InferTy,
        args: Vec<InferTy>,
        returns: InferTy,
        type_symbol: Symbol,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining constructor {callee:?}({args:?}) = {type_symbol:?}");
        self.defer.push_back(Constraint::Construction(Construction {
            callee_id,
            callee,
            args,
            returns,
            type_symbol,
            cause,
            span,
        }))
    }

    pub fn conforms(&mut self, ty: InferTy, protocol_id: ProtocolId, span: Span) {
        tracing::debug!("constraining conforms {ty:?} < {protocol_id:?}");
        self.defer.push_back(Constraint::Conforms(Conforms {
            ty,
            protocol_id,
            span,
        }));
    }

    #[allow(clippy::too_many_arguments)]
    pub fn associated_equals(
        &mut self,
        node_id: NodeID,
        subject: InferTy,
        protocol_id: ProtocolId,
        associated_type_id: AssociatedTypeId,
        output: InferTy,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!(
            "constraining associated_equals {subject:?} = ({protocol_id:?}.{associated_type_id:?}) = {output:?}"
        );

        self.defer
            .push_back(Constraint::AssociatedEquals(AssociatedEquals {
                node_id,
                subject,
                protocol_id,
                associated_type_id,
                output,
                cause,
                span,
            }));
    }

    #[allow(clippy::too_many_arguments)]
    pub fn call(
        &mut self,
        callee_id: NodeID,
        callee: InferTy,
        args: Vec<InferTy>,
        type_args: Vec<InferTy>,
        returns: InferTy,
        receiver: Option<InferTy>,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining call {callee:?}({args:?}) = {returns:?}");
        self.defer.push_back(Constraint::Call(Call {
            callee_id,
            callee,
            args,
            type_args,
            returns,
            receiver,
            cause,
            span,
        }))
    }

    pub fn all(&self) -> Vec<Constraint> {
        let mut result = vec![];
        result.extend(self.simple.clone());
        result.extend(self.defer.clone());
        result
    }

    pub fn equals(&mut self, lhs: InferTy, rhs: InferTy, cause: ConstraintCause, span: Span) {
        if lhs == rhs {
            return;
        }

        // if !lhs.collect_foralls().is_empty() || !rhs.collect_foralls().is_empty() {
        //     panic!("cannot constrain forall: {lhs:?}, {rhs:?}");
        // }

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
        node_id: NodeID,
        receiver: InferTy,
        label: Label,
        ty: InferTy,
        cause: ConstraintCause,
        span: Span,
    ) {
        tracing::debug!("constraining member {receiver:?}.{label:?} <> {ty:?}");
        self.defer.push_back(Constraint::Member(Member {
            node_id,
            receiver,
            label,
            ty,
            cause,
            span,
        }))
    }

    pub fn _has_field(
        &mut self,
        row: InferRow,
        label: Label,
        ty: InferTy,
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
