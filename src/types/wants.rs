use std::collections::VecDeque;

use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::ProtocolId,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::{
            call::Call, conforms::Conforms, constraint::Constraint, equals::Equals,
            has_field::HasField, member::Member, projection::Projection, type_member::TypeMember,
        },
        infer_row::InferRow,
        infer_ty::{InferTy, Level},
        type_operations::UnificationSubstitutions,
    },
};

#[derive(Debug, Default)]
pub struct Wants {
    pub simple: VecDeque<Constraint>,
    pub defer: VecDeque<Constraint>,
}

impl Wants {
    pub fn apply(&mut self, substitutions: &mut UnificationSubstitutions) {
        self.simple = std::mem::take(&mut self.simple)
            .into_iter()
            .map(|c| c.apply(substitutions))
            .collect();
        self.defer = std::mem::take(&mut self.defer)
            .into_iter()
            .map(|c| c.apply(substitutions))
            .collect();
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

    #[instrument(skip(self))]
    pub fn defer(&mut self, constraint: Constraint) {
        match &constraint {
            Constraint::Call(..) => self.defer.push_back(constraint),
            Constraint::Equals(..) => self.simple.push_back(constraint),
            Constraint::HasField(..) => self.simple.push_back(constraint),
            Constraint::Member(..) => self.defer.push_back(constraint),
            Constraint::Conforms(..) => self.defer.push_back(constraint),
            Constraint::TypeMember(..) => self.defer.push_back(constraint),
            Constraint::Projection(..) => self.defer.push_back(constraint),
        }
    }

    #[instrument(skip(self))]
    pub fn push(&mut self, constraint: Constraint) {
        match &constraint {
            Constraint::Call(..) => self.defer.push_back(constraint),
            Constraint::Equals(..) => self.simple.push_back(constraint),
            Constraint::HasField(..) => self.simple.push_back(constraint),
            Constraint::Member(..) => self.defer.push_back(constraint),
            Constraint::Conforms(..) => self.defer.push_back(constraint),
            Constraint::TypeMember(..) => self.defer.push_back(constraint),
            Constraint::Projection(..) => self.defer.push_back(constraint),
        }
    }

    #[instrument(skip(self))]
    pub fn conforms(&mut self, ty: InferTy, protocol_id: ProtocolId, span: Span) {
        self.defer.push_back(Constraint::Conforms(Conforms {
            ty,
            protocol_id,
            span,
        }));
    }

    #[instrument(skip(self))]
    pub fn type_member(
        &mut self,
        base: InferTy,
        name: Label,
        generics: Vec<InferTy>,
        result: InferTy,
        id: NodeID,
        span: Span,
    ) {
        self.defer.push_back(Constraint::TypeMember(TypeMember {
            node_id: id,
            base,
            name,
            generics,
            result,
            span,
        }));
    }

    #[allow(clippy::too_many_arguments)]
    #[instrument(skip(self))]
    pub fn call(
        &mut self,
        callee_id: NodeID,
        callee: InferTy,
        args: Vec<InferTy>,
        type_args: Vec<InferTy>,
        returns: InferTy,
        receiver: Option<InferTy>,
        level: Level,
        span: Span,
    ) {
        self.defer.push_back(Constraint::Call(Call {
            callee_id,
            callee,
            args,
            type_args,
            returns,
            receiver,
            level,
            span,
        }))
    }

    pub fn all(&self) -> Vec<Constraint> {
        let mut result = vec![];
        result.extend(self.simple.clone());
        result.extend(self.defer.clone());
        result
    }

    #[instrument(skip(self))]
    pub fn equals(&mut self, lhs: InferTy, rhs: InferTy) {
        if lhs == rhs {
            return;
        }

        // if !lhs.collect_foralls().is_empty() || !rhs.collect_foralls().is_empty() {
        //     panic!("cannot constrain forall: {lhs:?}, {rhs:?}");
        // }

        self.simple.push_back(Constraint::Equals(Equals {
            lhs,
            rhs,
            cause,
            span,
        }));
    }

    #[instrument(skip(self))]
    pub fn member(&mut self, node_id: NodeID, receiver: InferTy, label: Label, ty: InferTy) {
        self.defer.push_back(Constraint::Member(Member {
            node_id,
            receiver,
            label,
            ty,
            cause,
            span,
        }))
    }

    #[instrument(skip(self))]
    pub fn _has_field(&mut self, row: InferRow, label: Label, ty: InferTy) {
        self.simple
            .push_back(Constraint::HasField(HasField { row, label, ty }))
    }

    #[instrument(skip(self))]
    #[allow(clippy::too_many_arguments)]
    pub fn projection(
        &mut self,
        node_id: NodeID,
        base: InferTy,
        label: Label,
        protocol_id: Option<ProtocolId>,
        result: InferTy,
    ) {
        self.push(Constraint::Projection(Projection {
            node_id,
            base,
            protocol_id,
            label,
            result,
        }));
    }
}
