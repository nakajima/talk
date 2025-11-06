//SLOPFILE

use tracing::instrument;

use crate::{
    name_resolution::symbol::{AssociatedTypeId, ProtocolId},
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_ty::{InferTy, Level},
        type_catalog::ConformanceKey,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AssociatedEquals {
    pub node_id: NodeID,
    pub subject: InferTy,
    pub protocol_id: ProtocolId,
    pub associated_type_id: AssociatedTypeId,
    pub output: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl AssociatedEquals {
    #[instrument(level = tracing::Level::TRACE, skip(session, substitutions))]
    pub fn solve(
        &self,
        session: &mut TypeSession,
        level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let subject = apply(self.subject.clone(), substitutions);
        let subject_symbol = match subject {
            InferTy::Nominal { symbol, .. } => symbol,
            InferTy::Primitive(symbol) => symbol,
            _ => panic!("can't get subject symbol from: {subject:?}"),
        };

        let conformance = session
            .lookup_conformance_mut(&ConformanceKey {
                protocol_id: self.protocol_id,
                conforming_id: subject_symbol,
            })
            .expect("did not get conformance");

        let ty = conformance
            .associated_types
            .get(&self.associated_type_id)
            .expect("did not get associated requirement");

        let ty = apply(ty.clone(), substitutions);

        next_wants.equals(ty, self.output.clone(), self.cause, self.span);
        Ok(false)
    }
}
