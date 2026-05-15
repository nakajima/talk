use itertools::Itertools;

use super::{InferencePass, TypedRet};
use crate::{
    name::Name,
    name_resolution::symbol::{ProtocolId, Symbol, set_symbol_names},
    node_id::NodeID,
    node_kinds::{body::Body, decl::DeclKind},
    span::Span,
    types::{
        conformance::{ConformanceClaim, ConformanceObligation},
        solve_context::SolveContext,
        type_error::TypeError,
    },
};

impl InferencePass<'_> {
    pub(super) fn conformance_claim_from_body(
        conforming_symbol: Symbol,
        protocol_id: ProtocolId,
        node_id: NodeID,
        span: Span,
        body: &Body,
    ) -> ConformanceClaim {
        let mut claim = ConformanceClaim::new(node_id, conforming_symbol, protocol_id, span);

        for member in &body.decls {
            match &member.kind {
                DeclKind::TypeAlias(lhs, ..) => {
                    if let Ok(sym) = lhs.symbol() {
                        claim
                            .associated_type_candidates
                            .insert(lhs.name_str().into(), sym);
                    }
                }
                DeclKind::Method { func, is_static } if !*is_static => {
                    if let Ok(sym) = func.name.symbol() {
                        claim
                            .method_candidates
                            .insert(func.name.name_str().into(), sym);
                    }
                }
                _ => {}
            }
        }

        claim
    }

    pub(super) fn register_conformance(
        &mut self,
        conforming_symbol: Symbol,
        protocol_symbol: Symbol,
        conformance_node_id: NodeID,
        conformance_span: Span,
        context: &mut SolveContext,
    ) -> TypedRet<()> {
        let _s = set_symbol_names(self.session.resolved_names.symbol_names.clone());

        let Symbol::Protocol(protocol_id) = protocol_symbol else {
            tracing::error!("didnt get protocol id for conformance: {protocol_symbol:?}");
            return Err(TypeError::NameNotResolved(Name::Resolved(
                protocol_symbol,
                "".into(),
            )));
        };

        let transitive_conformance_keys = self
            .session
            .type_catalog
            .conformance_evidence
            .keys()
            .filter(|c| c.conforming_id == protocol_symbol)
            .copied()
            .collect_vec();

        for indirect_conformance in transitive_conformance_keys {
            let (sym, node_id, span) = {
                let indirect = self
                    .session
                    .type_catalog
                    .conformance_evidence
                    .get(&indirect_conformance)
                    .unwrap_or_else(|| unreachable!());
                (
                    Symbol::Protocol(indirect.protocol_id),
                    indirect.node_id,
                    indirect.span,
                )
            };

            self.register_conformance(conforming_symbol, sym, node_id, span, context)?;
        }

        // Get the protocol's associated type declarations
        // First try ASTs (for locally defined protocols), then type_catalog (for imported protocols)
        let protocol_associated_types = self
            .session
            .resolved_names
            .child_types
            .get(&protocol_symbol)
            .cloned()
            .or_else(|| self.session.lookup_associated_types(protocol_symbol))
            .unwrap_or_default();

        self.session.declare_conformance(ConformanceClaim::new(
            conformance_node_id,
            conforming_symbol,
            protocol_id,
            conformance_span,
        ));

        let mut obligation = ConformanceObligation::new(
            conformance_node_id,
            conforming_symbol,
            protocol_id,
            conformance_span,
        );

        for (label, _) in protocol_associated_types {
            let associated_ty =
                self.session
                    .associated_type_slot(obligation.key(), &label, context.level());
            obligation.associated_types.insert(label, associated_ty);
        }

        self.session.declare_conformance_obligation(obligation);

        Ok(())
    }
}
