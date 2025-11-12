use crate::{
    ast::AST,
    label::Label,
    name_resolution::{name_resolver::NameResolved, symbol::ProtocolId},
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_ty::InferTy,
        solve_context::{Solve, SolveContext},
        type_catalog::ConformanceKey,
        type_error::TypeError,
        type_operations::apply,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Projection {
    pub protocol_id: Option<ProtocolId>,
    pub node_id: NodeID,
    pub base: InferTy,
    pub label: Label,
    pub result: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl Projection {
    pub fn solve(
        &self,
        ast: &AST<NameResolved>,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> Result<bool, TypeError> {
        let base = apply(self.base.clone(), &mut context.substitutions);
        let result = apply(self.result.clone(), &mut context.substitutions);

        // Try to reduce when base is a concrete nominal
        if let InferTy::Nominal {
            symbol: base_sym, ..
        } = base
        {
            let conformance = if let Some(protocol_id) = self.protocol_id {
                session.type_catalog.conformances.get(&ConformanceKey {
                    protocol_id, // add this field to Projection (see below)
                    conforming_id: base_sym,
                })
            } else {
                session
                    .type_catalog
                    .conformances
                    .values()
                    .find(|c| c.conforming_id == base_sym)
            };

            // Find a conformance for the nominal base that mentions this associated label
            if let Some(conf) = conformance {
                // Prefer the alias symbol (if the nominal actually provided `typealias T = ...`)
                if let Some(alias_sym) = ast
                    .phase
                    .child_types
                    .get(&base_sym)
                    .and_then(|t| t.get(&self.label))
                    .cloned()
                {
                    // Instantiate the nominal TYPE scheme at this projection node id.
                    // This yields Type(@Struct(base_sym), row metas_for_A, ...)
                    let nominal_entry = session.lookup(&base_sym).expect("nominal env entry");
                    let nominal_inst =
                        nominal_entry.instantiate(self.node_id, context, session, self.span);

                    // Force the base we're projecting from to be "this" instantiation,
                    // so the metas_for_A unify with the actual arguments (Float/Int).
                    context.wants_mut().equals(
                        base.clone(),
                        nominal_inst,
                        ConstraintCause::Internal,
                        self.span,
                    );

                    // Instantiate the alias SCHEME at the SAME node id.
                    // This reuses the exact same TypeParamId -> meta mapping as the nominal above.
                    let alias_entry = session.lookup(&alias_sym).expect("alias env entry");
                    let alias_inst =
                        alias_entry.instantiate(self.node_id, context, session, self.span);

                    // Self.T must equal the instantiated alias.
                    context.wants_mut().equals(
                        result.clone(),
                        alias_inst,
                        ConstraintCause::Internal,
                        self.span,
                    );

                    return Ok(true);
                }

                // Fallback: no alias symbol recorded; if a concrete (non-param) witness
                // was recorded for this conformance, equate to it. Otherwise leave unsolved.
                if let Some(witness) = conf.associated_types.get(&self.label) {
                    let witness = apply(witness.clone(), &mut context.substitutions);
                    if !matches!(witness, InferTy::Param(_)) {
                        context.wants_mut().equals(
                            result,
                            witness,
                            ConstraintCause::Internal,
                            self.span,
                        );
                        return Ok(true);
                    }
                }
            }
        }

        Ok(false)
    }
}
