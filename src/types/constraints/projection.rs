use tracing::instrument;

use crate::{
    ast::AST,
    label::Label,
    name_resolution::{name_resolver::NameResolved, symbol::ProtocolId},
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::store::{ConstraintId, ConstraintStore},
        infer_ty::{InferTy, Level, Meta},
        solve_context::SolveContext,
        type_catalog::ConformanceKey,
        type_error::TypeError,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Projection {
    pub id: ConstraintId,
    pub protocol_id: Option<ProtocolId>,
    pub node_id: NodeID,
    pub base: InferTy,
    pub label: Label,
    pub result: InferTy,
}

impl Projection {
    #[instrument(skip(constraints, context, session, asts))]
    pub fn solve(
        &self,
        level: Level,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        asts: &[AST<NameResolved>],
    ) -> SolveResult {
        let base = session.apply(self.base.clone(), &mut context.substitutions);
        let result = session.apply(self.result.clone(), &mut context.substitutions);

        // Try to reduce when base is a concrete nominal or primitive
        let base_sym = match &base {
            InferTy::Nominal { symbol, .. } => Some(*symbol),
            InferTy::Primitive(symbol) => Some(*symbol),
            _ => None,
        };

        if let Some(base_sym) = base_sym {
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
            tracing::debug!("Projection: conformance={:?}", conformance);
            if let Some(conf) = conformance {
                // Prefer the alias symbol (if the nominal actually provided `typealias T = ...`)
                if let Some(alias_sym) = asts
                    .iter()
                    .find_map(|ast| ast.phase.child_types.get(&base_sym))
                    .and_then(|t| t.get(&self.label))
                    .cloned()
                {
                    // Instantiate the nominal TYPE scheme at this projection node id.
                    // This yields Type(@Struct(base_sym), row metas_for_A, ...)
                    let Some(nominal_entry) = session.lookup(&base_sym) else {
                        return SolveResult::Err(TypeError::TypeNotFound(format!(
                            "{:?}",
                            self.base
                        )));
                    };

                    let nominal_inst =
                        nominal_entry.instantiate(self.node_id, constraints, context, session);

                    // Force the base we're projecting from to be "this" instantiation,
                    // so the metas_for_A unify with the actual arguments (Float/Int).
                    constraints.wants_equals(base.clone(), nominal_inst);

                    let Some(alias_entry) = session.lookup(&alias_sym) else {
                        return SolveResult::Err(TypeError::TypeNotFound(format!("{alias_sym:?}")));
                    };

                    let alias_inst =
                        alias_entry.instantiate(self.node_id, constraints, context, session);

                    // Self.T must equal the instantiated alias.
                    constraints.wants_equals(result.clone(), alias_inst);

                    return SolveResult::Solved(Default::default());
                }

                // Fallback: no alias symbol recorded; if a concrete (non-param) witness
                // was recorded for this conformance, equate to it. Otherwise leave unsolved.
                if let Some(witness) = conf.associated_types.get(&self.label) {
                    let witness = session.apply(witness.clone(), &mut context.substitutions);
                    if !matches!(witness, InferTy::Param(_)) {
                        constraints.wants_equals(result, witness);
                        return SolveResult::Solved(Default::default());
                    }
                }
            }
        }

        // If the base is still a meta variable, try to infer it from the result type
        if let InferTy::Var { id, .. } = &base {
            // If we have a concrete result and a known protocol, try to find which type
            // would give us this associated type value (defaulting)
            if let Some(protocol_id) = self.protocol_id {
                tracing::debug!(
                    "Projection defaulting: base={:?}, result={:?}, protocol={:?}",
                    base,
                    result,
                    protocol_id
                );
                if !matches!(result, InferTy::Var { .. }) {
                    // Find all conformances to this protocol where the associated type matches
                    // First collect relevant conformance keys to avoid borrow issues
                    let candidate_keys: Vec<_> = session
                        .type_catalog
                        .conformances
                        .iter()
                        .filter_map(|(key, conf)| {
                            if key.protocol_id == protocol_id {
                                conf.associated_types
                                    .get(&self.label)
                                    .map(|assoc_ty| (key.conforming_id, assoc_ty.clone()))
                            } else {
                                None
                            }
                        })
                        .collect();

                    let num_candidates = candidate_keys.len();

                    // Now check which ones match (with mutable access to session)
                    let matching: Vec<_> = candidate_keys
                        .into_iter()
                        .filter(|(_, assoc_ty)| {
                            let applied =
                                session.apply(assoc_ty.clone(), &mut context.substitutions);
                            applied == result
                        })
                        .collect();

                    tracing::debug!(
                        "Projection defaulting: candidates={:?}, matching={:?}",
                        num_candidates,
                        matching.len()
                    );

                    // If exactly one candidate, unify the base with that type
                    if matching.len() == 1 {
                        let (conforming_id, _) = &matching[0];
                        tracing::debug!(
                            "Projection defaulting: unifying base with {:?}",
                            conforming_id
                        );
                        let conforming_ty = InferTy::Primitive(*conforming_id);
                        constraints.wants_equals(base.clone(), conforming_ty);
                        return SolveResult::Solved(vec![Meta::Ty(*id)]);
                    }
                }
            }

            SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)))
        } else {
            SolveResult::Defer(DeferralReason::Unknown)
        }
    }
}
