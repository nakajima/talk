use indexmap::IndexSet;
use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    types::{
        conformance::ConformanceKey,
        constraint_solver::{DeferralReason, SolveResult},
        constraints::store::{ConstraintId, ConstraintStore},
        infer_ty::{Level, Meta, Ty},
        solve_context::SolveContext,
        type_error::TypeError,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Projection {
    pub id: ConstraintId,
    pub protocol_id: Option<ProtocolId>,
    pub node_id: NodeID,
    pub base: Ty,
    pub label: Label,
    pub result: Ty,
}

impl Projection {
    #[instrument(skip(constraints, context, session,))]
    pub fn solve(
        &self,
        level: Level,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        let base = session.apply(self.base.clone(), &mut context.substitutions_mut());
        let result = session.apply(self.result.clone(), &mut context.substitutions_mut());

        // Try to reduce when base is a concrete nominal or primitive
        let base_sym = match &base {
            Ty::Nominal { symbol, .. } => Some(*symbol),
            Ty::Primitive(symbol) => Some(*symbol),
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
            if let Some(conf) = conformance {
                // Prefer the alias symbol (if the nominal actually provided `typealias T = ...`)
                if let Some(alias_sym) = session
                    .resolved_names
                    .child_types
                    .get(&base_sym)
                    .and_then(|t| t.get(&self.label))
                    .cloned()
                {
                    // Instantiate the nominal TYPE scheme at this projection node id.
                    // This yields Type(@Struct(base_sym), row metas_for_A, ...)
                    let Some(nominal_entry) = session.lookup(&base_sym) else {
                        return SolveResult::Err(TypeError::TypeNotFound(format!(
                            "Projection {:?} not found for {:?}",
                            self.label, self.base
                        )));
                    };

                    let nominal_inst =
                        nominal_entry.instantiate(self.node_id, constraints, context, session);

                    // Force the base we're projecting from to be "this" instantiation,
                    // so the metas_for_A unify with the actual arguments (Float/Int).
                    let group = constraints.copy_group(self.id);
                    constraints.wants_equals_at(self.node_id, base.clone(), nominal_inst, &group);

                    let Some(alias_entry) = session.lookup(&alias_sym) else {
                        return SolveResult::Err(TypeError::TypeNotFound(format!(
                            "Type alias {:?} not found for projection {alias_sym:?}",
                            self.label
                        )));
                    };

                    let alias_inst =
                        alias_entry.instantiate(self.node_id, constraints, context, session);

                    // Self.T must equal the instantiated alias.
                    let group = constraints.copy_group(self.id);
                    constraints.wants_equals_at(self.node_id, result.clone(), alias_inst, &group);

                    return SolveResult::Solved(Default::default());
                }

                // Fallback: no alias symbol recorded; if a concrete (non-param) witness
                // was recorded for this conformance, equate to it. Otherwise leave unsolved.
                if let Some(witness) = conf.witnesses.associated_types.get(&self.label).cloned() {
                    let witness_applied = session.apply(witness.clone(), &mut context.substitutions_mut());
                    if !matches!(witness_applied, Ty::Param(..)) {
                        let group = constraints.copy_group(self.id);
                        constraints.wants_equals_at(self.node_id, result, witness_applied, &group);
                        return SolveResult::Solved(Default::default());
                    }
                }
            }
        }

        // If the base is still a meta variable, try to infer it from the result type
        if let Ty::Var { id, .. } = &base {
            // If we have a concrete result and a known protocol, try to find which type
            // would give us this associated type value (defaulting)
            if let Some(protocol_id) = self.protocol_id {
                tracing::debug!(
                    "Projection defaulting: base={:?}, result={:?}, protocol={:?}",
                    base,
                    result,
                    protocol_id
                );

                if !matches!(result, Ty::Var { .. }) {
                    // Find all conformances to this protocol where the associated type matches
                    // First collect relevant conformance keys to avoid borrow issues

                    let candidate_keys: Vec<_> = session.lookup_protocol_conformances(&protocol_id);
                    let num_candidates = candidate_keys.len();

                    // Now check which ones match (with mutable access to session)
                    let matching: IndexSet<_> = candidate_keys
                        .into_iter()
                        .filter_map(|key| {
                            let conformance = session.lookup_conformance(&key)?;
                            let assoc_ty = conformance
                                .witnesses
                                .associated_types
                                .get(&self.label)?
                                .clone();
                            let applied =
                                session.apply(assoc_ty.clone(), &mut context.substitutions_mut());
                            if applied == result {
                                Some((key, assoc_ty))
                            } else {
                                None
                            }
                        })
                        .collect();

                    tracing::debug!(
                        "Projection defaulting: candidates={:?}, matching={:?}",
                        num_candidates,
                        matching.len()
                    );

                    // If exactly one candidate, unify the base with that type
                    return match matching.len() {
                        0 => SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id))),
                        1 => {
                            let (key, _) = &matching[0];
                            let conforming_ty = if matches!(key.conforming_id, Symbol::Builtin(..))
                            {
                                Ty::Primitive(key.conforming_id)
                            } else {
                                Ty::Nominal {
                                    symbol: key.conforming_id,
                                    type_args: Default::default(),
                                }
                            };
                            let group = constraints.copy_group(self.id);
                            constraints.wants_equals_at(
                                self.node_id,
                                base.clone(),
                                conforming_ty,
                                &group,
                            );
                            return SolveResult::Solved(vec![Meta::Ty(*id)]);
                        }
                        _ => {
                            unimplemented!("ambiguous: {matching:?}");
                        }
                    };
                }
            }

            return SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)));
        }

        // If we have a concrete base type and a protocol, defer waiting for that conformance
        if let Some(base_sym) = match &base {
            Ty::Nominal { symbol, .. } => Some(*symbol),
            Ty::Primitive(symbol) => Some(*symbol),
            _ => None,
        } && let Some(protocol_id) = self.protocol_id
        {
            let key = ConformanceKey {
                protocol_id,
                conforming_id: base_sym,
            };
            return SolveResult::Defer(DeferralReason::WaitingOnConformance(key));
        }

        SolveResult::Defer(DeferralReason::Unknown)
    }
}
