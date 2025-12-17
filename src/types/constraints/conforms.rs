use crate::node_id::NodeID;
use crate::span::Span;
use crate::types::conformance::{Conformance, ConformanceKey, Witnesses};
use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::store::ConstraintId,
        infer_ty::{InferTy, Meta, TypeParamId},
        predicate::Predicate,
        scheme::Scheme,
        solve_context::SolveContext,
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{substitute, unify},
        type_session::TypeSession,
    },
};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

type CheckWitnessResult = (Vec<(Label, Symbol)>, Vec<Meta>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Conforms {
    pub id: ConstraintId,
    pub conformance_node_id: NodeID,
    pub ty: InferTy,
    pub protocol_id: ProtocolId,
}

impl Conforms {
    #[instrument(skip(session))]
    pub fn solve(&self, context: &mut SolveContext, session: &mut TypeSession) -> SolveResult {
        let conforming_ty_sym = match &self.ty {
            InferTy::Var { id, .. } => {
                return SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)));
            }
            InferTy::Primitive(symbol) => *symbol,
            InferTy::Nominal { symbol, .. } => *symbol,
            InferTy::Param(param_id) => {
                for given in &context.givens {
                    if let Predicate::Conforms {
                        param,
                        protocol_id: given_protocol_id,
                    } = given
                        && param == param_id
                    {
                        // Direct conformance: param conforms to exactly the protocol we need
                        if *given_protocol_id == self.protocol_id {
                            return SolveResult::Solved(Default::default());
                        }

                        // Transitive conformance: param conforms to a protocol that
                        // itself conforms to the target protocol
                        let key = ConformanceKey {
                            conforming_id: Symbol::Protocol(*given_protocol_id),
                            protocol_id: self.protocol_id,
                        };

                        if session.type_catalog.conformances.contains_key(&key) {
                            return SolveResult::Solved(Default::default());
                        }
                    }
                }

                return SolveResult::Err(TypeError::TypesCannotConform {
                    ty: self.ty.clone(),
                    protocol_id: self.protocol_id,
                });
            }
            _ => {
                return SolveResult::Err(TypeError::TypesCannotConform {
                    ty: self.ty.clone(),
                    protocol_id: self.protocol_id,
                });
            }
        };

        // Make sure a conformance is declared, otherwise what's even the point of checking anything else
        let key = ConformanceKey {
            conforming_id: conforming_ty_sym,
            protocol_id: self.protocol_id,
        };
        let Some(conformance) = session.lookup_conformance(&key) else {
            return SolveResult::Defer(DeferralReason::WaitingOnConformance(key));
        };

        let Some(EnvEntry::Scheme(Scheme {
            ty: InferTy::Param(protocol_self_id),
            ..
        })) = session.lookup(&self.protocol_id.into())
        else {
            return SolveResult::Defer(DeferralReason::WaitingOnSymbol(self.protocol_id.into()));
        };

        // Build up some substitutions so we're not playing with the protocol's type params anymore
        let mut substitutions: FxHashMap<InferTy, InferTy> = FxHashMap::default();
        substitutions.insert(InferTy::Param(protocol_self_id), self.ty.clone());

        // If we're registering a conformance for a nominal, copy specialized versions of default methods
        if !matches!(conforming_ty_sym, Symbol::Protocol(..))
            && let Err(e) = self.specialize_methods(
                &conforming_ty_sym,
                self.protocol_id,
                session,
                substitutions.clone(),
                Default::default(),
            )
        {
            return SolveResult::Err(e);
        };

        let mut protocol_projections = FxHashMap::<Label, InferTy>::default();
        for (label, associated_sym) in session
            .lookup_associated_types(self.protocol_id.into())
            .unwrap_or_default()
        {
            let Some(associated_entry) = session.lookup(&associated_sym) else {
                return SolveResult::Defer(DeferralReason::WaitingOnSymbol(associated_sym));
            };

            for predicate in associated_entry.predicates() {
                if let Predicate::Projection {
                    base,
                    label,
                    returns,
                    protocol_id,
                } = predicate
                    && protocol_id == Some(self.protocol_id)
                    && base == InferTy::Param(protocol_self_id)
                {
                    protocol_projections.insert(label, returns);
                }
            }

            let associated_witness_ty = if let Some(witness_type_sym) = session
                .type_catalog
                .child_types
                .get(&conforming_ty_sym)
                .cloned()
                .unwrap_or_default()
                .get(&label)
            {
                if let Some(entry) = session.lookup(witness_type_sym) {
                    entry._as_ty()
                } else {
                    return SolveResult::Defer(DeferralReason::WaitingOnSymbol(*witness_type_sym));
                }
            } else if let Some(projection) = protocol_projections.get(&label) {
                substitutions
                    .entry(projection.clone())
                    .or_insert_with(|| {
                        #[allow(clippy::expect_used)]
                        conformance
                            .witnesses
                            .associated_types
                            .get(&label)
                            .cloned()
                            .unwrap_or_else(|| session.new_ty_meta_var(context.level))
                    })
                    .clone()
            } else {
                #[allow(clippy::expect_used)]
                conformance
                    .witnesses
                    .associated_types
                    .get(&label)
                    .cloned()
                    .unwrap_or_else(|| session.new_ty_meta_var(context.level))
            };

            substitutions.insert(associated_entry._as_ty(), associated_witness_ty);
        }

        match self.check_witnesses(
            context,
            session,
            &protocol_self_id,
            &conforming_ty_sym,
            protocol_projections,
            substitutions,
        ) {
            Ok((missing_conformances, solved_vars)) => {
                if missing_conformances.is_empty() {
                    SolveResult::Solved(solved_vars)
                } else {
                    SolveResult::Defer(DeferralReason::WaitingOnSymbols(
                        missing_conformances.iter().map(|c| c.1).collect(),
                    ))
                    // SolveResult::Err(TypeError::MissingConformanceRequirement(format!(
                    //     "{missing_conformances:?}"
                    // )))
                }
            }
            Err(e) => SolveResult::Err(e),
        }
    }

    fn specialize_methods(
        &self,
        conforming_ty_sym: &Symbol,
        protocol_id: ProtocolId,
        session: &mut TypeSession,
        mut substitutions: FxHashMap<InferTy, InferTy>,
        mut seen: FxHashSet<ProtocolId>,
    ) -> Result<(), TypeError> {
        if seen.contains(&protocol_id) {
            return Ok(());
        }

        seen.insert(protocol_id);

        let Some(EnvEntry::Scheme(Scheme {
            ty: InferTy::Param(protocol_self_id),
            ..
        })) = session.lookup(&protocol_id.into())
        else {
            return Err(TypeError::TypeNotFound(format!(
                "Did not find protocol self for {:?}",
                protocol_id
            )));
        };

        substitutions.insert(InferTy::Param(protocol_self_id), self.ty.clone());

        for (label, sym) in session.lookup_instance_methods(&protocol_id.into()) {
            let Some(entry) = session.lookup(&sym) else {
                tracing::error!("didn't get entry for {sym:?}");
                continue;
            };

            let specialized_entry = entry.substitute(&substitutions);
            let specialized_symbol = session
                .symbols
                .next_instance_method(session.current_module_id);
            let name_str = session
                .resolve_name(&sym)
                .unwrap_or_else(|| unreachable!("Didn't get name for symbol: {sym:}"));
            session
                .resolved_names
                .symbol_names
                .insert(specialized_symbol.into(), name_str.to_string());

            session.insert_term(
                specialized_symbol.into(),
                specialized_entry,
                &mut Default::default(),
            );

            session
                .type_catalog
                .instance_methods
                .entry(*conforming_ty_sym)
                .or_default()
                .insert(label, specialized_symbol.into());

            for key in session
                .type_catalog
                .conformances
                .keys()
                .cloned()
                .collect_vec()
            {
                self.specialize_methods(
                    conforming_ty_sym,
                    key.protocol_id,
                    session,
                    substitutions.clone(),
                    seen.clone(),
                )?;
            }
        }

        Ok(())
    }

    fn check_witnesses(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
        protocol_self_id: &TypeParamId,
        conforming_ty_sym: &Symbol,
        projections: FxHashMap<Label, InferTy>,
        mut substitutions: FxHashMap<InferTy, InferTy>,
    ) -> Result<CheckWitnessResult, TypeError> {
        let mut missing_witnesses = vec![];
        let mut solved_metas = vec![];

        let Some(requirements) = session.lookup_method_requirements(self.protocol_id.into()) else {
            return Ok((missing_witnesses, solved_metas));
        };

        for (label, required_sym) in requirements {
            let Some(required_entry) = session.lookup(&required_sym).clone() else {
                return Err(TypeError::TypeNotFound(format!(
                    "did not find required protocol entry: {label} {required_sym:?}"
                )));
            };

            for predicate in required_entry.predicates() {
                if let Predicate::Projection {
                    base,
                    label,
                    returns,
                    ..
                } = predicate
                    && base == InferTy::Param(*protocol_self_id)
                    && let Some(projection) = projections.get(&label)
                    && let Some(substitution) = substitutions.get(projection).cloned()
                {
                    substitutions.insert(returns.clone(), substitution.clone());
                }
            }

            let required_ty = substitute(required_entry._as_ty(), &substitutions);

            let Some(witness_sym) = session.lookup_concrete_member(conforming_ty_sym, &label)
            else {
                missing_witnesses.push((label, required_sym));
                continue;
            };

            let Some(witness) = session.lookup(&witness_sym).clone() else {
                tracing::error!("Didn't get witness for sym: {witness_sym:?}");
                missing_witnesses.push((label, witness_sym));
                continue;
            };

            // Update witnesses
            let key = ConformanceKey {
                protocol_id: self.protocol_id,
                conforming_id: *conforming_ty_sym,
            };

            let entry = session
                .type_catalog
                .conformances
                .entry(key)
                .or_insert(Conformance {
                    node_id: self.conformance_node_id,
                    conforming_id: *conforming_ty_sym,
                    protocol_id: self.protocol_id,
                    witnesses: Witnesses::default(),
                    span: Span::SYNTHESIZED,
                });

            entry.witnesses.methods.insert(label.clone(), witness_sym);

            match unify(&required_ty, &witness._as_ty(), context, session) {
                Ok(vars) => solved_metas.extend(vars),
                Err(e) => {
                    tracing::error!("Error checking witness {label:?}: {e:?}");
                    missing_witnesses.push((label, required_sym))
                }
            }
        }

        Ok((missing_witnesses, solved_metas))
    }
}
