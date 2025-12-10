use crate::types::conformance::ConformanceKey;
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
use rustc_hash::FxHashMap;
use tracing::instrument;

type CheckWitnessResult = (Vec<(Label, Symbol)>, Vec<Meta>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Conforms {
    pub id: ConstraintId,
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
                // For type parameters, check if any given conformance implies conformance
                // to the target protocol through protocol inheritance.
                //
                // Example: if we have `T: B` as a given, and `protocol B: A`, then
                // `T: A` is satisfied because B inherits from A.
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
        let Some(conformance) = session
            .type_catalog
            .conformances
            .get(&ConformanceKey {
                conforming_id: conforming_ty_sym,
                protocol_id: self.protocol_id,
            })
            .cloned()
        else {
            return SolveResult::Err(TypeError::TypesDoesNotConform {
                symbol: conforming_ty_sym,
                protocol_id: self.protocol_id,
            });
        };

        let Some(EnvEntry::Scheme(Scheme {
            ty: InferTy::Param(protocol_self_id),
            ..
        })) = session.lookup(&self.protocol_id.into())
        else {
            return SolveResult::Err(TypeError::TypeNotFound(format!(
                "did not find protocol self: {:?}",
                self.protocol_id
            )));
        };

        // Build up some substitutions so we're not playing with the protocol's type params anymore
        let mut substitutions: FxHashMap<InferTy, InferTy> = FxHashMap::default();
        substitutions.insert(InferTy::Param(protocol_self_id), self.ty.clone());

        let mut protocol_projections = FxHashMap::<Label, InferTy>::default();
        for (label, associated_sym) in session
            .type_catalog
            .associated_types
            .get(&self.protocol_id.into())
            .cloned()
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
                .get(&label.to_string())
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
                            .expect("discover_conformances didn't set associated type")
                    })
                    .clone()
            } else {
                #[allow(clippy::expect_used)]
                conformance
                    .witnesses
                    .associated_types
                    .get(&label)
                    .cloned()
                    .expect("discover_conformances didn't set associated type")
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
                    SolveResult::Err(TypeError::MissingConformanceRequirement(format!(
                        "{missing_conformances:?}"
                    )))
                }
            }
            Err(e) => SolveResult::Err(e),
        }
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

        let Some(requirements) = session
            .type_catalog
            .method_requirements
            .get(&self.protocol_id.into())
            .cloned()
        else {
            return Ok((missing_witnesses, solved_metas));
        };

        let instance_methods = session
            .type_catalog
            .instance_methods
            .get(conforming_ty_sym)
            .cloned()
            .unwrap_or_default();

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

            let Some(witness_sym) = instance_methods.get(&label) else {
                missing_witnesses.push((label, required_sym));
                continue;
            };

            let Some(witness) = session.lookup(witness_sym).clone() else {
                tracing::error!("Didn't get witness for sym: {witness_sym:?}");
                continue;
            };

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
