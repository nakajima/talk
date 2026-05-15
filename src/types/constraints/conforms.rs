use crate::node_id::NodeID;
use crate::types::conformance::{
    ConformanceClaim, ConformanceEvidence, ConformanceKey, ConformanceOrigin, WitnessTable,
};
use crate::types::constraints::store::ConstraintStore;
use crate::types::scheme::ForAll;
use crate::types::type_operations::{Substitutions, substitute_with_subs};
use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::store::ConstraintId,
        infer_ty::{Meta, Ty},
        predicate::Predicate,
        scheme::Scheme,
        solve_context::SolveContext,
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::unify,
        type_session::TypeSession,
    },
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::instrument;

enum CheckWitnessResult {
    Ok(Vec<(Label, Symbol)>, Vec<Meta>),
    Defer(Vec<DeferralReason>),
    Err(TypeError),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Conforms {
    pub id: ConstraintId,
    pub conformance_node_id: NodeID,
    pub ty: Ty,
    pub protocol_id: ProtocolId,
}

impl Conforms {
    #[instrument(skip(session, constraints, context))]
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        // Extract both the symbol and type args from the conforming type
        let (conforming_ty_sym, conforming_type_args) = match &self.ty {
            Ty::Var { id, .. } => {
                return SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)));
            }
            Ty::Primitive(symbol) => (*symbol, vec![]),
            Ty::Nominal { symbol, type_args } => (*symbol, type_args.clone()),
            Ty::Param(param_id, _) => {
                for given in context.givens_mut().iter() {
                    if let Predicate::Conforms {
                        param,
                        protocol_id: given_protocol_id,
                    } = given
                        && param == param_id
                    {
                        // Direct conformance: param conforms to exactly the protocol we need
                        if given_protocol_id == &self.protocol_id {
                            return SolveResult::Solved(Default::default());
                        }

                        // Transitive conformance: param conforms to a protocol that
                        // itself conforms to the target protocol
                        let key = ConformanceKey {
                            conforming_id: Symbol::Protocol(*given_protocol_id),
                            protocol_id: self.protocol_id,
                        };

                        if session.type_catalog.conformance_evidence.contains_key(&key) {
                            return SolveResult::Solved(Default::default());
                        }
                    }
                }

                return SolveResult::Err(TypeError::TypeCannotConform {
                    ty: self.ty.clone(),
                    protocol_id: self.protocol_id,
                });
            }
            Ty::Func(..) => {
                if session.is_auto_derivable(self.protocol_id) {
                    return SolveResult::Solved(Default::default());
                }
                return SolveResult::Err(TypeError::TypeCannotConform {
                    ty: self.ty.clone(),
                    protocol_id: self.protocol_id,
                });
            }
            _ => {
                return SolveResult::Err(TypeError::TypeCannotConform {
                    ty: self.ty.clone(),
                    protocol_id: self.protocol_id,
                });
            }
        };

        // Auto-derive if this protocol supports it
        if session.is_auto_derivable(self.protocol_id) {
            session.auto_derive_protocol(conforming_ty_sym, self.protocol_id, constraints);
        }

        match self.check_conformance(
            conforming_ty_sym,
            &conforming_type_args,
            self.protocol_id,
            constraints,
            context,
            session,
        ) {
            CheckWitnessResult::Ok(conformances, vars) => {
                if conformances.is_empty() {
                    SolveResult::Solved(vars)
                } else {
                    SolveResult::Defer(DeferralReason::WaitingOnSymbols(
                        conformances.iter().map(|c| c.1).collect(),
                    ))
                }
            }
            CheckWitnessResult::Defer(reason) => SolveResult::Defer(DeferralReason::Multi(reason)),
            CheckWitnessResult::Err(e) => SolveResult::Err(e),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(context, session, constraints))]
    fn check_conformance(
        &self,
        conforming_ty_sym: Symbol,
        conforming_type_args: &[Ty],
        protocol_id: ProtocolId,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> CheckWitnessResult {
        let mut missing_conformances = vec![];
        let mut solved_vars = vec![];

        // Make sure a conformance is declared, otherwise what's even the point of checking anything else
        let key = ConformanceKey {
            conforming_id: conforming_ty_sym,
            protocol_id,
        };

        let conformance_claim = session.lookup_conformance_claim(&key);
        let mut conformance = if let Some(conformance) = session.lookup_conformance(&key) {
            conformance
        } else if let Some(claim) = conformance_claim.as_ref() {
            ConformanceEvidence::from_claim(claim)
        } else {
            return CheckWitnessResult::Defer(vec![DeferralReason::WaitingOnConformance(key)]);
        };
        let mut witnesses = conformance.witnesses.clone();

        let Some(EnvEntry::Scheme(Scheme {
            ty: Ty::Param(protocol_self_id, protocol_self_bounds),
            ..
        })) = session.lookup(&protocol_id.into())
        else {
            return CheckWitnessResult::Defer(vec![DeferralReason::WaitingOnSymbol(
                self.protocol_id.into(),
            )]);
        };

        // Build up some substitutions so we're not playing with the protocol's type params anymore
        let mut substitutions: FxHashMap<Ty, Ty> = FxHashMap::default();
        substitutions.insert(
            Ty::Param(protocol_self_id, protocol_self_bounds.clone()),
            self.ty.clone(),
        );

        // Add substitutions for the conforming type's type params
        // e.g., for Person<Float> conforming to Aged, substitute A -> Float
        if !conforming_type_args.is_empty()
            && let Some(nominal) = session.lookup_nominal(&conforming_ty_sym)
        {
            for (param, arg) in nominal.type_params.iter().zip(conforming_type_args.iter()) {
                substitutions.insert(param.clone(), arg.clone());
            }
        }

        let mut deferral_reasons = vec![];

        let mut protocol_projections = FxHashMap::<Label, Ty>::default();
        for (label, associated_sym) in session
            .lookup_associated_types(protocol_id.into())
            .unwrap_or_default()
        {
            let Some(associated_entry) = session.lookup(&associated_sym) else {
                deferral_reasons.push(DeferralReason::WaitingOnSymbol(associated_sym));
                continue;
            };

            for predicate in associated_entry.predicates() {
                if let Predicate::Projection {
                    base,
                    label,
                    returns,
                    protocol_id: id,
                } = predicate
                    && id == Some(protocol_id)
                    && base == Ty::Param(protocol_self_id, protocol_self_bounds.clone())
                {
                    protocol_projections.insert(label, returns);
                }
            }

            let declared_witness_sym = conformance_claim
                .as_ref()
                .and_then(|claim| claim.associated_type_candidates.get(&label).copied());
            let child_witness_sym = if conformance_claim.is_none()
                && !matches!(conformance.origin, ConformanceOrigin::Declared)
            {
                session
                    .type_catalog
                    .child_types
                    .get(&conforming_ty_sym)
                    .and_then(|child_types| child_types.get(&label).copied())
            } else {
                None
            };

            let associated_witness_ty =
                if let Some(witness_type_sym) = declared_witness_sym.or(child_witness_sym) {
                    let Some(entry) = session.lookup(&witness_type_sym) else {
                        deferral_reasons.push(DeferralReason::WaitingOnSymbol(witness_type_sym));
                        continue;
                    };

                    entry._as_ty()
                } else if let Some(projection) = protocol_projections.get(&label) {
                    substitutions
                        .entry(projection.clone())
                        .or_insert_with(|| {
                            #[allow(clippy::expect_used)]
                            witnesses
                                .associated_types
                                .get(&label)
                                .cloned()
                                .unwrap_or_else(|| session.new_ty_meta_var(context.level()))
                        })
                        .clone()
                } else {
                    #[allow(clippy::expect_used)]
                    witnesses
                        .associated_types
                        .get(&label)
                        .cloned()
                        .unwrap_or_else(|| session.new_ty_meta_var(context.level()))
                };

            witnesses
                .associated_types
                .insert(label.clone(), associated_witness_ty.clone());

            substitutions.insert(associated_entry._as_ty(), associated_witness_ty);
        }

        // Check super protocols
        let mut super_conformance_keys = session
            .type_catalog
            .conformance_evidence
            .keys()
            .chain(session.type_catalog.conformance_claims.keys())
            .filter(|conformance| conformance.conforming_id == protocol_id.into())
            .copied()
            .collect_vec();
        super_conformance_keys.sort();
        super_conformance_keys.dedup();

        for conformance in super_conformance_keys {
            match self.check_conformance(
                conforming_ty_sym,
                conforming_type_args,
                conformance.protocol_id,
                constraints,
                context,
                session,
            ) {
                CheckWitnessResult::Ok(missing, vars) => {
                    missing_conformances.extend(missing);
                    solved_vars.extend(vars);
                }
                CheckWitnessResult::Defer(reasons) => deferral_reasons.extend(reasons),
                CheckWitnessResult::Err(e) => return CheckWitnessResult::Err(e),
            };
        }

        match self.check_witnesses(
            context,
            session,
            protocol_id,
            &protocol_self_id,
            &protocol_self_bounds,
            &conforming_ty_sym,
            conformance_claim.as_ref(),
            conformance.origin,
            &mut witnesses,
            protocol_projections,
            substitutions,
        ) {
            Ok(res) => match res {
                CheckWitnessResult::Ok(missing, vars) => {
                    missing_conformances.extend(missing);
                    solved_vars.extend(vars);
                }

                CheckWitnessResult::Defer(reasons) => deferral_reasons.extend(reasons),
                CheckWitnessResult::Err(e) => return CheckWitnessResult::Err(e),
            },
            Err(e) => return CheckWitnessResult::Err(e),
        }

        if deferral_reasons.is_empty() {
            if missing_conformances.is_empty() {
                conformance.witnesses = witnesses;
                session
                    .type_catalog
                    .conformance_evidence
                    .insert(key, conformance);
                constraints.wake_conformances(&[key]);
            }

            CheckWitnessResult::Ok(missing_conformances, solved_vars)
        } else {
            CheckWitnessResult::Defer(deferral_reasons)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_witnesses(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
        protocol_id: ProtocolId,
        protocol_self: &Symbol,
        protocol_self_bounds: &[ProtocolId],
        conforming_ty_sym: &Symbol,
        conformance_claim: Option<&ConformanceClaim>,
        conformance_origin: ConformanceOrigin,
        witness_table: &mut WitnessTable,
        projections: FxHashMap<Label, Ty>,
        ty_substitutions: FxHashMap<Ty, Ty>,
    ) -> Result<CheckWitnessResult, TypeError> {
        let mut missing_witnesses = vec![];
        let mut solved_metas = vec![];

        let Some(requirements) = session.lookup_method_requirements(protocol_id.into()) else {
            return Ok(CheckWitnessResult::Ok(missing_witnesses, solved_metas));
        };

        for (label, required_sym) in requirements {
            let Some(required_entry) = session.lookup(&required_sym).clone() else {
                return Err(TypeError::TypeNotFound(format!(
                    "did not find required protocol entry: {label} {required_sym:?}"
                )));
            };

            // Build unified substitutions for this requirement
            let mut substitutions = Substitutions::new();
            substitutions.ty = ty_substitutions.clone();

            // Handle projection predicates
            for predicate in required_entry.predicates() {
                if let Predicate::Projection {
                    base,
                    label,
                    returns,
                    ..
                } = predicate
                    && base == Ty::Param(*protocol_self, protocol_self_bounds.to_owned())
                    && let Some(projection) = projections.get(&label)
                    && let Some(substitution) = substitutions.ty.get(projection).cloned()
                {
                    substitutions.ty.insert(returns.clone(), substitution);
                }
            }

            let witness_sym = if let Some(claim) = conformance_claim {
                claim.method_candidates.get(&label).copied()
            } else {
                witness_table.get_witness(&label, &required_sym).or_else(
                    || match conformance_origin {
                        ConformanceOrigin::Declared => None,
                        ConformanceOrigin::AutoDerived | ConformanceOrigin::Inherited => {
                            session.lookup_concrete_member(conforming_ty_sym, &label)
                        }
                    },
                )
            };
            let Some(witness_sym) = witness_sym else {
                missing_witnesses.push((label, required_sym));
                continue;
            };

            let Some(witness) = session.lookup(&witness_sym).clone() else {
                tracing::error!("Didn't get witness for sym: {witness_sym:?}");
                missing_witnesses.push((label, witness_sym));
                continue;
            };

            // Add row param substitutions for the required entry's row params
            for forall in required_entry.foralls() {
                if let ForAll::Row(param) = forall {
                    let fresh_row_meta = session.new_row_meta_var(context.level());
                    substitutions.insert_row(param, fresh_row_meta);
                }
            }

            // Substitute required type with type and row substitutions
            let required_ty = substitute_with_subs(required_entry._as_ty(), &substitutions);

            // Map the witness's forall type params (from the extend block) to the
            // corresponding substitutions. The extend block may declare its own type
            // param symbols (e.g., C:48) that are distinct from the struct's (e.g., C:46).
            // Match them positionally with the nominal's type params.
            if let Some(nominal) = session.lookup_nominal(conforming_ty_sym) {
                let witness_forall_params: Vec<Symbol> = witness
                    .foralls()
                    .iter()
                    .filter_map(|f| {
                        if let ForAll::Ty(sym) = f {
                            Some(*sym)
                        } else {
                            None
                        }
                    })
                    .collect();
                for (witness_param, nominal_param) in
                    witness_forall_params.iter().zip(nominal.type_params.iter())
                {
                    if let Some(arg) = substitutions.ty.get(nominal_param).cloned() {
                        substitutions
                            .ty
                            .insert(Ty::Param(*witness_param, vec![]), arg);
                    }
                }
            }

            // Also substitute the witness type with the struct's type params
            // e.g., for Person<Float>, substitute A -> Float in getAge's type
            let witness_ty = substitute_with_subs(witness._as_ty(), &substitutions);

            tracing::debug!(
                "Checking witness {label:?}: required_ty={:?}, witness_ty={:?}",
                required_ty,
                witness_ty,
            );
            match unify(&required_ty, &witness_ty, context, session) {
                Ok(vars) => {
                    solved_metas.extend(vars);
                    witness_table.methods.insert(label.clone(), witness_sym);
                    witness_table.requirements.insert(required_sym, witness_sym);
                }
                Err(e) => {
                    tracing::error!("Error checking witness {label:?}: {e:?}");
                    missing_witnesses.push((label, required_sym))
                }
            }
        }

        Ok(CheckWitnessResult::Ok(missing_witnesses, solved_metas))
    }
}
