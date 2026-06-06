use crate::node_id::NodeID;
use crate::types::conformance::{
    ConformanceEvidence, ConformanceKey, ConformanceOrigin, WitnessTable,
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
                        if session.protocol_implies(*given_protocol_id, self.protocol_id) {
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
            None,
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
        seed: Option<ConformanceEvidence>,
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

        let Some(conformance) = session.conformance_seed(key, seed) else {
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

            let associated_type_candidate =
                session.associated_type_candidate(key, &label, conformance.origin);

            let associated_witness_ty = if let Some(witness_type_sym) = associated_type_candidate {
                let Some(entry) = session.lookup(&witness_type_sym) else {
                    deferral_reasons.push(DeferralReason::WaitingOnSymbol(witness_type_sym));
                    continue;
                };

                entry._as_ty()
            } else {
                let pending_ty = witnesses
                    .associated_types
                    .get(&label)
                    .cloned()
                    .or_else(|| session.lookup_associated_type_slot(&key, &label))
                    .unwrap_or_else(|| session.associated_type_slot(key, &label, context.level()));

                if let Some(projection) = protocol_projections.get(&label) {
                    substitutions
                        .entry(projection.clone())
                        .or_insert_with(|| pending_ty.clone())
                        .clone()
                } else {
                    pending_ty
                }
            };

            witnesses
                .associated_types
                .insert(label.clone(), associated_witness_ty.clone());

            substitutions.insert(associated_entry._as_ty(), associated_witness_ty);
        }

        // Check super protocols
        for super_key in session.superprotocol_keys_for(protocol_id) {
            let inherited =
                session.inherited_evidence(&conformance, conforming_ty_sym, super_key.protocol_id);
            match self.check_conformance(
                conforming_ty_sym,
                conforming_type_args,
                super_key.protocol_id,
                Some(inherited),
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
            key,
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
                session.record_witnesses(key, conformance, witnesses);
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
        conformance_key: ConformanceKey,
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

            let witness_sym = session.method_witness_candidate(
                conformance_key,
                &label,
                &required_sym,
                conformance_origin,
                witness_table,
            );
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
