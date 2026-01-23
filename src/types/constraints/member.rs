use std::assert_matches::assert_matches;
use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::{
            constraint::ConstraintCause,
            store::{ConstraintId, ConstraintStore},
        },
        infer_row::InferRow,
        infer_ty::{InferTy, Meta},
        passes::uncurry_function,
        predicate::Predicate,
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::{curry, instantiate_ty, unify},
        type_session::TypeSession,
        variational::{AlternativeIndex, ChoiceAlternative, Configuration, DimensionId},
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Member {
    pub id: ConstraintId,
    pub node_id: NodeID,
    pub receiver: InferTy,
    pub label: Label,
    pub ty: InferTy,
}

impl Member {
    #[instrument(skip(constraints, context, session))]
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        let receiver = self.receiver.clone();
        let ty = self.ty.clone();

        // Debug: trace member constraint solving for `.name()` specifically
        if self.label.to_string() == "name" {
            tracing::debug!(
                "Member::solve for .name() - receiver: {:?}, ty: {:?}, node_id: {:?}",
                receiver,
                ty,
                self.node_id
            );
            if let InferTy::Var { id, .. } = &receiver {
                tracing::debug!(
                    "  receiver is Var, lookup_reverse_instantiation: {:?}",
                    session.lookup_reverse_instantiation(*id)
                );
            }
        }

        match &receiver {
            InferTy::Var { id, .. } => {
                // Use lookup_reverse_instantiation to find the type param through the union-find.
                // This handles the case where the meta was unified with another that has the mapping.
                if let Some(InferTy::Param(param_id, _)) = session.lookup_reverse_instantiation(*id)
                    && let SolveResult::Solved(metas) =
                        self.lookup_type_param_member(constraints, context, session, &ty, param_id)
                {
                    return SolveResult::Solved(metas);
                }

                tracing::trace!("waiting on meta {id:?}");

                return SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)));
            }
            InferTy::Rigid(id) => {
                let Some(InferTy::Param(type_param_id, _)) =
                    session.skolem_map.get(&InferTy::Rigid(*id))
                else {
                    unreachable!();
                };

                return self.lookup_type_param_member(
                    constraints,
                    context,
                    session,
                    &ty,
                    *type_param_id,
                );
            }
            InferTy::Param(id, _) => {
                return self.lookup_type_param_member(constraints, context, session, &ty, *id);
            }
            InferTy::Constructor { name, .. } => {
                return self.lookup_static_member(
                    constraints,
                    context,
                    session,
                    &name.symbol().unwrap_or_else(|_| unreachable!()),
                );
            }
            InferTy::Record(box row) => {
                constraints._has_field(
                    row.clone(),
                    self.label.clone(),
                    ty,
                    Some(self.node_id),
                    &constraints.copy_group(self.id),
                );
                return SolveResult::Solved(Default::default());
            }
            InferTy::Primitive(symbol) => {
                return self.lookup_nominal_member(
                    constraints,
                    context,
                    session,
                    symbol,
                    Default::default(),
                );
            }
            InferTy::Nominal { symbol, type_args } => {
                return self.lookup_nominal_member(
                    constraints,
                    context,
                    session,
                    symbol,
                    type_args,
                );
            }
            _ => {}
        }

        SolveResult::Defer(DeferralReason::Unknown)
    }

    #[allow(clippy::too_many_arguments)]
    #[instrument(skip(self, context, session, constraints))]
    fn lookup_type_param_member(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        ty: &InferTy,
        type_param: Symbol,
    ) -> SolveResult {
        let mut solved_metas: Vec<Meta> = Default::default();
        let cause = ConstraintCause::Member(self.node_id);

        // Collect protocol_ids by value to avoid borrowing context.givens
        let candidates: Vec<ProtocolId> = context
            .givens_mut()
            .iter()
            .filter_map(|given| {
                if let Predicate::Conforms {
                    param, protocol_id, ..
                } = given
                    && param == &type_param
                {
                    Some(*protocol_id)
                } else {
                    None
                }
            })
            .collect();

        // Collect all matching protocol methods
        let matching_methods: Vec<(ProtocolId, Symbol)> = candidates
            .iter()
            .filter_map(|protocol_id| {
                session
                    .lookup_member(&(*protocol_id).into(), &self.label)
                    .map(|(req, _source)| (*protocol_id, req))
            })
            .collect();

        if matching_methods.is_empty() {
            return SolveResult::Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        }

        // Register variational choices for ALL type param member accesses.
        // This allows SpecializationPass to resolve the concrete witness.
        let dimension = DimensionId(self.node_id);
        let mut alt_index = 0;

        for (protocol_id, req) in matching_methods.iter() {
            // For each conformance to this protocol, register a choice alternative
            let conformances: Vec<_> = session
                .type_catalog
                .conformances
                .iter()
                .filter(|(key, _)| key.protocol_id == *protocol_id)
                .map(|(key, conf)| (key.conforming_id, conf.witnesses.clone()))
                .collect();

            for (conforming_id, witnesses) in conformances {
                if let Some(witness) = witnesses.get_witness(&self.label, req) {
                    let alternative = ChoiceAlternative {
                        conforming_type: conforming_id,
                        witness_sym: witness,
                        protocol_id: *protocol_id,
                    };

                    session.choices.register_alternative(
                        dimension,
                        AlternativeIndex(alt_index),
                        alternative,
                    );
                    alt_index += 1;
                }
            }
        }

        if alt_index > 0 {
            tracing::debug!(
                "Registered {} variational choices for member {} at {:?}",
                alt_index,
                self.label,
                self.node_id
            );
        }

        // For multiple alternatives, create variational constraints for each one
        // so the resolution phase can eliminate invalid alternatives based on type errors.
        if alt_index > 1 {
            for alt_idx in 0..alt_index {
                let Some(alternative) = session.choices.get_alternative(
                    DimensionId(self.node_id),
                    AlternativeIndex(alt_idx),
                ) else {
                    continue;
                };

                let Some((_, req)) = matching_methods
                    .iter()
                    .find(|(pid, _)| *pid == alternative.protocol_id)
                else {
                    continue;
                };

                let Some(entry) = session.lookup(req) else {
                    continue;
                };

                let config = Configuration::single(dimension, AlternativeIndex(alt_idx));
                let mut group = constraints.copy_group(self.id);
                group.config = config;

                let req_ty = entry.instantiate(self.node_id, constraints, context, session);
                let (req_self, req_func) = consume_self(&req_ty);

                constraints.wants_equals_at_with_cause(
                    self.node_id,
                    req_self,
                    self.receiver.clone(),
                    &group,
                    Some(cause),
                );
                constraints.wants_equals_at_with_cause(
                    self.node_id,
                    req_func,
                    ty.clone(),
                    &group,
                    Some(cause),
                );
            }
        }

        // Unify with first method universally (for single alternative, or as optimistic solution)
        let (protocol_id, req) = &matching_methods[0];
        let Some(entry) = session.lookup(req) else {
            return SolveResult::Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        };

        let req_ty = entry.instantiate(self.node_id, constraints, context, session);
        let (req_self, req_func) = consume_self(&req_ty);

        match unify(&req_self, &self.receiver, context, session).map_err(|e| e.with_cause(cause)) {
            Ok(metas) => solved_metas.extend(metas),
            Err(e) => return SolveResult::Err(e),
        }

        match unify(ty, &req_func, context, session).map_err(|e| e.with_cause(cause)) {
            Ok(metas) => solved_metas.extend(metas),
            Err(e) => return SolveResult::Err(e),
        };

        tracing::trace!(
            "Chose protocol {:?} for member {} at {:?}",
            protocol_id,
            self.label,
            self.node_id
        );

        SolveResult::Solved(solved_metas)
    }

    #[instrument(skip(self, context, session, constraints))]
    fn lookup_static_member(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        nominal_symbol: &Symbol,
    ) -> SolveResult {
        let cause = ConstraintCause::Member(self.node_id);
        let Some(member_sym) = session.lookup_static_member(nominal_symbol, &self.label) else {
            return SolveResult::Defer(DeferralReason::WaitingOnSymbol(*nominal_symbol));
        };

        let mut member_ty = if let Some(entry) = session.lookup(&member_sym) {
            entry.instantiate(self.node_id, constraints, context, session)
        } else {
            return SolveResult::Defer(DeferralReason::WaitingOnSymbol(member_sym));
            // InferTy::Error(
            //     TypeError::MemberNotFound(self.receiver.clone(), self.label.to_string()).into(),
            // )
        };

        if let Symbol::Variant(..) = member_sym {
            let Some(nominal) = session.lookup_nominal(nominal_symbol) else {
                return SolveResult::Defer(DeferralReason::WaitingOnSymbol(*nominal_symbol));
            };

            for param in nominal.type_params.iter() {
                let InferTy::Param(param_id, _) = param else {
                    continue;
                };

                if context
                    .instantiations_mut()
                    .get_ty(&self.node_id, param_id)
                    .is_some()
                {
                    continue;
                }

                let InferTy::Var { id: meta, .. } = session.new_ty_meta_var(context.level()) else {
                    unreachable!();
                };

                // Store the full type param with bounds
                session
                    .reverse_instantiations
                    .ty
                    .insert(meta, param.clone());
                context
                    .instantiations_mut()
                    .insert_ty(self.node_id, *param_id, meta);
                session.type_catalog.instantiations.insert_ty(
                    self.node_id,
                    *param_id,
                    InferTy::Var {
                        id: meta,
                        level: context.level(),
                    },
                );
            }

            let Some(variant) = nominal.variants.get(&self.label) else {
                return SolveResult::Defer(DeferralReason::WaitingOnSymbol(member_sym));
            };

            member_ty = if let Some(enum_entry) = session.lookup(nominal_symbol) {
                let level = context.level();
                let enum_ty = instantiate_ty(
                    self.node_id,
                    enum_entry._as_ty(),
                    context.instantiations_mut(),
                    level,
                );

                match variant.len() {
                    0 => enum_ty,
                    _ => {
                        let instantiated_variants: Vec<_> = variant
                            .iter()
                            .map(|v| {
                                instantiate_ty(
                                    self.node_id,
                                    v.clone(),
                                    context.instantiations_mut(),
                                    level,
                                )
                            })
                            .collect();
                        let instantiated_enum = instantiate_ty(
                            self.node_id,
                            enum_ty,
                            context.instantiations_mut(),
                            level,
                        );
                        curry(instantiated_variants, instantiated_enum, InferRow::Empty.into())
                    }
                }
            } else {
                InferTy::Error(
                    TypeError::TypeNotFound(format!(
                        "{nominal_symbol:?} while looking up static member {:?}",
                        self.label
                    ))
                    .into(),
                )
            };
        }

        match unify(&member_ty, &self.ty, context, session).map_err(|e| e.with_cause(cause)) {
            Ok(vars) => SolveResult::Solved(vars),
            Err(e) => SolveResult::Err(e),
        }
    }

    #[instrument(skip(self, context, session, constraints), fields(label = self.label.to_string()))]
    fn lookup_nominal_member(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        symbol: &Symbol,
        type_args: &[InferTy],
    ) -> SolveResult {
        let mut solved_metas: Vec<Meta> = Default::default();
        let cause = ConstraintCause::Member(self.node_id);

        // First get the nominal - if it doesn't exist yet, defer
        let Some(nominal) = session.lookup_nominal(symbol) else {
            return SolveResult::Defer(DeferralReason::WaitingOnSymbol(*symbol));
        };

        // Try to find a method/variant via lookup_member
        if let Some((member_sym, _source)) = session.lookup_member(symbol, &self.label) {
            match member_sym {
                Symbol::InstanceMethod(..) | Symbol::MethodRequirement(..) => {
                    let Some(entry) = session.lookup(&member_sym) else {
                        return SolveResult::Err(TypeError::MemberNotFound(
                            self.receiver.clone(),
                            self.label.to_string(),
                        ));
                    };

                    let method = entry.instantiate(self.node_id, constraints, context, session);
                    let method = session.apply(method, &mut context.substitutions_mut());
                    let (method_receiver, method_fn) = consume_self(&method);

                    match unify(&method_receiver, &self.receiver, context, session)
                        .map_err(|e| e.with_cause(cause))
                    {
                        Ok(metas) => solved_metas.extend(metas),
                        Err(e) => return SolveResult::Err(e),
                    };

                    match unify(&method_fn, &self.ty, context, session)
                        .map_err(|e| e.with_cause(cause))
                    {
                        Ok(metas) => solved_metas.extend(metas),
                        Err(e) => return SolveResult::Err(e),
                    };

                    return SolveResult::Solved(solved_metas);
                }
                Symbol::Variant(..) => {
                    let Some(values) = nominal
                        .substituted_variant_values(type_args)
                        .get(&self.label)
                        .cloned()
                    else {
                        return SolveResult::Err(TypeError::MemberNotFound(
                            self.receiver.clone(),
                            self.label.to_string(),
                        ));
                    };

                    let constructor_ty = match values.len() {
                        0 => self.receiver.clone(),
                        _ => curry(values, self.receiver.clone(), InferRow::Empty.into()),
                    };

                    let group = constraints.copy_group(self.id);
                    constraints.wants_equals_at_with_cause(
                        self.node_id,
                        constructor_ty,
                        self.ty.clone(),
                        &group,
                        Some(cause),
                    );
                    return SolveResult::Solved(Default::default());
                }
                Symbol::StaticMethod(..) => {
                    return self.lookup_static_member(constraints, context, session, symbol);
                }
                _ => (),
            }
        }

        // If all else fails, see if it's a property
        if let Some(ty) = nominal
            .substitute_properties(type_args)
            .get(&self.label)
            .cloned()
        {
            match unify(&self.ty, &ty, context, session).map_err(|e| e.with_cause(cause)) {
                Ok(vars) => SolveResult::Solved(vars),
                Err(e) => SolveResult::Err(e),
            }
        } else {
            SolveResult::Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ))
        }
    }
}

#[instrument(level = tracing::Level::TRACE, ret)]
pub fn consume_self(method: &InferTy) -> (InferTy, InferTy) {
    assert_matches!(method, InferTy::Func(..), "didn't get func to consume self");
    let (mut params, ret, effects) = uncurry_function(method.clone());
    let method_receiver = params.remove(0);
    if params.is_empty() {
        // We need to make sure there's at least one param or else curry doesn't return a func.
        params.insert(0, InferTy::Void);
    }
    (method_receiver, curry(params, ret, effects.into()))
}
