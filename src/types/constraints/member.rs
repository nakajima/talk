use std::assert_matches::assert_matches;
use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::{
            constraint::ConstraintCause,
            store::{ConstraintId, ConstraintStore},
        },
        infer_row::InferRow,
        infer_ty::{InferTy, Meta, TypeParamId},
        passes::uncurry_function,
        predicate::Predicate,
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::{curry, instantiate_ty, unify},
        type_session::TypeSession,
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

        match &receiver {
            InferTy::Var { id, .. } => {
                if let Some(param) = session.reverse_instantiations.ty.get(id)
                    && let SolveResult::Solved(metas) =
                        self.lookup_type_param_member(constraints, context, session, &ty, *param)
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
        type_param_id: TypeParamId,
    ) -> SolveResult {
        let mut solved_metas: Vec<Meta> = Default::default();
        let cause = ConstraintCause::Member(self.node_id);
        let mut candidates = vec![];
        for given in &context.givens {
            if let Predicate::Conforms {
                param, protocol_id, ..
            } = given
                && param == &type_param_id
            {
                candidates.push(protocol_id);
            };
        }

        for candidate in candidates {
            if let Some((req, _source)) = session.lookup_member(&candidate.into(), &self.label) {
                let Some(entry) = session.lookup(&req) else {
                    return SolveResult::Err(TypeError::MemberNotFound(
                        self.receiver.clone(),
                        self.label.to_string(),
                    ));
                };

                let req_ty = entry.instantiate(self.node_id, constraints, context, session);
                let (req_self, req_func) = consume_self(&req_ty);

                match unify(&req_self, &self.receiver, context, session)
                    .map_err(|e| e.with_cause(cause))
                {
                    Ok(metas) => {
                        solved_metas.extend(metas);
                    }
                    Err(e) => return SolveResult::Err(e),
                }

                match unify(ty, &req_func, context, session).map_err(|e| e.with_cause(cause)) {
                    Ok(metas) => solved_metas.extend(metas),
                    Err(e) => return SolveResult::Err(e),
                };

                // Record the witness for protocol member access
                session.protocol_members.insert(self.node_id, req);

                return SolveResult::Solved(solved_metas);
            }
        }

        SolveResult::Err(TypeError::MemberNotFound(
            self.receiver.clone(),
            self.label.to_string(),
        ))
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
                    .instantiations
                    .get_ty(&self.node_id, param_id)
                    .is_some()
                {
                    continue;
                }

                let InferTy::Var { id: meta, .. } = session.new_ty_meta_var(context.level) else {
                    unreachable!();
                };

                session.reverse_instantiations.ty.insert(meta, *param_id);
                context
                    .instantiations
                    .insert_ty(self.node_id, *param_id, meta);
                session.type_catalog.instantiations.insert_ty(
                    self.node_id,
                    *param_id,
                    InferTy::Var {
                        id: meta,
                        level: context.level,
                    },
                );
            }

            let Some(variant) = nominal.variants.get(&self.label) else {
                return SolveResult::Defer(DeferralReason::WaitingOnSymbol(member_sym));
            };

            member_ty = if let Some(enum_entry) = session.lookup(nominal_symbol) {
                let enum_ty = instantiate_ty(
                    self.node_id,
                    enum_entry._as_ty(),
                    &context.instantiations,
                    context.level,
                );

                match variant.len() {
                    0 => enum_ty,
                    _ => curry(
                        variant.iter().map(|v| {
                            instantiate_ty(
                                self.node_id,
                                v.clone(),
                                &context.instantiations,
                                context.level,
                            )
                        }),
                        instantiate_ty(
                            self.node_id,
                            enum_ty,
                            &context.instantiations,
                            context.level,
                        ),
                        InferRow::Empty.into(),
                    ),
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
                    let method = session.apply(method, &mut context.substitutions);
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
