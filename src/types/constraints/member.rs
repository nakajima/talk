use std::assert_matches::assert_matches;

use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::store::{ConstraintId, ConstraintStore},
        infer_row::InferRow,
        infer_ty::{InferTy, Meta, TypeParamId},
        passes::uncurry_function,
        predicate::Predicate,
        solve_context::SolveContext,
        type_catalog::MemberWitness,
        type_error::TypeError,
        type_operations::{curry, unify},
        type_session::{MemberSource, TypeSession},
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
                let Some(InferTy::Param(type_param_id)) =
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
            InferTy::Param(id) => {
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
                    &constraints.copy_group(self.id),
                );
                return SolveResult::Solved(Default::default());
            }
            InferTy::Primitive(symbol) => {
                return self.lookup_nominal_member(constraints, context, session, symbol, None);
            }
            InferTy::Nominal { symbol, box row } => {
                return self.lookup_nominal_member(
                    constraints,
                    context,
                    session,
                    symbol,
                    Some(row),
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

                match unify(&req_self, &self.receiver, context, session) {
                    Ok(metas) => {
                        solved_metas.extend(metas);
                    }
                    Err(e) => return SolveResult::Err(e),
                }

                // Store the method requirement symbol directly as a concrete witness
                // since it represents the protocol method that will be called
                session.type_catalog.member_witnesses.insert(
                    self.node_id,
                    MemberWitness::Requirement(req, req_self.clone()),
                );

                match unify(ty, &req_func, context, session) {
                    Ok(metas) => solved_metas.extend(metas),
                    Err(e) => return SolveResult::Err(e),
                };

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
        let Some(member_sym) = session.lookup_static_member(nominal_symbol, &self.label) else {
            return SolveResult::Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        };

        let mut member_ty = if let Some(entry) = session.lookup(&member_sym) {
            entry.instantiate(self.node_id, constraints, context, session)
        } else {
            InferTy::Error(
                TypeError::MemberNotFound(self.receiver.clone(), self.label.to_string()).into(),
            )
        };

        if let Symbol::Variant(..) = member_sym {
            member_ty = if let Some(enum_entry) = session.lookup(nominal_symbol) {
                let enum_ty = enum_entry.instantiate(self.node_id, constraints, context, session);
                match member_ty {
                    InferTy::Void => enum_ty,
                    InferTy::Tuple(values) => curry(values, enum_ty),
                    other => curry(vec![other], enum_ty),
                }
            } else {
                InferTy::Error(TypeError::TypeNotFound(format!("{nominal_symbol:?}")).into())
            };
        }

        match unify(&member_ty, &self.ty, context, session) {
            Ok(vars) => SolveResult::Solved(vars),
            Err(e) => SolveResult::Err(e),
        }
    }

    #[instrument(skip(self, context, session, constraints))]
    fn lookup_nominal_member(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        symbol: &Symbol,
        row: Option<&InferRow>,
    ) -> SolveResult {
        let mut solved_metas: Vec<Meta> = Default::default();
        let Some((member_sym, source)) = session.lookup_member(symbol, &self.label) else {
            return SolveResult::Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        };

        session
            .type_catalog
            .member_witnesses
            .insert(self.node_id, MemberWitness::Concrete(member_sym));

        match member_sym {
            Symbol::InstanceMethod(..) => {
                let Some(entry) = session.lookup(&member_sym) else {
                    return SolveResult::Err(TypeError::MemberNotFound(
                        self.receiver.clone(),
                        self.label.to_string(),
                    ));
                };
                let method = entry.instantiate(self.node_id, constraints, context, session);
                let method = session.apply(method, &mut context.substitutions);
                let (method_receiver, method_fn) = consume_self(&method);

                if let MemberSource::Protocol(protocol_id) = source {
                    tracing::trace!("member found in protocol: {protocol_id:?}");
                }

                match unify(&method_receiver, &self.receiver, context, session) {
                    Ok(metas) => solved_metas.extend(metas),
                    Err(e) => return SolveResult::Err(e),
                };

                match unify(&method_fn, &self.ty, context, session) {
                    Ok(metas) => solved_metas.extend(metas),
                    Err(e) => return SolveResult::Err(e),
                };

                return SolveResult::Solved(solved_metas);
            }
            Symbol::Variant(..) => {
                let Some(row) = row else {
                    return SolveResult::Err(TypeError::ExpectedRow(self.receiver.clone()));
                };

                let Some(variant) = self.lookup_variant(row) else {
                    return SolveResult::Err(TypeError::MemberNotFound(
                        self.receiver.clone(),
                        self.label.to_string(),
                    ));
                };

                let constructor_ty = match variant {
                    InferTy::Void => self.receiver.clone(),
                    InferTy::Tuple(values) => curry(values, self.receiver.clone()),
                    other => curry(vec![other], self.receiver.clone()),
                };

                constraints.wants_equals(constructor_ty, self.ty.clone());
                return SolveResult::Solved(Default::default());
            }
            Symbol::StaticMethod(..) => {
                return self.lookup_static_member(constraints, context, session, symbol);
            }
            _ => (),
        }

        // If all else fails, see if it's a property
        let Some(row) = row else {
            return SolveResult::Err(TypeError::ExpectedRow(self.receiver.clone()));
        };
        constraints._has_field(
            row.clone(),
            self.label.clone(),
            self.ty.clone(),
            &constraints.copy_group(self.id),
        );
        SolveResult::Solved(Default::default())
    }

    fn lookup_variant(&self, row: &InferRow) -> Option<InferTy> {
        if let InferRow::Extend { row, label, ty } = row {
            if *label == self.label {
                return Some(ty.clone());
            }

            return self.lookup_variant(row);
        }

        None
    }
}

#[instrument(level = tracing::Level::TRACE, ret)]
pub fn consume_self(method: &InferTy) -> (InferTy, InferTy) {
    assert_matches!(method, InferTy::Func(..), "didn't get func to consume self");
    let (mut params, ret) = uncurry_function(method.clone());
    let method_receiver = params.remove(0);
    if params.is_empty() {
        // We need to make sure there's at least one param or else curry doesn't return a func.
        params.insert(0, InferTy::Void);
    }
    (method_receiver, curry(params, ret))
}
