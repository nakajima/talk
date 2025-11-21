use std::assert_matches::assert_matches;

use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_row::InferRow,
        infer_ty::{InferTy, TypeParamId},
        passes::uncurry_function,
        predicate::Predicate,
        solve_context::{Solve, SolveContext},
        type_catalog::MemberWitness,
        type_error::TypeError,
        type_operations::{apply, curry, unify},
        type_session::{MemberSource, TypeSession},
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Member {
    pub node_id: NodeID,
    pub receiver: InferTy,
    pub label: Label,
    pub ty: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl Member {
    pub fn solve(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> Result<bool, TypeError> {
        let receiver = self.receiver.clone();
        let ty = self.ty.clone();

        tracing::debug!(
            "Member::solve receiver={receiver:?}, label={:?} id={:?}",
            self.label,
            self.node_id
        );

        match &receiver {
            InferTy::Var { id, .. } => {
                if let Some(param) = session.reverse_instantiations.ty.get(id)
                    && self.lookup_type_param_member(context, session, &ty, *param) == Ok(true)
                {
                    return Ok(true);
                }

                context.wants.defer(Constraint::Member(self.clone()));
                return Ok(false);
            }
            InferTy::Rigid(id) => {
                let Some(InferTy::Param(type_param_id)) =
                    session.skolem_map.get(&InferTy::Rigid(*id))
                else {
                    unreachable!();
                };

                return self.lookup_type_param_member(context, session, &ty, *type_param_id);
            }
            InferTy::Param(id) => {
                return self.lookup_type_param_member(context, session, &ty, *id);
            }
            InferTy::Constructor { name, .. } => {
                return self.lookup_static_member(context, session, &name.symbol());
            }
            InferTy::Record(box row) => {
                context.wants._has_field(
                    row.clone(),
                    self.label.clone(),
                    ty,
                    self.cause,
                    self.span,
                );
                return Ok(true);
            }
            InferTy::Primitive(symbol) => {
                return self.lookup_nominal_member(context, session, symbol, None);
            }
            InferTy::Nominal { symbol, box row } => {
                return self.lookup_nominal_member(context, session, symbol, Some(row));
            }
            _ => {}
        }

        Ok(false)
    }

    #[allow(clippy::too_many_arguments)]
    #[instrument(skip(self, context, session))]
    fn lookup_type_param_member(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
        ty: &InferTy,
        type_param_id: TypeParamId,
    ) -> Result<bool, TypeError> {
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
                    return Err(TypeError::MemberNotFound(
                        self.receiver.clone(),
                        self.label.to_string(),
                    ));
                };
                let req_ty = entry.instantiate(self.node_id, context, session, self.span);
                let (req_self, req_func) = consume_self(&req_ty);
                context.wants_mut().equals(
                    req_self.clone(),
                    self.receiver.clone(),
                    ConstraintCause::Internal,
                    self.span,
                );

                // Store the method requirement symbol directly as a concrete witness
                // since it represents the protocol method that will be called
                session
                    .type_catalog
                    .member_witnesses
                    .insert(self.node_id, MemberWitness::Requirement(req));

                return unify(ty, &req_func, context, session);
            }
        }

        Ok(false)
    }

    #[instrument(skip(self, context, session))]
    fn lookup_static_member(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
        nominal_symbol: &Symbol,
    ) -> Result<bool, TypeError> {
        let Some(member_sym) = session.lookup_static_member(nominal_symbol, &self.label) else {
            return Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        };

        let mut member_ty = if let Some(entry) = session.lookup(&member_sym) {
            entry.instantiate(self.node_id, context, session, self.span)
        } else {
            InferTy::Error(
                TypeError::MemberNotFound(self.receiver.clone(), self.label.to_string()).into(),
            )
        };

        if let Symbol::Variant(..) = member_sym {
            member_ty = if let Some(enum_entry) = session.lookup(nominal_symbol) {
                let enum_ty = enum_entry.instantiate(self.node_id, context, session, self.span);
                match member_ty {
                    InferTy::Void => enum_ty,
                    InferTy::Tuple(values) => curry(values, enum_ty),
                    other => curry(vec![other], enum_ty),
                }
            } else {
                InferTy::Error(TypeError::TypeNotFound(format!("{nominal_symbol:?}")).into())
            };
        }

        context
            .wants
            .equals(member_ty, self.ty.clone(), self.cause, self.span);
        Ok(true)
    }

    #[instrument(skip(self, context, session))]
    fn lookup_nominal_member(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
        symbol: &Symbol,
        row: Option<&InferRow>,
    ) -> Result<bool, TypeError> {
        let Some((member_sym, source)) = session.lookup_member(symbol, &self.label) else {
            return Err(TypeError::MemberNotFound(
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
                    return Err(TypeError::MemberNotFound(
                        self.receiver.clone(),
                        self.label.to_string(),
                    ));
                };
                let method = entry.instantiate(self.node_id, context, session, self.span);
                let method = apply(method, &mut context.substitutions);
                let (method_receiver, method_fn) = consume_self(&method);

                if let MemberSource::Protocol(protocol_id) = source {
                    tracing::trace!("member found in protocol: {protocol_id:?}");
                }

                context.wants.equals(
                    method_receiver,
                    self.receiver.clone(),
                    self.cause,
                    self.span,
                );

                context
                    .wants
                    .equals(method_fn, self.ty.clone(), self.cause, self.span);
                return Ok(true);
            }
            Symbol::Variant(..) => {
                let Some(row) = row else {
                    return Err(TypeError::ExpectedRow(self.receiver.clone()));
                };

                let Some(variant) = self.lookup_variant(row) else {
                    return Err(TypeError::MemberNotFound(
                        self.receiver.clone(),
                        self.label.to_string(),
                    ));
                };

                let constructor_ty = match variant {
                    InferTy::Void => self.receiver.clone(),
                    InferTy::Tuple(values) => curry(values, self.receiver.clone()),
                    other => curry(vec![other], self.receiver.clone()),
                };

                context
                    .wants
                    .equals(constructor_ty, self.ty.clone(), self.cause, self.span);
                return Ok(true);
            }
            Symbol::StaticMethod(..) => {
                return self.lookup_static_member(context, session, symbol);
            }
            _ => (),
        }

        // If all else fails, see if it's a property
        let Some(row) = row else {
            return Err(TypeError::ExpectedRow(self.receiver.clone()));
        };
        context.wants._has_field(
            row.clone(),
            self.label.clone(),
            self.ty.clone(),
            self.cause,
            self.span,
        );
        Ok(true)
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
