use std::assert_matches::assert_matches;

use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::{
            constraint::{Constraint, ConstraintCause},
            projection::Projection,
        },
        infer_row::InferRow,
        infer_ty::{InferTy, TypeParamId},
        passes::uncurry_function,
        predicate::Predicate,
        solve_context::{Solve, SolveContext},
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
            "Member::solve receiver={receiver:?}, label={:?}",
            self.label
        );

        match &receiver {
            InferTy::Var { id, .. } => {
                if let Some(param) = session.reverse_instantiations.ty.get(id)
                    && self.lookup_type_param_member(context, session, &ty, *param) == Ok(true)
                {
                    return Ok(true);
                }

                tracing::debug!("deferring member constraint: {self:?}");
                context.wants.push(Constraint::Member(self.clone()));
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

        // // after instantiating the requirement scheme:
        // let req_ty = requirement_entry.instantiate(node_id, context, self.session, span);

        // // peel off self: func(Self) -> Ret  ==>  (Self, func(Void) -> Ret)
        // let (req_self_ty, consumed_fun) = consume_self(&req_ty);
        // let ret_ty = consumed_fun.ret_ty().clone(); // however you fetch the return

        // // 1) Self must match the receiver
        // context.wants_mut().equals(
        //     req_self_ty.clone(),
        //     receiver.clone(),
        //     ConstraintCause::Internal,
        //     span,
        // );

        // // 2) The *associated type result* is the method's *return*:
        // context.wants_mut().projection(
        //     node_id,
        //     receiver.clone(),
        //     label.clone(),  // "T"
        //     ret_ty.clone(), // <-- use the return, not the member var
        //     ConstraintCause::Member(node_id),
        //     span,
        // );

        // // 3) The *member expression* denotes the consumed function value:
        // context
        //     .wants_mut()
        //     .equals(member_ty_var, consumed_fun, ConstraintCause::Internal, span);

        for candidate in candidates {
            if let Some((req, _source)) = session.lookup_member(&candidate.into(), &self.label) {
                let entry = session.lookup(&req).unwrap();
                let req_ty = entry.instantiate(self.node_id, context, session, self.span);
                let (req_self, req_func) = consume_self(&req_ty);
                context.wants_mut().equals(
                    req_self,
                    self.receiver.clone(),
                    ConstraintCause::Internal,
                    self.span,
                );

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
        symbol: &Symbol,
    ) -> Result<bool, TypeError> {
        let Some(member_sym) = session.lookup_static_member(symbol, &self.label) else {
            return Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        };

        let entry = session.lookup(&member_sym).unwrap();
        let mut member_ty = entry.instantiate(self.node_id, context, session, self.span);

        if let Symbol::Variant(..) = member_sym {
            let enum_ty = session.lookup(symbol).unwrap().instantiate(
                self.node_id,
                context,
                session,
                self.span,
            );
            member_ty = match member_ty {
                InferTy::Void => enum_ty,
                InferTy::Tuple(values) => curry(values, enum_ty),
                other => curry(vec![other], enum_ty),
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

        match member_sym {
            Symbol::InstanceMethod(..) => {
                let entry = session.lookup(&member_sym).unwrap();
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

                let variant = self.lookup_variant(row).unwrap();
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
                todo!()
            }
            _ => (),
        }

        // match member_sym {
        //     Symbol::InstanceMethod(..) => {
        //         let entry = session
        //             .elaborated_types
        //             .nominals
        //             .get(symbol)
        //             .unwrap()
        //             .members
        //             .methods
        //             .get(&self.label)
        //             .unwrap();
        //         let entry = session.materialize_entry(entry.clone(), Level::default(), next_wants);
        //         let method = entry.instantiate(
        //             self.node_id,
        //             session,
        //             Level::default(),
        //             next_wants,
        //             self.span,
        //         );

        //         println!("method: {method:?}");
        //         let (method_receiver, method_fn) = consume_self(&method);
        //         println!("receiver: {:?}", self.receiver);
        //         println!("ty: {:?}", self.ty);
        //         println!("method_receiver: {method_receiver:?}");
        //         println!("method_fn: {method_fn:?}");
        //         next_wants.equals(
        //             method_receiver,
        //             self.receiver.clone(),
        //             self.cause,
        //             self.span,
        //         );
        //         next_wants.equals(method_fn, self.ty.clone(), self.cause, self.span);
        //         return Ok(true);
        //     }
        //     Symbol::Variant(..) => {
        //         println!("instantiating variant. ty: {:?}", self.ty);
        //         let variant = self.lookup_variant(row).unwrap();
        //         let constructor_ty = match variant {
        //             InferTy::Void => self.receiver.clone(),
        //             InferTy::Tuple(values) => curry(values, self.receiver.clone()),
        //             other => curry(vec![other], self.receiver.clone()),
        //         };

        //         next_wants.equals(constructor_ty, self.ty.clone(), self.cause, self.span);
        //         return Ok(true);
        //     }
        //     _ => (),
        // }

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
