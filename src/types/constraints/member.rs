use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_row::InferRow,
        infer_ty::{InferTy, Level, TypeParamId},
        passes::uncurry_function,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, curry, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq)]
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
        session: &mut TypeSession,
        level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let receiver = self.receiver.clone();
        let ty = self.ty.clone();

        tracing::debug!(
            "Member::solve receiver={receiver:?}, label={:?}",
            self.label
        );

        match &receiver {
            InferTy::Var { .. } => {
                tracing::debug!("deferring member constraint");
                next_wants.push(Constraint::Member(self.clone()));
                return Ok(false);
            }
            InferTy::Rigid(id) => {
                let Some(InferTy::Param(type_param_id)) =
                    session.skolem_map.get(&InferTy::Rigid(*id))
                else {
                    unreachable!();
                };

                return self.lookup_type_param_member(
                    &ty,
                    *type_param_id,
                    session,
                    level,
                    next_wants,
                    substitutions,
                );
            }
            InferTy::Param(id) => {
                return self.lookup_type_param_member(
                    &ty,
                    *id,
                    session,
                    level,
                    next_wants,
                    substitutions,
                );
            }
            InferTy::Record(box row) => {
                next_wants._has_field(row.clone(), self.label.clone(), ty, self.cause, self.span);
                return Ok(true);
            }
            InferTy::Nominal { symbol, box row } => {
                return self.lookup_nominal_member(symbol, row, session, next_wants);
            }
            _ => {}
        }

        Ok(false)
    }

    #[allow(clippy::too_many_arguments)]
    #[instrument(skip(self, session, substitutions, wants))]
    fn lookup_type_param_member(
        &self,
        ty: &InferTy,
        type_param_id: TypeParamId,
        session: &mut TypeSession,
        level: Level,
        wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        // let conformances = session
        //     .elaborated_types
        //     .type_param_conformances
        //     .get(&type_param_id)
        //     .cloned()
        //     .unwrap_or_default();
        // println!("hi conformances {conformances:?}");
        // for conformance in conformances {
        //     println!(
        //         "cat: {:?}",
        //         session
        //             .type_catalog
        //             .method_requirements
        //             .get(&conformance.0.into())
        //     );
        //     if let Some(req) = session.lookup_member(&conformance.0.into(), &self.label) {
        //         println!("found a member lol: {req:?}");
        //         let entry = session.lookup(&req).unwrap();
        //         let req_ty = entry.instantiate(self.node_id, session, level, wants, self.span);
        //         return unify(ty, &req_ty, substitutions, session);
        //     }
        // }

        panic!("didn't find a conformance to find a member in");
    }

    #[instrument(skip(self, session, next_wants))]
    fn lookup_nominal_member(
        &self,
        symbol: &Symbol,
        row: &InferRow,
        session: &mut TypeSession,
        next_wants: &mut Wants,
    ) -> Result<bool, TypeError> {
        let Some(member_sym) = session.lookup_member(symbol, &self.label) else {
            return Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        };

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
        next_wants._has_field(
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

fn consume_self(method: &InferTy) -> (InferTy, InferTy) {
    let (mut params, ret) = uncurry_function(method.clone());
    let method_receiver = params.remove(0);
    if params.is_empty() {
        // We need to make sure there's at least one param or else curry doesn't return a func.
        params.insert(0, InferTy::Void);
    }
    (method_receiver, curry(params, ret))
}
