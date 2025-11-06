use indexmap::IndexSet;
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
        predicate::Predicate,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, curry, unify},
        type_session::{MemberSource, TypeSession},
        wants::Wants,
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
        session: &mut TypeSession,
        level: Level,
        givens: &IndexSet<Predicate<InferTy>>,
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
            InferTy::Var { id, .. } => {
                if let Some(param) = session.reverse_instantiations.ty.get(id) {
                    println!("well we have a param: {param:?}");
                    return self.lookup_type_param_member(
                        &ty,
                        *param,
                        session,
                        level,
                        givens,
                        next_wants,
                        substitutions,
                    );
                }

                tracing::debug!("deferring member constraint: {self:?}");
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
                    givens,
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
                    givens,
                    next_wants,
                    substitutions,
                );
            }
            InferTy::Constructor { name, .. } => {
                return self.lookup_static_member(
                    &name.symbol(),
                    session,
                    next_wants,
                    level,
                    substitutions,
                );
            }
            InferTy::Record(box row) => {
                next_wants._has_field(row.clone(), self.label.clone(), ty, self.cause, self.span);
                return Ok(true);
            }
            InferTy::Nominal { symbol, box row } => {
                return self.lookup_nominal_member(
                    symbol,
                    row,
                    session,
                    next_wants,
                    level,
                    substitutions,
                );
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
        givens: &IndexSet<Predicate<InferTy>>,
        wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        println!("GIVENS: {givens:?}");
        let mut candidates = vec![];
        for given in givens {
            if let Predicate::Conforms {
                param, protocol_id, ..
            } = given
                && param == &type_param_id
            {
                candidates.push(protocol_id);
            };
        }

        for candidate in candidates {
            if let Some((req, source)) = session.lookup_member(&candidate.into(), &self.label) {
                println!("found a member lol: {req:?}, source: {source:?}");
                let entry = session.lookup(&req).unwrap();
                let req_ty = entry
                    .instantiate(self.node_id, session, level, wants, self.span)
                    .0;
                return unify(ty, &req_ty, substitutions, session);
            }
        }

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

        // }

        panic!("didn't find a conformance to find a member in for {self:?}");
    }

    #[instrument(skip(self, session, next_wants))]
    fn lookup_static_member(
        &self,
        symbol: &Symbol,
        session: &mut TypeSession,
        next_wants: &mut Wants,
        level: Level,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let Some(member_sym) = session.lookup_static_member(symbol, &self.label) else {
            return Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        };

        let entry = session.lookup(&member_sym).unwrap();
        let (mut member_ty, instantiation_substitutions) =
            entry.instantiate(self.node_id, session, level, next_wants, self.span);

        if let Symbol::Variant(..) = member_sym {
            let enum_ty = session
                .lookup(symbol)
                .unwrap()
                .instantiate_with_substitutions(
                    self.node_id,
                    session,
                    level,
                    next_wants,
                    self.span,
                    instantiation_substitutions,
                )
                .0;
            member_ty = match member_ty {
                InferTy::Void => enum_ty,
                InferTy::Tuple(values) => curry(values, enum_ty),
                other => curry(vec![other], enum_ty),
            };
        }

        println!("LOOKUP STATIC MEMBER: {symbol:?} . {member_sym:?}");

        next_wants.equals(member_ty, self.ty.clone(), self.cause, self.span);
        Ok(true)
    }

    #[instrument(skip(self, session, next_wants))]
    fn lookup_nominal_member(
        &self,
        symbol: &Symbol,
        row: &InferRow,
        session: &mut TypeSession,
        next_wants: &mut Wants,
        level: Level,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let Some((member_sym, source)) = session.lookup_member(symbol, &self.label) else {
            return Err(TypeError::MemberNotFound(
                self.receiver.clone(),
                self.label.to_string(),
            ));
        };

        println!("MEMBER SYM: {row:?} {member_sym:?} {source:?}");

        match member_sym {
            Symbol::InstanceMethod(..) => {
                let entry = session.lookup(&member_sym).unwrap();
                let method = entry
                    .instantiate(self.node_id, session, level, next_wants, self.span)
                    .0;
                let (method_receiver, method_fn) = consume_self(&method);

                println!("receiver: {:?}", self.receiver);
                println!("ty: {:?}", self.ty);
                println!("method_receiver: {method_receiver:?}");
                println!("method_fn: {method_fn:?}");

                if let MemberSource::Protocol(protocol_id) = source {}

                next_wants.equals(
                    method_receiver,
                    self.receiver.clone(),
                    self.cause,
                    self.span,
                );

                next_wants.equals(method_fn, self.ty.clone(), self.cause, self.span);
                return Ok(true);
            }
            Symbol::Variant(..) => {
                println!("instantiating variant. ty: {:?}", self.ty);
                let variant = self.lookup_variant(row).unwrap();
                let constructor_ty = match variant {
                    InferTy::Void => self.receiver.clone(),
                    InferTy::Tuple(values) => curry(values, self.receiver.clone()),
                    other => curry(vec![other], self.receiver.clone()),
                };

                next_wants.equals(constructor_ty, self.ty.clone(), self.cause, self.span);
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
