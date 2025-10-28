use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_row::InferRow,
        infer_ty::{InferTy, Level},
        passes::inference_pass::uncurry_function,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, curry},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
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
        _level: Level,
        next_wants: &mut Wants,
        _substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let receiver = self.receiver.clone();
        let ty = self.ty.clone();

        tracing::debug!(
            "Member::solve receiver={receiver:?}, label={:?}",
            self.label
        );

        if matches!(
            receiver,
            InferTy::Var { .. } | InferTy::Rigid(_) | InferTy::Param(_)
        ) {
            // If we don't know what the receiver is yet, we can't do much
            tracing::debug!("deferring member constraint");
            next_wants.push(Constraint::Member(self.clone()));
            return Ok(false);
        }

        if let InferTy::Record(box row) = &receiver {
            next_wants._has_field(row.clone(), self.label.clone(), ty, self.cause, self.span);
            return Ok(true);
        }

        if let InferTy::Nominal { symbol, box row } = &receiver {
            let Some(member_sym) = session.lookup_member(symbol, &self.label) else {
                return Err(TypeError::MemberNotFound(receiver, self.label.to_string()));
            };

            match member_sym {
                Symbol::InstanceMethod(..) => {
                    let method = session.lookup(&member_sym).unwrap().instantiate(
                        self.node_id,
                        session,
                        Level::default(),
                        next_wants,
                        self.span,
                    );

                    let (method_receiver, method_fn) = consume_self(&method);
                    next_wants.equals(method_receiver, receiver, self.cause, self.span);
                    next_wants.equals(method_fn, self.ty.clone(), self.cause, self.span);
                    return Ok(true);
                }
                Symbol::Variant(..) => {
                    println!("instantiating variant. ty: {receiver:?}");
                    let variant = self.lookup_variant(row).unwrap();
                    let constructor_ty = match variant {
                        InferTy::Void => receiver,
                        InferTy::Tuple(values) => curry(values, receiver),
                        other => curry(vec![other], receiver),
                    };

                    next_wants.equals(constructor_ty, ty, self.cause, self.span);
                    return Ok(true);
                }
                _ => (),
            }

            // If all else fails, see if it's a property
            next_wants._has_field(row.clone(), self.label.clone(), ty, self.cause, self.span);
            return Ok(true);
        }

        Ok(false)
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
