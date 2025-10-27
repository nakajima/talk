use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_row::{InferRow, RowTail, normalize_row},
        infer_ty::{InferTy, Level},
        passes::{dependencies_pass::ConformanceRequirement, old_inference_pass::curry},
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, instantiate_ty, unify,
        },
        type_session::{TypeDefKind, TypeSession},
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

        if matches!(
            receiver,
            InferTy::Var { .. } | InferTy::Rigid(_) | InferTy::Param(_)
        ) {
            // If we don't know what the receiver is yet, we can't do much
            tracing::debug!("deferring member constraint");
            next_wants.push(Constraint::Member(self.clone()));
            return Ok(false);
        }

        match &receiver {
            InferTy::Nominal { box row, .. } => {
                next_wants._has_field(
                    row.clone(),
                    self.label.clone(),
                    self.ty.clone(),
                    self.cause,
                    self.span,
                );
                Ok(true)
            }
            _ => todo!(),
        }
    }
}
