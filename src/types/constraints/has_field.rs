use tracing::instrument;

use crate::{
    label::Label,
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::{constraint::ConstraintCause, store::{ConstraintId, ConstraintStore}},
        infer_row::InferRow,
        infer_ty::{InferTy, Level, Meta},
        type_error::TypeError,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HasField {
    pub id: ConstraintId,
    pub node_id: Option<NodeID>,
    pub row: InferRow,
    pub label: Label,
    pub ty: InferTy,
}

impl HasField {
    #[instrument(skip(constraints))]
    pub fn solve(&self, level: Level, constraints: &mut ConstraintStore) -> SolveResult {
        match &self.row {
            InferRow::Empty(..) => SolveResult::Err(TypeError::MemberNotFound(
                self.ty.clone(),
                self.label.to_string(),
            )),
            InferRow::Param(..) => SolveResult::Err(TypeError::MemberNotFound(
                InferTy::Record(Box::new(self.row.clone())),
                self.label.to_string(),
            )),
            InferRow::Var(id) => {
                // Keep the constraint for the next iteration with the applied row
                SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Row(*id)))
            }
            InferRow::Extend { box row, label, ty } => {
                if self.label == *label {
                    let group = constraints.copy_group(self.id);
                    if let Some(node_id) = self.node_id {
                        constraints.wants_equals_at_with_cause(
                            node_id,
                            self.ty.clone(),
                            ty.clone(),
                            &group,
                            Some(ConstraintCause::Member(node_id)),
                        );
                    } else {
                        constraints.wants_equals(self.ty.clone(), ty.clone());
                    }
                    tracing::trace!("found match for {label:?}");
                    SolveResult::Solved(Default::default())
                } else {
                    constraints._has_field(
                        row.clone(),
                        self.label.clone(),
                        self.ty.clone(),
                        self.node_id,
                        &constraints.copy_group(self.id),
                    );
                    SolveResult::Solved(Default::default())
                }
            }
        }
    }
}
