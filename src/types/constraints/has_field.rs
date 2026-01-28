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
        infer_row::Row,
        infer_ty::{Meta, Ty},
        solve_context::SolveContext,
        type_error::TypeError,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HasField {
    pub id: ConstraintId,
    pub node_id: Option<NodeID>,
    pub row: Row,
    pub label: Label,
    pub ty: Ty,
}

impl HasField {
    #[instrument(skip(constraints, context, session))]
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        match &self.row {
            Row::Empty => {
                // Check if this is an effect constraint - give a better error message
                if let Label::_Symbol(Symbol::Effect(_)) = &self.label {
                    SolveResult::Err(TypeError::UnhandledEffect(self.label.to_string()))
                } else {
                    SolveResult::Err(TypeError::MemberNotFound(
                        self.ty.clone(),
                        self.label.to_string(),
                    ))
                }
            }
            Row::Param(..) => SolveResult::Err(TypeError::MemberNotFound(
                Ty::Record(None, Box::new(self.row.clone())),
                self.label.to_string(),
            )),
            Row::Var(id) => {
                // For effect constraints, extend the row immediately.
                // For other constraints (records), defer until more info is available.
                if let Label::_Symbol(Symbol::Effect(_)) = &self.label {
                    // Extend the row with this effect by creating a fresh tail
                    let tail = session.new_row_meta_var(context.level());

                    // Build the extended row: Extend { row: tail, label, ty }
                    let extended = Row::Extend {
                        row: Box::new(tail),
                        label: self.label.clone(),
                        ty: self.ty.clone(),
                    };

                    // Unify the original var with the extended row
                    let canon_id = session.canon_row(*id);
                    context.substitutions_mut().row.insert(canon_id, extended);

                    SolveResult::Solved(vec![Meta::Row(canon_id)])
                } else {
                    // For non-effect HasField, defer until row is resolved
                    SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Row(*id)))
                }
            }
            Row::Extend { box row, label, ty } => {
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
