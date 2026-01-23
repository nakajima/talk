use tracing::instrument;

use crate::{
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::store::{ConstraintId, ConstraintStore},
        infer_row::{InferRow, RowTail, normalize_row},
        infer_ty::{InferTy, Meta},
        solve_context::SolveContext,
        type_error::TypeError,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RowSubset {
    pub id: ConstraintId,
    pub node_id: Option<NodeID>,
    pub left: InferRow,
    pub right: InferRow,
}

impl RowSubset {
    #[instrument(skip(constraints, context, session))]
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        let left = session.apply_row(self.left.clone(), &mut context.substitutions_mut());
        let right = session.apply_row(self.right.clone(), &mut context.substitutions_mut());

        let (left_fields, left_tail) =
            normalize_row(left.clone(), &mut context.substitutions_mut(), session);
        let (mut right_fields, right_tail) =
            normalize_row(right.clone(), &mut context.substitutions_mut(), session);

        let group = context.group_info();
        let node_id = self.node_id.unwrap_or(NodeID::SYNTHESIZED);

        for (label, left_ty) in left_fields {
            if let Some(right_ty) = right_fields.remove(&label) {
                constraints.wants_equals_at(node_id, left_ty, right_ty, &group);
            } else {
                match right_tail {
                    RowTail::Var(_) => {
                        constraints._has_field(right.clone(), label, left_ty, self.node_id, &group);
                    }
                    RowTail::Empty | RowTail::Param(_) => {
                        return SolveResult::Err(TypeError::MemberNotFound(
                            InferTy::Record(Box::new(right.clone())),
                            label.to_string(),
                        ));
                    }
                }
            }
        }

        match left_tail {
            RowTail::Var(id) => SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Row(id))),
            RowTail::Param(_) => match right_tail {
                RowTail::Empty => SolveResult::Err(TypeError::invalid_unification(
                    InferTy::Record(Box::new(left)),
                    InferTy::Record(Box::new(right)),
                )),
                RowTail::Param(_) | RowTail::Var(_) => SolveResult::Solved(Default::default()),
            },
            RowTail::Empty => SolveResult::Solved(Default::default()),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        compiling::module::ModuleId,
        label::Label,
        types::{
            constraint_solver::{DeferralReason, SolveResult},
            constraints::{row_subset::RowSubset, store::ConstraintStore},
            infer_row::InferRow,
            infer_ty::{InferTy, Level, Meta},
            solve_context::{SolveContext, SolveContextKind},
            type_error::TypeError,
            type_operations::UnificationSubstitutions,
            type_session::TypeSession,
        },
    };

    fn setup() -> (TypeSession, SolveContext) {
        let session = TypeSession::new(
            ModuleId::Current,
            Default::default(),
            Default::default(),
            Default::default(),
        );
        let context = SolveContext::new(
            UnificationSubstitutions::new(session.meta_levels.clone()),
            Level::default(),
            Default::default(),
            SolveContextKind::Normal,
        );
        (session, context)
    }

    fn single_field_row(label: &str, ty: InferTy) -> InferRow {
        InferRow::Extend {
            row: Box::new(InferRow::Empty),
            label: Label::Named(label.into()),
            ty,
        }
    }

    #[test]
    fn solves_when_fields_match() {
        let (mut session, mut context) = setup();
        let mut constraints = ConstraintStore::default();

        let left = single_field_row("a", InferTy::Int);
        let right = single_field_row("a", InferTy::Int);

        let subset = RowSubset {
            id: 0.into(),
            node_id: None,
            left,
            right,
        };

        let result = subset.solve(&mut constraints, &mut context, &mut session);
        assert!(matches!(result, SolveResult::Solved(_)));
    }

    #[test]
    fn errors_when_missing_field_on_closed_rhs() {
        let (mut session, mut context) = setup();
        let mut constraints = ConstraintStore::default();

        let left = single_field_row("a", InferTy::Int);
        let right = InferRow::Empty;

        let subset = RowSubset {
            id: 0.into(),
            node_id: None,
            left,
            right,
        };

        let result = subset.solve(&mut constraints, &mut context, &mut session);
        assert!(matches!(
            result,
            SolveResult::Err(TypeError::MemberNotFound(..))
        ));
    }

    #[test]
    fn defers_when_left_tail_is_open() {
        let (mut session, mut context) = setup();
        let mut constraints = ConstraintStore::default();

        let left = session.new_row_meta_var(Level::default());
        let left_meta = match left {
            InferRow::Var(id) => id,
            _ => unreachable!("expected row var"),
        };

        let subset = RowSubset {
            id: 0.into(),
            node_id: None,
            left,
            right: InferRow::Empty,
        };

        let result = subset.solve(&mut constraints, &mut context, &mut session);
        assert!(matches!(
            result,
            SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Row(id))) if id == left_meta
        ));
    }
}
