use tracing::trace_span;

use crate::{
    type_checker::TypeError,
    types::{
        constraint::{Constraint, ConstraintKind, ConstraintState},
        constraint_set::ConstraintSet,
        ty::{Primitive, Ty},
        type_checking_session::ExprIDTypeMap,
        type_var::TypeVarDefault,
        type_var_context::TypeVarContext,
    },
};

const MAX_FAILED_ATTEMPTS: usize = 4;

pub struct ConstraintSolver<'a> {
    context: &'a mut TypeVarContext,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(context: &'a mut TypeVarContext) -> Self {
        Self { context }
    }

    pub fn solve(
        &mut self,
        constraints: &'a mut ConstraintSet,
    ) -> Result<ExprIDTypeMap, TypeError> {
        let mut result = ExprIDTypeMap::default();
        let mut failed_attempts = 0;

        loop {
            let mut made_progress = false;
            let mut deferred = vec![];

            if constraints.is_empty() {
                break;
            }

            while let Some(mut constraint) = constraints.pop() {
                if !matches!(
                    constraint.state,
                    ConstraintState::Waiting | ConstraintState::Pending
                ) {
                    continue;
                }

                let before = constraint.state;
                self.solve_constraint(&mut constraint, &mut result)?;
                made_progress |= before != constraint.state;

                if constraint.state != ConstraintState::Solved {
                    deferred.push(constraint);
                }
            }

            if failed_attempts == MAX_FAILED_ATTEMPTS {
                break;
            }

            if failed_attempts == MAX_FAILED_ATTEMPTS - 1 {
                self.context.apply_defaults()?;
            }

            if !made_progress {
                failed_attempts += 1;
            }

            for constraint in deferred {
                constraints.add(constraint);
            }
        }

        Ok(result)
    }

    pub fn solve_constraint(
        &mut self,
        constraint: &mut Constraint,
        out: &mut ExprIDTypeMap,
    ) -> Result<(), TypeError> {
        let _s = trace_span!("solve_constraint", constraint = format!("{constraint:?}"));

        match constraint.kind.clone() {
            ConstraintKind::Equals(lhs, rhs) => self.solve_equals(constraint, lhs, rhs, out)?,
            ConstraintKind::LiteralPrimitive(ty, primitive) => {
                self.solve_literal_primitive(constraint, &ty, &primitive, out)?;
            }
            ConstraintKind::RowCombine(expr_id, row_combination) => todo!(),
        }

        Ok(())
    }

    fn solve_equals(
        &mut self,
        constraint: &mut Constraint,
        lhs: Ty,
        rhs: Ty,
        out: &mut ExprIDTypeMap,
    ) -> Result<(), TypeError> {
        let lhs = self.context.resolve(&lhs);
        let rhs = self.context.resolve(&rhs);

        match (lhs, rhs) {
            (Ty::Var(lhs), Ty::Var(rhs)) => {
                self.context.unify(lhs, Ty::Var(rhs))?;
                constraint.state = ConstraintState::Waiting;
                Ok(())
            }
            (Ty::Var(var), ty) | (ty, Ty::Var(var)) => {
                self.context.unify(var, ty.clone())?;
                tracing::trace!("Unifying {var:?} -> {ty:?}");
                constraint.state = ConstraintState::Solved;
                out.insert(constraint.expr_id, ty);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn solve_literal_primitive(
        &mut self,
        constraint: &mut Constraint,
        ty: &Ty,
        primitive: &Primitive,
        out: &mut ExprIDTypeMap,
    ) -> Result<(), TypeError> {
        let resolved = self.context.resolve(ty);

        match resolved {
            Ty::Primitive(p) => {
                if p == *primitive {
                    constraint.state = ConstraintState::Solved;
                    out.insert(constraint.expr_id, Ty::Primitive(*primitive));
                } else {
                    constraint.state = ConstraintState::Error;
                }
            }
            Ty::Var(type_var) => {
                if type_var.accepts(&Ty::Primitive(*primitive)) {
                    constraint.state = ConstraintState::Waiting;
                } else {
                    constraint.state = ConstraintState::Error;
                }
            }
            _ => unreachable!("Internal error"),
        }

        Ok(())
    }
}
