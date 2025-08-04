use tracing::trace_span;

use crate::{
    type_checker::TypeError,
    types::{
        constraint::{Constraint, ConstraintCause, ConstraintKind, ConstraintState},
        constraint_set::{ConstraintId, ConstraintSet},
        ty::{Primitive, Ty},
        type_checking_session::ExprIDTypeMap,
        type_var_context::TypeVarContext,
    },
};

const MAX_FAILED_ATTEMPTS: usize = 4;

pub struct ConstraintSolver<'a> {
    context: &'a mut TypeVarContext,
    constraints: &'a mut ConstraintSet,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(context: &'a mut TypeVarContext, constraints: &'a mut ConstraintSet) -> Self {
        Self {
            context,
            constraints,
        }
    }

    pub fn solve(&mut self) -> Result<ExprIDTypeMap, TypeError> {
        let mut result = ExprIDTypeMap::default();
        let mut failed_attempts = 0;

        loop {
            let mut made_progress = false;
            let mut deferred = vec![];

            if self.constraints.is_empty() {
                break;
            }

            while let Some(mut constraint) = self.constraints.pop() {
                if !matches!(
                    constraint.state,
                    ConstraintState::Waiting | ConstraintState::Pending
                ) {
                    continue;
                }

                let before = constraint.state.clone();
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
                self.constraints.add(constraint);
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
            ConstraintKind::Call {
                callee,
                args,
                returning,
            } => {
                self.solve_call(constraint, callee, args, returning, out)?;
            }
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => todo!(),
        }

        Ok(())
    }

    fn solve_call(
        &mut self,
        constraint: &mut Constraint,
        callee: Ty,
        args: Vec<Ty>,
        returning: Ty,
        out: &mut ExprIDTypeMap,
    ) -> Result<(), TypeError> {
        let Ty::Func { params, box returns } = callee else {
            // We don't have enough information
            return Ok(());
        };

        if args.len() != params.len() {
            constraint.state = ConstraintState::Error(TypeError::ArgumentError(format!(
                "Expected {} args, got {}",
                params.len(),
                args.len()
            )));
        }

        // If it's the first time this constraint has been attempted, spawn the child
        // constraints
        if constraint.state == ConstraintState::Pending {
            out.insert(constraint.expr_id, returning.clone());
            for (param, arg) in params.iter().zip(args.iter()) {
                let id = self.constraints.next_id();
                let child = Constraint {
                    id,
                    expr_id: constraint.expr_id, // TODO: It'd be nicer to use the arg id
                    cause: ConstraintCause::Call,
                    kind: ConstraintKind::Equals(param.clone(), arg.clone()),
                    children: vec![],
                    state: ConstraintState::Pending,
                };
                self.constraints.add(child);
            }

            let id = self.constraints.next_id();
            let child = Constraint {
                id,
                expr_id: constraint.expr_id, // TODO: It'd be nicer to use the ret id
                cause: ConstraintCause::Call,
                kind: ConstraintKind::Equals(returns.clone(), returning.clone()),
                children: vec![],
                state: ConstraintState::Pending,
            };
            self.constraints.add(child);
        } else if constraint.state == ConstraintState::Waiting
            && constraint
                .children
                .iter()
                .all(|c| self.constraints.state_for(c) == Some(ConstraintState::Solved))
        {
            constraint.state = ConstraintState::Solved;
        } else {
            constraint.state = ConstraintState::Waiting;
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
                    constraint.state = ConstraintState::Error(TypeError::Mismatch(
                        primitive.to_string(),
                        p.to_string(),
                    ));
                }
            }
            Ty::Var(type_var) => {
                if type_var.accepts(&Ty::Primitive(*primitive)) {
                    constraint.state = ConstraintState::Waiting;
                } else {
                    constraint.state =
                        ConstraintState::Error(TypeError::Unknown("Unexpected type".to_string()));
                }
            }
            _ => unreachable!("Internal error"),
        }

        Ok(())
    }
}
