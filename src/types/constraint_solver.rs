use std::collections::BTreeMap;

use tracing::trace_span;

use crate::{
    type_checker::TypeError,
    types::{
        constraint::{Constraint, ConstraintCause, ConstraintKind, ConstraintState},
        constraint_set::ConstraintSet,
        row::{ClosedRow, Row},
        ty::{Primitive, Ty},
        type_checking_session::ExprIDTypeMap,
        type_var::{TypeVar, TypeVarKind},
        type_var_context::TypeVarContext,
    },
};

const MAX_FAILED_ATTEMPTS: usize = 4;

pub struct ConstraintSolver<'a> {
    context: &'a mut TypeVarContext,
    constraints: &'a mut ConstraintSet,
    record_fields: BTreeMap<TypeVar, BTreeMap<String, Ty>>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(context: &'a mut TypeVarContext, constraints: &'a mut ConstraintSet) -> Self {
        Self {
            context,
            constraints,
            record_fields: Default::default(),
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
                type_args,
                returning,
            } => {
                self.solve_call(constraint, callee, type_args, args, returning, out)?;
            }
            ConstraintKind::HasField { record, label, ty } => {
                self.solve_has_field(constraint, &record, label, ty)?;
            }
            ConstraintKind::RowClosed { record } => {
                self.solve_row_closed(constraint, &record)?;
            }
            #[allow(clippy::todo)]
            ConstraintKind::RowCombine(..) => todo!(),
        }

        Ok(())
    }

    fn solve_has_field(
        &mut self,
        constraint: &mut Constraint,
        record: &Ty,
        label: String,
        ty: Ty,
    ) -> Result<(), TypeError> {
        let record = self.context.resolve(record);

        let Ty::Var(var) = record else {
            return Err(TypeError::Unknown(format!("{record:?} can't have fields",)));
        };

        if let Some(existing) = self.record_fields.entry(var).or_default().get(&label) {
            self.context.unify_ty_ty(existing, &ty)?;
        } else {
            self.record_fields.entry(var).or_default().insert(label, ty);
        }

        constraint.state = ConstraintState::Solved;

        Ok(())
    }

    fn solve_row_closed(
        &mut self,
        constraint: &mut Constraint,
        record: &Ty,
    ) -> Result<(), TypeError> {
        if self
            .constraints
            .row_constraints_for(record)?
            .iter()
            .all(|c| c.is_solved())
        {
            let Ty::Var(var) = record else {
                return Err(TypeError::Unknown("Did not get var".to_string()));
            };

            // Gather the fields
            let Some(fields) = self.record_fields.remove(var) else {
                return Err(TypeError::Unknown("Did not get fields".to_string()));
            };

            let mut labels = vec![];
            let mut values = vec![];

            for (label, ty) in fields.into_iter() {
                labels.push(label);
                values.push(self.context.resolve(&ty));
            }

            self.context.unify_var_ty(
                *var,
                Ty::Product(Row::Closed(ClosedRow {
                    fields: labels,
                    values,
                })),
            )?;

            constraint.state = ConstraintState::Solved;

            return Ok(());
        }

        // We don't have enough yet
        constraint.state = ConstraintState::Waiting;

        Ok(())
    }

    fn solve_call(
        &mut self,
        constraint: &mut Constraint,
        callee: Ty,
        _type_args: Vec<Ty>,
        args: Vec<Ty>,
        returning: Ty,
        out: &mut ExprIDTypeMap,
    ) -> Result<(), TypeError> {
        let callee = self.context.resolve(&callee);

        let (params, returns, generic_constraints) = match callee {
            Ty::Func { params, returns, generic_constraints } => (params, *returns, generic_constraints),
            Ty::Var(_) => {
                let params = args
                    .iter()
                    .map(|_| Ty::Var(self.context.new_var(TypeVarKind::None)))
                    .collect();

                let returns = Ty::Var(self.context.new_var(TypeVarKind::None));

                (params, returns, vec![])
            }
            _ => {
                constraint.state = ConstraintState::Error(TypeError::Unknown(
                    "Can't call non-func type".to_string(),
                ));

                return Err(TypeError::Unknown("Can't call non-func type".to_string()));
            }
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
            let mut substitutions = Default::default();

            out.insert(constraint.expr_id, returning.clone());

            for (param, arg) in params.iter().zip(args.iter()) {
                let param = param.instantiate(self.context, &mut substitutions);

                let id = self.constraints.next_id();
                let child = Constraint {
                    id,
                    expr_id: constraint.expr_id, // TODO: It'd be nicer to use the arg id
                    cause: ConstraintCause::Call,
                    kind: ConstraintKind::Equals(param.clone(), arg.clone()),
                    parent: Some(constraint.id),
                    children: vec![],
                    state: ConstraintState::Pending,
                };

                self.constraints.add(child);
                constraint.children.push(id);
            }

            let returns = returns.instantiate(self.context, &mut substitutions);
            let id = self.constraints.next_id();
            let child = Constraint {
                id,
                expr_id: constraint.expr_id, // TODO: It'd be nicer to use the ret id
                cause: ConstraintCause::Call,
                kind: ConstraintKind::Equals(returns.clone(), returning.clone()),
                parent: Some(constraint.id),
                children: vec![],
                state: ConstraintState::Pending,
            };
            self.constraints.add(child);
            constraint.children.push(id);

            // Add generic constraints as children
            for generic_constraint in generic_constraints {
                let instantiated = generic_constraint.instantiate(self.context, &mut substitutions);
                let id = self.constraints.next_id();
                let child = Constraint {
                    id,
                    expr_id: constraint.expr_id,
                    cause: ConstraintCause::Call,
                    kind: instantiated,
                    parent: Some(constraint.id),
                    children: vec![],
                    state: ConstraintState::Pending,
                };
                self.constraints.add(child);
                constraint.children.push(id);
            }

            constraint.state = ConstraintState::Waiting;
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
                // Determine which type var should constrain the other based on specificity
                let (to_unify, with) = if lhs.kind.is_more_specific_than(&rhs.kind) {
                    (rhs, lhs)
                } else {
                    (lhs, rhs)
                };
                
                self.context.unify_var_ty(to_unify, Ty::Var(with))?;
                constraint.state = ConstraintState::Waiting;
                Ok(())
            }
            (Ty::Var(var), ty) | (ty, Ty::Var(var)) => {
                // Check if the type variable can accept this type
                if !var.accepts(&ty) {
                    constraint.state = ConstraintState::Error(TypeError::Mismatch(
                        format!("{var:?}"),
                        format!("{ty:?}")
                    ));
                    return Err(TypeError::Mismatch(
                        format!("{var:?}"),
                        format!("{ty:?}")
                    ));
                }
                
                self.context.unify_var_ty(var, ty.clone())?;
                tracing::trace!("Unifying {var:?} -> {ty:?}");
                constraint.state = ConstraintState::Solved;
                out.insert(constraint.expr_id, ty);
                Ok(())
            }
            (Ty::Primitive(p1), Ty::Primitive(p2)) if p1 == p2 => {
                constraint.state = ConstraintState::Solved;
                out.insert(constraint.expr_id, Ty::Primitive(p1));
                Ok(())
            }
            (lhs_ty, rhs_ty) => {
                constraint.state = ConstraintState::Error(TypeError::Mismatch(
                    format!("{lhs_ty:?}"),
                    format!("{rhs_ty:?}")
                ));
                Err(TypeError::Mismatch(format!("{lhs_ty:?}"), format!("{rhs_ty:?}")))
            }
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
                    self.context.unify_ty_ty(ty, &Ty::Primitive(*primitive))?;
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
