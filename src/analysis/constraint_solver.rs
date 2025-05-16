use std::collections::HashMap;

use super::type_checker::{Constraint, Environment, Ty, TypeChecker, TypeVarID};

#[derive(Debug)]
pub enum ConstraintError {
    TypeConflict(Ty, Ty),
    OccursConflict,
}

pub struct ConstraintSolver<'a> {
    type_checker: &'a mut TypeChecker,
    constraints: &'a mut Vec<Constraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(type_checker: &'a mut TypeChecker, constraints: &'a mut Vec<Constraint>) -> Self {
        Self {
            type_checker,
            constraints,
        }
    }

    pub fn solve(&mut self) -> Result<(), ConstraintError> {
        let mut substitutions = HashMap::<TypeVarID, Ty>::new();

        while let Some(constraint) = self.constraints.pop() {
            match constraint {
                Constraint::Equality(node_id, lhs, rhs) => {
                    let lhs = Self::apply(lhs, &substitutions);
                    let rhs = Self::apply(rhs, &substitutions);

                    Self::unify(
                        &lhs,
                        &rhs,
                        &mut substitutions,
                        self.type_checker.environment.as_ref().unwrap(),
                    )?;

                    self.type_checker.define(node_id, lhs);
                }
            }
        }

        for ty in &mut self
            .type_checker
            .environment
            .as_mut()
            .unwrap()
            .types
            .values_mut()
        {
            *ty = Self::apply(ty.clone(), &substitutions);
        }

        Ok(())
    }

    fn apply(ty: Ty, substitutions: &HashMap<TypeVarID, Ty>) -> Ty {
        match ty {
            Ty::Int => ty,
            Ty::Float => ty,
            Ty::Func(params, returning) => {
                let applied_params = params
                    .iter()
                    .map(|param| Self::apply(param.clone(), substitutions))
                    .collect();

                let applied_return = Self::apply(*returning, substitutions);

                Ty::Func(applied_params, applied_return.into())
            }
            Ty::TypeVar(type_var) => {
                if let Some(ty) = substitutions.get(&type_var) {
                    Self::apply(ty.clone(), substitutions)
                } else {
                    ty
                }
            }
            Ty::Tuple(_items) => todo!(),
        }
    }

    fn unify(
        lhs: &Ty,
        rhs: &Ty,
        substitutions: &mut HashMap<TypeVarID, Ty>,
        env: &Environment,
    ) -> Result<(), ConstraintError> {
        match (lhs, rhs) {
            // They're the same, sick.
            (a, b) if a == b => Ok(()),
            (Ty::TypeVar(v), ty) | (ty, Ty::TypeVar(v)) => {
                if Self::occurs_check(v, ty, substitutions, env) {
                    Err(ConstraintError::OccursConflict)
                } else {
                    substitutions.insert(*v, ty.clone());
                    Ok(())
                }
            }
            _ => todo!(),
        }
    }

    /// Returns true if `v` occurs inside `ty` (after applying current `subs`).
    fn occurs_check(
        v: &TypeVarID,
        ty: &Ty,
        substitutions: &HashMap<TypeVarID, Ty>,
        env: &Environment,
    ) -> bool {
        let ty = Self::apply(ty.clone(), substitutions);
        match ty {
            Ty::TypeVar(ref tv) => tv == v,
            Ty::Func(params, returning) => {
                // check each parameter and the return type
                params
                    .iter()
                    .any(|param| Self::occurs_check(v, &param, substitutions, env))
                    || Self::occurs_check(v, &returning, substitutions, env)
            }

            Ty::Tuple(elem_ids) => elem_ids
                .iter()
                .any(|&nid| Self::occurs_check(v, &env.types[&nid], substitutions, env)),

            _ => false,
        }
    }
}
