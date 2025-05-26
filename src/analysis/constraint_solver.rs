use std::collections::HashMap;

use crate::{SourceFile, Typed, parser::ExprID};

use super::type_checker::{Ty, TypeVarID};

#[derive(Debug)]
pub enum ConstraintError {
    TypeConflict(Ty, Ty),
    OccursConflict,
}

#[derive(Debug, Clone)]
pub enum ConstrainedExpr {
    Ty(Ty),
    TypeScheme(Ty, Vec<TypeVarID>),
}

#[derive(Debug, Clone)]
pub enum Constraint {
    Equality(ExprID, Ty, Ty),
}

pub struct ConstraintSolver<'a> {
    source_file: &'a mut SourceFile<Typed>,
    constraints: Vec<Constraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(source_file: &'a mut SourceFile<Typed>, constraints: Vec<Constraint>) -> Self {
        Self {
            source_file,
            constraints,
        }
    }

    pub fn solve(&mut self) -> Result<(), ConstraintError> {
        let mut substitutions = HashMap::<TypeVarID, Ty>::new();
        log::info!("solving {:#?}", self.constraints);

        while let Some(constraint) = self.constraints.pop() {
            self.solve_constraint(constraint, &mut substitutions)?
        }

        for typed_expr in &mut self.source_file.types().values_mut() {
            typed_expr.ty = Self::apply(typed_expr.ty.clone(), &substitutions);
        }

        Ok(())
    }

    fn solve_constraint(
        &mut self,
        constraint: Constraint,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), ConstraintError> {
        match constraint {
            Constraint::Equality(node_id, lhs, rhs) => {
                let lhs = Self::apply(lhs, substitutions);
                let rhs = Self::apply(rhs, substitutions);

                Self::unify(&lhs, &rhs, substitutions).map_err(|err| {
                    log::error!("{:?}", err);
                    err
                })?;

                self.source_file.define(node_id, lhs);
            }
        };

        Ok(())
    }

    fn apply(ty: Ty, substitutions: &HashMap<TypeVarID, Ty>) -> Ty {
        match ty {
            Ty::Int => ty,
            Ty::Float => ty,
            Ty::Bool => ty,
            Ty::Func(params, returning) => {
                let applied_params = params
                    .iter()
                    .map(|param| Self::apply(param.clone(), substitutions))
                    .collect();

                let applied_return = Self::apply(*returning, substitutions);

                Ty::Func(applied_params, Box::new(applied_return))
            }
            Ty::TypeVar(ref type_var) => {
                if let Some(ty) = substitutions.get(type_var) {
                    Self::apply(ty.clone(), substitutions)
                } else {
                    ty
                }
            }
            Ty::Void => todo!(),
        }
    }

    fn unify(
        lhs: &Ty,
        rhs: &Ty,
        substitutions: &mut HashMap<TypeVarID, Ty>,
    ) -> Result<(), ConstraintError> {
        log::trace!("Unifying: {:?} and {:?}", lhs, rhs);

        match (lhs, rhs) {
            // They're the same, sick.
            (a, b) if a == b => Ok(()),
            (Ty::TypeVar(v), ty) | (ty, Ty::TypeVar(v)) => {
                if Self::occurs_check(v, ty, substitutions) {
                    Err(ConstraintError::OccursConflict)
                } else {
                    substitutions.insert(v.clone(), ty.clone());
                    Ok(())
                }
            }
            (Ty::Func(lhs_params, lhs_returning), Ty::Func(rhs_params, rhs_returning))
                if lhs_params.len() == rhs_params.len() =>
            {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    Self::unify(lhs, rhs, substitutions)?;
                }

                Self::unify(lhs_returning, rhs_returning, substitutions)?;

                Ok(())
            }
            _ => todo!("{:#?} / {:#?}", lhs, rhs),
        }
    }

    /// Returns true if `v` occurs inside `ty` (after applying current `subs`).
    fn occurs_check(v: &TypeVarID, ty: &Ty, substitutions: &HashMap<TypeVarID, Ty>) -> bool {
        let ty = Self::apply(ty.clone(), substitutions);
        match &ty {
            Ty::TypeVar(tv) => tv == v,
            Ty::Func(params, returning) => {
                // check each parameter and the return type
                let oh = params
                    .iter()
                    .any(|param| Self::occurs_check(v, param, substitutions))
                    || Self::occurs_check(v, returning, substitutions);

                if oh {
                    log::error!("occur check failed: {:?}", ty);
                }

                oh
            }
            _ => false,
        }
    }
}
