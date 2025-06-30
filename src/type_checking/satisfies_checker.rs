use crate::{
    NameResolved, conformance_checker::ConformanceError, constraint_solver::ConstraintSolver,
    environment::Environment, ty::Ty, type_checker::TypeError, type_constraint::TypeConstraint,
};
use std::collections::HashMap;

pub struct SatisfiesChecker<'a> {
    env: &'a Environment,
    ty: &'a Ty,
    constraints: &'a [TypeConstraint],
}

impl<'a> SatisfiesChecker<'a> {
    pub fn new(env: &'a Environment, ty: &'a Ty, constraints: &'a [TypeConstraint]) -> Self {
        Self {
            env,
            ty,
            constraints,
        }
    }

    pub fn check(self) -> Result<Vec<(Ty, Ty)>, TypeError> {
        let (type_id, type_args) = match &self.ty {
            Ty::Enum(type_id, type_args)
            | Ty::EnumVariant(type_id, type_args)
            | Ty::Struct(type_id, type_args)
            | Ty::Protocol(type_id, type_args) => (type_id, type_args),
            _ => {
                return Err(TypeError::Unknown(format!(
                    "{:?} cannot satisfy type requirements: {:?}",
                    self.ty, self.constraints
                )));
            }
        };

        let type_def = self
            .env
            .lookup_type(type_id)
            .expect("didn't find type")
            .clone();

        let mut unifications = vec![];
        let mut errors = vec![];

        for constraint in self.constraints.iter() {
            log::trace!("= Checking {:?} satisfies {constraint:?}", self.ty);

            let protocol_def = self
                .env
                .lookup_protocol(&constraint.protocol_id)
                .expect("did not get protocol definition (should be impossible)");

            if let Some(conformance) = type_def
                .conformances()
                .iter()
                .find(|c| c.protocol_id == constraint.protocol_id)
            {
                let mut specialization_map = HashMap::new();
                for (param, arg) in type_def.type_parameters().iter().zip(type_args.iter()) {
                    specialization_map.insert(param.type_var.clone(), arg.clone());
                }

                let specialized_conformance_types = conformance
                    .associated_types
                    .iter()
                    .map(|ty| {
                        ConstraintSolver::<NameResolved>::substitute_ty_with_map(
                            ty,
                            &specialization_map,
                        )
                    })
                    .collect::<Vec<_>>();

                if specialized_conformance_types.len() != constraint.associated_types.len() {
                    errors.push(ConformanceError::TypeDoesNotConform(
                        type_def.name().to_string(),
                        "mismatched associated type count".to_string(),
                    ));
                    continue;
                }

                for (provided, required) in specialized_conformance_types
                    .iter()
                    .zip(&constraint.associated_types)
                {
                    unifications.push((provided.clone(), required.clone()));
                }
            } else {
                errors.push(ConformanceError::TypeDoesNotConform(
                    type_def.name().to_string(),
                    protocol_def.name_str.to_string(),
                ))
            }
        }

        if errors.is_empty() {
            Ok(unifications)
        } else {
            Err(TypeError::ConformanceError(errors))
        }
    }
}
