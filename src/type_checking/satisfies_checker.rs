use std::collections::HashMap;

use crate::{
    conformance_checker::ConformanceError, environment::Environment, ty::Ty,
    type_checker::TypeError, type_constraint::TypeConstraint,
};

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
        let (type_id, _) = match &self.ty {
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

        let Some(type_def) = self.env.lookup_type(type_id) else {
            return Err(TypeError::Unknown(format!(
                "Did not resolve type with id: {type_id:?}"
            )));
        };

        let mut unifications = vec![];
        let mut errors = vec![];

        for constraint in self.constraints.iter() {
            match constraint {
                TypeConstraint::Equals { .. } => (),
                TypeConstraint::InstanceOf { .. } => (),
                TypeConstraint::Conforms {
                    protocol_id,
                    associated_types: conformance_associated_types,
                } => {
                    log::trace!("= Checking {:?} satisfies {constraint:?}", self.ty);

                    let Some(protocol_def) = self.env.lookup_protocol(protocol_id).cloned() else {
                        continue;
                    };

                    // if protocol_def.associated_types.len() != conformance_associated_types.len() {
                    //     errors.push(ConformanceError::TypeDoesNotConform(
                    //         type_def.name().to_string(),
                    //         "could not determine type parameters".to_string(),
                    //     ));
                    // }

                    if let Some(conformance) = type_def
                        .conformances()
                        .iter()
                        .find(|c| c.protocol_id == *protocol_id)
                    {
                        let mut map = HashMap::new();

                        for (provided, required) in conformance
                            .associated_types
                            .iter()
                            .zip(protocol_def.canonical_associated_types())
                        {
                            map.insert(provided.clone(), required.clone());
                        }

                        for (provided, required) in conformance_associated_types
                            .iter()
                            .zip(protocol_def.canonical_associated_types().iter())
                        {
                            let arg = map.get(provided).unwrap_or(provided);
                            unifications.push((required.clone(), arg.clone()));
                        }
                    } else {
                        errors.push(ConformanceError::TypeDoesNotConform(
                            type_def.name().to_string(),
                            protocol_def.name_str.to_string(),
                        ))
                    }
                }
            }
        }

        println!("--------------- Unifications from Satisfies: {unifications:#?}");

        if errors.is_empty() {
            Ok(unifications)
        } else {
            Err(TypeError::ConformanceError(errors))
        }
    }
}
