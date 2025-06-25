use crate::{
    constraint_solver::{ConstraintSolver, Substitutions},
    environment::{Environment, Method, ProtocolDef, TypeDef},
    ty::Ty,
    type_checker::TypeError,
};

pub struct ConformanceChecker<'a> {
    env: &'a mut Environment,
    type_def: &'a TypeDef,
    protocol: &'a ProtocolDef,
    substitutions: &'a mut Substitutions,
    errors: Vec<ConformanceError>,
}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum ConformanceError {
    TypeCannotConform(Ty),
    MethodNotImplemented(TypeDef, ProtocolDef, String),
}

impl<'a> ConformanceChecker<'a> {
    pub fn new(
        env: &'a mut Environment,
        type_def: &'a TypeDef,
        protocol: &'a ProtocolDef,
        substitutions: &'a mut Substitutions,
    ) -> Self {
        Self {
            env,
            type_def,
            protocol,
            substitutions,
            errors: Default::default(),
        }
    }

    pub fn check(mut self) -> Result<(), TypeError> {
        log::trace!(
            "Checking {} conforms to {}",
            self.type_def.name(),
            self.protocol.name_str
        );

        for method in self.protocol.methods.iter() {
            let ty_method = match self.find_method(&method.name) {
                Ok(m) => m.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            ConstraintSolver::unify(&method.ty, &ty_method.ty, self.substitutions, self.env)?;
        }

        for _property in self.protocol.properties.iter() {}
        for _initializer in self.protocol.initializers.iter() {}

        if self.errors.is_empty() {
            Ok(())
        } else {
            log::error!(
                "{} does not conform: {:?}",
                self.type_def.name(),
                self.errors
            );
            Err(TypeError::ConformanceError(self.errors))
        }
    }

    fn find_method(&self, method_name: &str) -> Result<&Method, ConformanceError> {
        if let Some(method) = self.type_def.find_method(method_name) {
            Ok(method)
        } else {
            Err(ConformanceError::MethodNotImplemented(
                self.type_def.clone(),
                self.protocol.clone(),
                method_name.to_string(),
            ))
        }
    }
}
