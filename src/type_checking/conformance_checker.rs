use crate::{
    environment::{Method, Property, ProtocolDef, TypeDef},
    ty::Ty,
    type_checker::TypeError,
};

pub struct ConformanceChecker<'a> {
    type_def: &'a TypeDef,
    protocol: &'a ProtocolDef,
    errors: Vec<ConformanceError>,
}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum ConformanceError {
    TypeCannotConform(Ty),
    MemberNotImplemented(TypeDef, ProtocolDef, String),
}

impl<'a> ConformanceChecker<'a> {
    pub fn new(type_def: &'a TypeDef, protocol: &'a ProtocolDef) -> Self {
        Self {
            type_def,
            protocol,
            errors: Default::default(),
        }
    }

    pub fn check(mut self) -> Result<Vec<(Ty, Ty)>, TypeError> {
        log::trace!(
            "Checking {} conforms to {}",
            self.type_def.name(),
            self.protocol.name_str
        );

        let mut unifications = vec![];

        for method in self.protocol.methods.iter() {
            let ty_method = match self.find_method(&method.name) {
                Ok(m) => m.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            unifications.push((method.ty.clone(), ty_method.ty.clone()));
        }

        for method in self.protocol.method_requirements.iter() {
            let ty_method = match self.find_method(&method.name) {
                Ok(m) => m.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            unifications.push((method.ty.clone(), ty_method.ty.clone()));
        }

        for property in self.protocol.properties.iter() {
            let ty_property = match self.find_property(&property.name) {
                Ok(p) => p.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            unifications.push((property.ty.clone(), ty_property.ty.clone()));
        }

        for _initializer in self.protocol.initializers.iter() {}

        if self.errors.is_empty() {
            Ok(unifications)
        } else {
            log::error!(
                "{} does not conform: {:?}",
                self.type_def.name(),
                self.errors
            );
            Err(TypeError::ConformanceError(self.errors))
        }
    }

    fn find_property(&self, name: &str) -> Result<&Property, ConformanceError> {
        if let Some(property) = self.type_def.find_property(name) {
            Ok(property)
        } else {
            Err(ConformanceError::MemberNotImplemented(
                self.type_def.clone(),
                self.protocol.clone(),
                name.to_string(),
            ))
        }
    }

    fn find_method(&self, method_name: &str) -> Result<&Method, ConformanceError> {
        if let Some(method) = self.type_def.find_method(method_name) {
            Ok(method)
        } else {
            Err(ConformanceError::MemberNotImplemented(
                self.type_def.clone(),
                self.protocol.clone(),
                method_name.to_string(),
            ))
        }
    }
}
