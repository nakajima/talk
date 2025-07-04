use crate::{
    SymbolID,
    environment::{Environment, free_type_vars},
    ty::Ty,
    type_checker::TypeError,
    type_defs::{TypeDef, protocol_def::ProtocolDef, struct_def::Property},
    type_var_id::TypeVarKind,
};

pub struct ConformanceChecker<'a> {
    type_def: &'a TypeDef,
    protocol: &'a ProtocolDef,
    errors: Vec<ConformanceError>,
    env: &'a Environment,
}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum ConformanceError {
    TypeCannotConform(String),
    TypeDoesNotConform(String, String),
    MemberNotImplemented {
        ty: SymbolID,
        protocol: SymbolID,
        member: String,
    },
}

impl<'a> ConformanceChecker<'a> {
    pub fn new(type_def: &'a TypeDef, protocol: &'a ProtocolDef, env: &'a Environment) -> Self {
        Self {
            type_def,
            protocol,
            errors: Default::default(),
            env,
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

            // Find self references in the protocol's type and replace them with our concrete type
            // for type_var in free_type_vars(&ty_method) {
            //     if matches!(type_var.kind, TypeVarKind::SelfVar(_)) {
            //         unifications.push((Ty::TypeVar(type_var), self.type_def.ty()));
            //     }
            // }

            unifications.push((method.ty.clone(), ty_method));
        }

        for method in self.protocol.method_requirements.iter() {
            let ty_method = match self.find_method(&method.name) {
                Ok(m) => m.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            unifications.push((method.ty.clone(), ty_method));
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
            Err(ConformanceError::MemberNotImplemented {
                ty: self.type_def.symbol_id(),
                protocol: self.protocol.symbol_id,
                member: name.to_string(),
            })
        }
    }

    fn find_method(&self, method_name: &str) -> Result<Ty, ConformanceError> {
        if let Some(ty) = self
            .type_def
            .member_ty_with_conformances(method_name, self.env)
            && matches!(ty, Ty::Func(_, _, _))
        {
            Ok(ty)
        } else {
            Err(ConformanceError::MemberNotImplemented {
                ty: self.type_def.symbol_id(),
                protocol: self.protocol.symbol_id,
                member: method_name.to_string(),
            })
        }
    }
}
