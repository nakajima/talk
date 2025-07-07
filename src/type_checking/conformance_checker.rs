use crate::{
    SymbolID,
    environment::{Environment, free_type_vars},
    substitutions::Substitutions,
    ty::Ty,
    type_checker::TypeError,
    type_defs::{
        TypeDef,
        protocol_def::{Conformance, ProtocolDef},
        struct_def::Property,
    },
    type_var_id::TypeVarKind,
};

pub struct ConformanceChecker<'a> {
    ty: &'a Ty,
    conformance: &'a Conformance,
    errors: Vec<ConformanceError>,
    env: &'a mut Environment,
}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum ConformanceError {
    TypeCannotConform(String),
    TypeDoesNotConform(String, String),
    MemberNotImplemented {
        ty: Ty,
        protocol: SymbolID,
        member: String,
    },
}

impl<'a> ConformanceChecker<'a> {
    pub fn new(ty: &'a Ty, conformance: &'a Conformance, env: &'a mut Environment) -> Self {
        Self {
            ty,
            conformance,
            errors: Default::default(),
            env,
        }
    }

    pub fn check(mut self) -> Result<Vec<(Ty, Ty)>, TypeError> {
        let Some(protocol) = self
            .env
            .lookup_protocol(&self.conformance.protocol_id)
            .cloned()
        else {
            return Err(TypeError::Unknown(
                "Cannot find enum for conformance check".into(),
            ));
        };

        // Replace the protocol's associated types with the conformance's
        let mut substitutions = Substitutions::new();
        for (canonical, conforming) in protocol
            .canonical_associated_type_vars()
            .into_iter()
            .zip(self.conformance.associated_types.iter())
        {
            substitutions.insert(canonical, conforming.clone());
        }

        let mut unifications = vec![];

        for method in protocol.methods.iter() {
            let ty_method = match self.find_method(&protocol, &method.name) {
                Ok(m) => m.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            // Find self references in the protocol's type and replace them with
            // our concrete type
            for type_var in free_type_vars(&ty_method) {
                if matches!(type_var.kind, TypeVarKind::SelfVar(_)) {
                    unifications.push((Ty::TypeVar(type_var), self.ty.clone()));
                }
            }

            unifications.push((
                substitutions.apply(&method.ty, 0, &mut self.env.context),
                substitutions.apply(&ty_method, 0, &mut self.env.context),
            ));
        }

        for method in protocol.method_requirements.iter() {
            let ty_method = match self.find_method(&protocol, &method.name) {
                Ok(m) => m.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            unifications.push((
                substitutions.apply(&method.ty, 0, &mut self.env.context),
                substitutions.apply(&ty_method, 0, &mut self.env.context),
            ));
        }

        for property in protocol.properties.iter() {
            let ty_property = match self.find_property(&protocol, &property.name) {
                Ok(p) => p.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            unifications.push((property.ty.clone(), ty_property.ty.clone()));
        }

        for _initializer in protocol.initializers.iter() {}

        if self.errors.is_empty() {
            Ok(unifications)
        } else {
            tracing::error!(
                "{} does not conform: {:?}",
                self.ty.to_string(),
                self.errors
            );
            Err(TypeError::ConformanceError(self.errors))
        }
    }

    fn find_property(
        &self,
        protocol: &ProtocolDef,
        name: &str,
    ) -> Result<&Property, ConformanceError> {
        if let Some(Some(property)) = self.type_def().map(|t| t.find_property(name)) {
            Ok(property)
        } else {
            Err(ConformanceError::MemberNotImplemented {
                ty: self.ty.clone(),
                protocol: protocol.symbol_id,
                member: name.to_string(),
            })
        }
    }

    fn find_method(
        &mut self,
        protocol: &ProtocolDef,
        method_name: &str,
    ) -> Result<Ty, ConformanceError> {
        if let Some(ty) = self
            .type_def()
            .cloned()
            .map(|t| t.member_ty_with_conformances(method_name, self.env))
            && let Some(ty @ Ty::Func(_, _, _)) = ty
        {
            Ok(ty)
        } else if let Ty::TypeVar(_var) = &self.ty {
            protocol
                .member_ty(method_name)
                .cloned()
                .ok_or(ConformanceError::MemberNotImplemented {
                    ty: self.ty.clone(),
                    protocol: protocol.symbol_id,
                    member: method_name.to_string(),
                })
        } else {
            Err(ConformanceError::MemberNotImplemented {
                ty: self.ty.clone(),
                protocol: protocol.symbol_id,
                member: method_name.to_string(),
            })
        }
    }

    fn type_def(&self) -> Option<&TypeDef> {
        match self.ty {
            Ty::Struct(symbol_id, _) | Ty::Enum(symbol_id, _) | Ty::Protocol(symbol_id, _) => {
                self.env.lookup_type(symbol_id)
            }
            Ty::Int => self.env.lookup_type(&SymbolID::INT),
            Ty::Float => self.env.lookup_type(&SymbolID::FLOAT),
            Ty::Bool => self.env.lookup_type(&SymbolID::BOOL),
            Ty::Pointer => self.env.lookup_type(&SymbolID::POINTER),
            _ => None,
        }
    }
}
