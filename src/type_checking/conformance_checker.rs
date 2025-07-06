use std::collections::HashMap;

use crate::{
    SymbolID,
    constraint_solver::ConstraintSolver,
    environment::{Environment, free_type_vars},
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
    type_def: &'a TypeDef,
    conformance: &'a Conformance,
    errors: Vec<ConformanceError>,
    env: &'a mut Environment,
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
    pub fn new(
        type_def: &'a TypeDef,
        conformance: &'a Conformance,
        env: &'a mut Environment,
    ) -> Self {
        Self {
            type_def,
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
        let mut substitutions = HashMap::new();
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
                    unifications.push((Ty::TypeVar(type_var), self.type_def.ty()));
                }
            }

            unifications.push((
                ConstraintSolver::apply(&method.ty, &substitutions, 0),
                ConstraintSolver::apply(&ty_method, &substitutions, 0),
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
                ConstraintSolver::apply(&method.ty, &substitutions, 0),
                ConstraintSolver::apply(&ty_method, &substitutions, 0),
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
                self.type_def.name(),
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
        if let Some(property) = self.type_def.find_property(name) {
            Ok(property)
        } else {
            Err(ConformanceError::MemberNotImplemented {
                ty: self.type_def.symbol_id(),
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
            .type_def
            .member_ty_with_conformances(method_name, self.env)
            && matches!(ty, Ty::Func(_, _, _))
        {
            Ok(ty)
        } else {
            Err(ConformanceError::MemberNotImplemented {
                ty: self.type_def.symbol_id(),
                protocol: protocol.symbol_id,
                member: method_name.to_string(),
            })
        }
    }
}
