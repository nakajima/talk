use tracing::Level;

use crate::{
    SymbolID,
    conformance::Conformance,
    environment::{Environment, free_type_vars},
    substitutions::Substitutions,
    ty::{RowKind, Ty},
    type_checker::TypeError,
    type_def::{Property, TypeDef},
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
        ty: Box<Ty>,
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

    #[tracing::instrument(level = Level::TRACE, skip(self), fields(result))]
    pub fn check(mut self) -> Result<Vec<(Ty, Ty)>, TypeError> {
        let Some(protocol) = self
            .env
            .lookup_protocol(&self.conformance.protocol_id)
            .cloned()
        else {
            return Err(TypeError::Unknown(
                "Cannot find protocol for conformance check".into(),
            ));
        };

        // Replace the protocol's associated types with the conformance's
        let mut substitutions = Substitutions::new();
        for (canonical, conforming) in protocol
            .canonical_type_variables()
            .into_iter()
            .zip(self.conformance.associated_types.iter())
        {
            substitutions.insert(canonical, conforming.clone());
        }

        let Some(type_def_conformance) = self.check_conformance_of_ty(&protocol).cloned() else {
            return Err(TypeError::ConformanceError(self.errors));
        };

        let mut unifications: Vec<(Ty, Ty)> = type_def_conformance
            .associated_types
            .iter()
            .cloned()
            .zip(self.conformance.associated_types.iter().cloned())
            .collect();

        for method in protocol.methods().iter() {
            let ty_method = match self.find_method(&protocol, &method.name) {
                Ok(m) => m.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            tracing::trace!("Found method {:?}", ty_method.to_string());

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

        for method in protocol.method_requirements().iter() {
            let ty_method = match self.find_method(&protocol, &method.name) {
                Ok(m) => m.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            tracing::trace!(
                "Found method {:?}\nConformance: {:?}",
                ty_method.to_string(),
                type_def_conformance
            );

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
            ))
        }

        for property in protocol.properties().iter() {
            let ty_property = match self.find_property(&protocol, &property.name) {
                Ok(p) => p.clone(),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            };

            // Find self references in the protocol's type and replace them with
            // our concrete type
            for type_var in free_type_vars(&ty_property.ty) {
                if matches!(type_var.kind, TypeVarKind::SelfVar(_)) {
                    unifications.push((Ty::TypeVar(type_var), self.ty.clone()));
                }
            }

            unifications.push((
                substitutions.apply(&property.ty, 0, &mut self.env.context),
                substitutions.apply(&ty_property.ty, 0, &mut self.env.context),
            ));
        }

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

    #[tracing::instrument(level = Level::TRACE, skip(self, protocol), fields(result))]
    fn find_property(&self, protocol: &TypeDef, name: &str) -> Result<&Property, ConformanceError> {
        if let Some(Some(property)) = self.type_def().map(|t| t.find_property(name)) {
            Ok(property)
        } else {
            Err(ConformanceError::MemberNotImplemented {
                ty: self.ty.clone().into(),
                protocol: protocol.symbol_id,
                member: name.to_string(),
            })
        }
    }

    #[tracing::instrument(level = Level::TRACE, skip(self, protocol), fields(result))]
    fn find_method(
        &mut self,
        protocol: &TypeDef,
        method_name: &str,
    ) -> Result<Ty, ConformanceError> {
        if let Some(ty) = self
            .type_def()
            .cloned()
            .map(|t| t.member_ty_with_conformances(method_name, self.env))
            && let Some(ty @ Ty::Method { .. }) = ty
        {
            Ok(ty)
        } else if let Ty::TypeVar(_var) = &self.ty {
            protocol
                .member_ty(method_name)
                .cloned()
                .ok_or(ConformanceError::MemberNotImplemented {
                    ty: self.ty.clone().into(),
                    protocol: protocol.symbol_id,
                    member: method_name.to_string(),
                })
        } else {
            Err(ConformanceError::MemberNotImplemented {
                ty: self.ty.clone().into(),
                protocol: protocol.symbol_id,
                member: method_name.to_string(),
            })
        }
    }

    fn check_conformance_of_ty(&mut self, protocol_def: &TypeDef) -> Option<&Conformance> {
        let type_def = self.ty.type_def(self.env)?;

        let conformance = type_def
            .conformances()
            .iter()
            .find(|c| c.protocol_id == protocol_def.symbol_id);

        if conformance.is_none() {
            self.errors.push(ConformanceError::TypeDoesNotConform(
                type_def.name().to_string(),
                protocol_def.name_str.to_string(),
            ));
        }

        conformance
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check;

    #[test]
    fn checks_basic() {
        let mut setup = check(
            "
        protocol Countable {}
        extend Int: Countable {}
        ",
        )
        .unwrap();

        let protocol = setup
            .env
            .types
            .values()
            .find(|t| t.name() == "Countable")
            .unwrap();

        let conformance = Conformance::new(protocol.symbol_id(), vec![]);
        let checker = ConformanceChecker::new(&Ty::Int, &conformance, &mut setup.env);
        let result = checker.check();
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn errors_with_no_conformance() {
        let mut setup = check(
            "
        protocol Countable {}
        ",
        )
        .unwrap();

        let protocol = setup
            .env
            .types
            .values()
            .find(|t| t.name() == "Countable")
            .unwrap();

        let conformance = Conformance::new(protocol.symbol_id(), vec![]);
        let checker = ConformanceChecker::new(&Ty::Int, &conformance, &mut setup.env);
        let result = checker.check();
        assert!(result.is_err(), "{result:?}");
    }
}
