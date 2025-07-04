use std::collections::HashMap;

use crate::{
    SymbolID,
    conformance_checker::ConformanceError,
    environment::{Environment, free_type_vars},
    ty::Ty,
    type_checker::TypeError,
    type_constraint::TypeConstraint,
    type_defs::{TypeDef, protocol_def::ProtocolDef, struct_def::Property},
    type_var_id::TypeVarKind,
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
        let (type_id, type_args) = match &self.ty {
            Ty::Enum(type_id, type_args)
            | Ty::EnumVariant(type_id, type_args)
            | Ty::Struct(type_id, type_args)
            | Ty::Protocol(type_id, type_args) => (type_id, type_args),
            Ty::Int => (&SymbolID::INT, &vec![]),
            Ty::Float => (&SymbolID::FLOAT, &vec![]),
            Ty::Bool => (&SymbolID::BOOL, &vec![]),
            Ty::Pointer => (&SymbolID::POINTER, &vec![]),
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
                    associated_types,
                } => {
                    log::trace!("= Checking {:?} satisfies {constraint:?}", self.ty);

                    let Some(protocol_def) = self.env.lookup_protocol(protocol_id).cloned() else {
                        log::error!("Protocol not found: {protocol_id:?}");
                        continue;
                    };

                    if let Some(conformance) = type_def
                        .conformances()
                        .iter()
                        .find(|c| c.protocol_id == *protocol_id)
                    {
                        let mut map = HashMap::new();

                        let (method_unifications, method_errors) =
                            self.check_method_conformance(&protocol_def, type_def);
                        unifications.extend(method_unifications);
                        errors.extend(method_errors);

                        let (property_unifications, property_errors) =
                            self.check_property_performance(&protocol_def, type_def);
                        unifications.extend(property_unifications);
                        errors.extend(property_errors);

                        log::warn!("Checking constraint: {constraint:?}");
                        log::warn!("Conformances: {conformance:?}");
                        log::warn!("Type def: {type_def:?}");
                        log::warn!("Protocol: {protocol_def:?}");

                        for (provided, required) in
                            conformance.associated_types.iter().zip(type_args)
                        {
                            map.insert(provided.clone(), required.clone());
                        }

                        log::warn!("Map: {map:?}");

                        for (param, arg) in
                            conformance.associated_types.iter().zip(associated_types)
                        {
                            let arg = map.get(arg).unwrap_or(arg);
                            unifications.push((param.clone(), arg.clone()));
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

        if errors.is_empty() {
            log::warn!("Returning unifications: {unifications:?}");
            Ok(unifications)
        } else {
            Err(TypeError::ConformanceError(errors))
        }
    }

    fn check_method_conformance(
        &self,
        protocol_def: &ProtocolDef,
        type_def: &TypeDef,
    ) -> (Vec<(Ty, Ty)>, Vec<ConformanceError>) {
        let mut errors = vec![];
        let mut unifications = vec![];

        for method in protocol_def.methods.iter() {
            let ty_method = match self.find_method(type_def, &protocol_def.symbol_id, &method.name)
            {
                Ok(m) => m.clone(),
                Err(e) => {
                    errors.push(e);
                    continue;
                }
            };

            // Find self references in the protocol's type and replace them with our concrete type
            for type_var in free_type_vars(&ty_method) {
                log::error!("free type var: {type_var:?}");
                if matches!(type_var.kind, TypeVarKind::SelfVar(_)) {
                    unifications.push((Ty::TypeVar(type_var), type_def.ty()));
                }
            }

            unifications.push((method.ty.clone(), ty_method));
        }

        (unifications, errors)
    }

    fn check_property_performance(
        &self,
        protocol_def: &ProtocolDef,
        type_def: &TypeDef,
    ) -> (Vec<(Ty, Ty)>, Vec<ConformanceError>) {
        let mut errors = vec![];
        let mut unifications = vec![];

        for property in protocol_def.properties.iter() {
            let ty_property =
                match self.find_property(type_def, protocol_def.symbol_id, &property.name) {
                    Ok(p) => p.clone(),
                    Err(e) => {
                        errors.push(e);
                        continue;
                    }
                };

            unifications.push((property.ty.clone(), ty_property.ty.clone()));
        }

        (unifications, errors)
    }

    fn find_property<'b>(
        &self,
        type_def: &'b TypeDef,
        protocol_id: SymbolID,
        name: &str,
    ) -> Result<&'b Property, ConformanceError> {
        if let Some(property) = type_def.find_property(name) {
            Ok(property)
        } else {
            Err(ConformanceError::MemberNotImplemented {
                ty: type_def.symbol_id(),
                protocol: protocol_id,
                member: name.to_string(),
            })
        }
    }

    fn find_method(
        &self,
        type_def: &TypeDef,
        protocol_id: &SymbolID,
        method_name: &str,
    ) -> Result<Ty, ConformanceError> {
        if let Some(ty) = type_def.member_ty_with_conformances(method_name, self.env)
            && matches!(ty, Ty::Func(_, _, _))
        {
            Ok(ty)
        } else {
            Err(ConformanceError::MemberNotImplemented {
                ty: type_def.symbol_id(),
                protocol: *protocol_id,
                member: method_name.to_string(),
            })
        }
    }
}
