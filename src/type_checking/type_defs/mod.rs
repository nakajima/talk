use std::collections::HashMap;

use crate::{
    SymbolID,
    constraint_solver::ConstraintSolver,
    environment::{Environment, TypeParameter},
    substitutions::Substitutions,
    ty::Ty,
    type_checker::Scheme,
    type_defs::{
        builtin_def::BuiltinDef,
        enum_def::{EnumDef, EnumVariant},
        protocol_def::{Conformance, ProtocolDef},
        struct_def::{Initializer, Method, Property, StructDef},
    },
};

pub mod builtin_def;
pub mod enum_def;
pub mod protocol_def;
pub mod struct_def;

pub type TypeParams = Vec<TypeParameter>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDef {
    Enum(EnumDef),
    Struct(StructDef),
    Protocol(ProtocolDef),
    Builtin(BuiltinDef),
}

impl TypeDef {
    pub fn ty(&self) -> Ty {
        match self {
            TypeDef::Enum(enum_def) => {
                Ty::Enum(enum_def.symbol_id, enum_def.canonical_type_parameters())
            }
            TypeDef::Struct(struct_def) => {
                Ty::Struct(struct_def.symbol_id, struct_def.canonical_type_parameters())
            }
            TypeDef::Protocol(protocol_def) => Ty::Protocol(
                protocol_def.symbol_id,
                protocol_def.canonical_associated_types(),
            ),
            TypeDef::Builtin(builtin_def) => builtin_def.ty.clone(),
        }
    }

    pub fn instantiate(&self, env: &mut Environment) -> Ty {
        let scheme = Scheme {
            ty: self.ty(),
            unbound_vars: self
                .type_parameters()
                .iter()
                .map(|p| p.type_var.clone())
                .collect(),
        };

        env.instantiate(&scheme)
    }

    pub fn member_ty_with_conformances(&self, name: &str, env: &mut Environment) -> Option<Ty> {
        if let Some(member) = self.member_ty(name).cloned() {
            return Some(
                member, // env.instantiate(&Scheme {
                       //     ty: member,
                       //     unbound_vars: self
                       //         .type_parameters()
                       //         .iter()
                       //         .map(|v| v.type_var.clone())
                       //         .collect(),
                       // }),
            );
        }

        for conformance in self.conformances() {
            if let Some(TypeDef::Protocol(protocol_def)) =
                env.lookup_type(&conformance.protocol_id).cloned()
                && let Some(ty) = protocol_def.member_ty(name).cloned()
            {
                let mut subst = Substitutions::new();
                for (param, arg) in protocol_def
                    .associated_types
                    .iter()
                    .zip(&conformance.associated_types)
                {
                    subst.insert(param.type_var.clone(), arg.clone());
                }

                //let new_ty = ty.replace(self.ty(), &|ty| {
                //    matches!(
                //        ty,
                //        Ty::TypeVar(TypeVarID {
                //            kind: TypeVarKind::SelfVar(_),
                //            ..
                //        })
                //    ) || matches!(ty, Ty::SelfType)
                //});

                //let res = env.instantiate(&Scheme {
                //    ty: new_ty,
                //    unbound_vars: protocol_def.canonical_associated_type_vars(),
                //});

                return Some(ConstraintSolver::substitute_ty_with_map(&ty, &subst));
            }
        }

        None
    }

    pub fn member_ty(&self, name: &str) -> Option<&Ty> {
        match self {
            TypeDef::Enum(enum_def) => enum_def.member_ty(name),
            TypeDef::Struct(struct_def) => struct_def.member_ty(name),
            TypeDef::Protocol(protocol_def) => protocol_def.member_ty(name),
            TypeDef::Builtin(builtin_def) => builtin_def.member_ty(name),
        }
    }

    pub fn symbol_id(&self) -> SymbolID {
        match self {
            Self::Enum(def) => def.symbol_id,
            Self::Struct(def) => def.symbol_id,
            Self::Protocol(def) => def.symbol_id,
            Self::Builtin(def) => def.symbol_id,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Self::Enum(def) => &def.name_str,
            Self::Struct(def) => &def.name_str,
            Self::Protocol(def) => &def.name_str,
            Self::Builtin(def) => &def.name_str,
        }
    }

    pub fn conformances(&self) -> &Vec<Conformance> {
        match self {
            Self::Enum(def) => &def.conformances,
            Self::Struct(def) => &def.conformances,
            Self::Protocol(def) => &def.conformances,
            Self::Builtin(def) => &def.conformances,
        }
    }

    pub fn type_parameters(&self) -> TypeParams {
        match self {
            Self::Enum(def) => def.type_parameters.clone(),
            Self::Struct(def) => def.type_parameters.clone(),
            Self::Protocol(def) => def.associated_types.clone(),
            Self::Builtin(_) => vec![],
        }
    }

    pub fn find_method(&self, method_name: &str) -> Option<&Method> {
        match self {
            Self::Enum(def) => def.methods.iter().find(|m| m.name == method_name),
            Self::Struct(def) => def.methods.iter().find(|m| m.name == method_name),
            Self::Protocol(def) => def.methods.iter().find(|m| m.name == method_name),
            Self::Builtin(def) => def.methods.iter().find(|m| m.name == method_name),
        }
    }

    pub fn find_property(&self, name: &str) -> Option<&Property> {
        match self {
            Self::Enum(_) => None,
            Self::Struct(def) => def.properties.iter().find(|p| p.name == name),
            Self::Protocol(def) => def.properties.iter().find(|p| p.name == name),
            Self::Builtin(_) => None,
        }
    }

    pub fn add_methods(&mut self, methods: Vec<Method>) {
        if methods.is_empty() {
            return;
        }

        match self {
            Self::Enum(def) => def.methods.extend(methods),
            Self::Struct(def) => def.methods.extend(methods),
            Self::Protocol(def) => def.methods.extend(methods),
            Self::Builtin(def) => def.methods.extend(methods),
        }
    }

    pub fn add_type_parameters(&mut self, params: Vec<TypeParameter>) {
        match self {
            Self::Enum(def) => def.type_parameters.extend(params),
            Self::Struct(def) => def.type_parameters.extend(params),
            Self::Protocol(def) => def.associated_types.extend(params),
            Self::Builtin(_) => (),
        }
    }

    pub fn add_method_requirements(&mut self, methods: Vec<Method>) {
        if methods.is_empty() {
            return;
        }
        match self {
            Self::Enum(_) => (),
            Self::Struct(_) => (),
            Self::Protocol(def) => def.method_requirements.extend(methods),
            Self::Builtin(_) => (),
        }
    }

    pub fn add_initializers(&mut self, initializers: Vec<Initializer>) {
        if initializers.is_empty() {
            return;
        }

        match self {
            Self::Enum(_) => tracing::error!("Enums can't have initializers"),
            Self::Struct(def) => def.initializers.extend(initializers),
            Self::Protocol(def) => def.initializers.extend(initializers),
            Self::Builtin(_) => (),
        }
    }

    pub fn add_properties(&mut self, properties: Vec<Property>) {
        if properties.is_empty() {
            return;
        }
        match self {
            Self::Enum(_) => tracing::error!("Enums can't have properties"),
            Self::Struct(def) => def.properties.extend(properties),
            Self::Protocol(def) => def.properties.extend(properties),
            Self::Builtin(_) => (),
        }
    }

    pub fn add_variants(&mut self, variants: Vec<EnumVariant>) {
        if variants.is_empty() {
            return;
        }
        match self {
            Self::Enum(def) => def.variants.extend(variants),
            Self::Struct(_) => (),
            Self::Protocol(_) => (),
            Self::Builtin(_) => (),
        }
    }

    pub fn add_conformances(&mut self, conformances: Vec<Conformance>) {
        match self {
            Self::Enum(def) => def.conformances.extend(conformances),
            Self::Struct(def) => def.conformances.extend(conformances),
            Self::Protocol(def) => def.conformances.extend(conformances),
            Self::Builtin(def) => def.conformances.extend(conformances),
        }
    }
}
