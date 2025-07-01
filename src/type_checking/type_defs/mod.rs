use crate::{
    SymbolID,
    environment::TypeParameter,
    ty::Ty,
    type_defs::{
        enum_def::{EnumDef, EnumVariant},
        protocol_def::{Conformance, ProtocolDef},
        struct_def::{Initializer, Method, Property, StructDef},
    },
};

pub mod enum_def;
pub mod protocol_def;
pub mod struct_def;

pub type TypeParams = Vec<TypeParameter>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeDef {
    Enum(EnumDef),
    Struct(StructDef),
    Protocol(ProtocolDef),
}

impl TypeDef {
    pub fn member_ty(&self, name: &str) -> Option<&Ty> {
        match self {
            TypeDef::Enum(enum_def) => enum_def.member_ty(name),
            TypeDef::Struct(struct_def) => struct_def.member_ty(name),
            TypeDef::Protocol(protocol_def) => protocol_def.member_ty(name),
        }
    }

    pub fn symbol_id(&self) -> SymbolID {
        match self {
            Self::Enum(def) => def.name.unwrap(),
            Self::Struct(def) => def.symbol_id,
            Self::Protocol(def) => def.symbol_id,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Self::Enum(def) => &def.name_str,
            Self::Struct(def) => &def.name_str,
            Self::Protocol(def) => &def.name_str,
        }
    }

    pub fn conformances(&self) -> &Vec<Conformance> {
        match self {
            Self::Enum(def) => &def.conformances,
            Self::Struct(def) => &def.conformances,
            Self::Protocol(def) => &def.conformances,
        }
    }

    pub fn type_parameters(&self) -> &TypeParams {
        match self {
            Self::Enum(def) => &def.type_parameters,
            Self::Struct(def) => &def.type_parameters,
            Self::Protocol(def) => &def.associated_types,
        }
    }

    pub fn find_method(&self, method_name: &str) -> Option<&Method> {
        match self {
            Self::Enum(def) => def.methods.iter().find(|m| m.name == method_name),
            Self::Struct(def) => def.methods.iter().find(|m| m.name == method_name),
            Self::Protocol(def) => def.methods.iter().find(|m| m.name == method_name),
        }
    }

    pub fn find_property(&self, name: &str) -> Option<&Property> {
        match self {
            Self::Enum(_) => None,
            Self::Struct(def) => def.properties.iter().find(|p| p.name == name),
            Self::Protocol(def) => def.properties.iter().find(|p| p.name == name),
        }
    }

    pub fn set_methods(&mut self, methods: Vec<Method>) {
        if methods.is_empty() {
            return;
        }
        match self {
            Self::Enum(def) => def.methods = methods,
            Self::Struct(def) => def.methods = methods,
            Self::Protocol(def) => def.methods = methods,
        }
    }

    pub fn set_type_parameters(&mut self, params: Vec<TypeParameter>) {
        match self {
            Self::Enum(def) => def.type_parameters = params,
            Self::Struct(def) => def.type_parameters = params,
            Self::Protocol(def) => def.associated_types = params,
        }
    }

    pub fn set_method_requirements(&mut self, methods: Vec<Method>) {
        if methods.is_empty() {
            return;
        }
        match self {
            Self::Enum(_) => (),
            Self::Struct(_) => (),
            Self::Protocol(def) => def.method_requirements = methods,
        }
    }

    pub fn set_initializers(&mut self, initializers: Vec<Initializer>) {
        if initializers.is_empty() {
            return;
        }

        match self {
            Self::Enum(_) => (),
            Self::Struct(def) => def.initializers = initializers,
            Self::Protocol(def) => def.initializers = initializers,
        }
    }

    pub fn set_properties(&mut self, properties: Vec<Property>) {
        if properties.is_empty() {
            return;
        }
        match self {
            Self::Enum(_) => (),
            Self::Struct(def) => def.properties = properties,
            Self::Protocol(def) => def.properties = properties,
        }
    }

    pub fn set_variants(&mut self, variants: Vec<EnumVariant>) {
        if variants.is_empty() {
            return;
        }
        match self {
            Self::Enum(def) => def.variants = variants,
            Self::Struct(_) => (),
            Self::Protocol(_) => (),
        }
    }

    pub fn set_conformances(&mut self, conformances: Vec<Conformance>) {
        match self {
            Self::Enum(def) => def.conformances = conformances,
            Self::Struct(def) => def.conformances = conformances,
            Self::Protocol(def) => def.conformances = conformances,
        }
    }
}
