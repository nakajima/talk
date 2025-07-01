use crate::{
    SymbolID,
    ty::Ty,
    type_defs::{
        TypeParams,
        struct_def::{Initializer, Method, Property},
    },
    type_var_id::TypeVarID,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Conformance {
    pub protocol_id: SymbolID,
    pub associated_types: Vec<Ty>,
}

impl Conformance {
    pub fn new(protocol_id: SymbolID, associated_types: Vec<Ty>) -> Self {
        Self {
            protocol_id,
            associated_types,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProtocolDef {
    pub symbol_id: SymbolID,
    pub name_str: String,
    pub associated_types: TypeParams,
    pub conformances: Vec<Conformance>,
    pub properties: Vec<Property>,
    pub methods: Vec<Method>,
    pub initializers: Vec<Initializer>,
    pub method_requirements: Vec<Method>,
}

impl ProtocolDef {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        symbol_id: SymbolID,
        name_str: String,
        associated_types: TypeParams,
        conformances: Vec<Conformance>,
        properties: Vec<Property>,
        methods: Vec<Method>,
        initializers: Vec<Initializer>,
        method_requirements: Vec<Method>,
    ) -> Self {
        Self {
            symbol_id,
            name_str,
            associated_types,
            conformances,
            properties,
            methods,
            initializers,
            method_requirements,
        }
    }

    pub fn canonical_associated_types(&self) -> Vec<Ty> {
        self.associated_types
            .iter()
            .map(|t| Ty::TypeVar(t.type_var.clone()))
            .collect()
    }

    pub fn canonical_associated_type_vars(&self) -> Vec<TypeVarID> {
        self.associated_types
            .iter()
            .map(|t| t.type_var.clone())
            .collect()
    }

    pub fn member_ty(&self, name: &str) -> Option<&Ty> {
        if let Some(property) = self.properties.iter().find(|p| p.name == name) {
            return Some(&property.ty);
        }

        if let Some(method) = self.methods.iter().find(|p| p.name == name) {
            return Some(&method.ty);
        }

        if let Some(method) = self.method_requirements.iter().find(|p| p.name == name) {
            return Some(&method.ty);
        }

        None
    }

    pub fn type_repr(&self, type_parameters: &TypeParams) -> Ty {
        Ty::Struct(
            self.symbol_id,
            type_parameters
                .iter()
                .map(|t| Ty::TypeVar(t.type_var.clone()))
                .collect(),
        )
    }
}
