use crate::{
    SymbolID,
    parser::ExprID,
    ty::Ty,
    type_defs::{TypeParams, protocol_def::Conformance},
    type_var_id::TypeVarID,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Property {
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
    pub default_value: Option<ExprID>,
}

impl Property {
    pub fn new(name: String, expr_id: ExprID, ty: Ty, default_value: Option<ExprID>) -> Self {
        Self {
            name,
            expr_id,
            ty,
            default_value,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RawProperty {
    pub name: String,
    pub expr_id: ExprID,
    pub placeholder: TypeVarID,
    pub default_value: Option<ExprID>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RawInitializer {
    pub name: String,
    pub expr_id: ExprID,
    pub func_id: ExprID,
    pub params: Vec<ExprID>,
    pub placeholder: TypeVarID,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Initializer {
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
}

impl Method {
    pub fn new(name: String, expr_id: ExprID, ty: Ty) -> Self {
        Self { name, expr_id, ty }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RawMethod {
    pub name: String,
    pub expr_id: ExprID,
    pub placeholder: TypeVarID,
}

impl RawMethod {
    pub fn new(name: String, expr_id: ExprID, placeholder: TypeVarID) -> Self {
        Self {
            name,
            expr_id,
            placeholder,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDef {
    pub symbol_id: SymbolID,
    pub name_str: String,
    pub type_parameters: TypeParams,
    pub properties: Vec<Property>,
    pub methods: Vec<Method>,
    pub initializers: Vec<Initializer>,
    pub conformances: Vec<Conformance>,
}

impl StructDef {
    pub fn new(symbol_id: SymbolID, name_str: String, type_parameters: TypeParams) -> Self {
        Self {
            symbol_id,
            name_str,
            type_parameters,
            methods: Default::default(),
            properties: Default::default(),
            initializers: Default::default(),
            conformances: Default::default(),
        }
    }

    pub fn member_ty(&self, name: &str) -> Option<&Ty> {
        if let Some(property) = self.properties.iter().find(|p| p.name == name) {
            return Some(&property.ty);
        }

        if let Some(method) = self.methods.iter().find(|p| p.name == name) {
            return Some(&method.ty);
        }

        None
    }

    pub fn conforms_to(&self, protocol_id: &SymbolID) -> bool {
        for conformance in self.conformances.iter() {
            if &conformance.protocol_id == protocol_id {
                return true;
            }
        }

        false
    }

    pub fn canonical_type_parameters(&self) -> Vec<Ty> {
        self.type_parameters
            .iter()
            .map(|t| Ty::TypeVar(t.type_var.clone()))
            .collect()
    }

    pub fn canonical_type_vars(&self) -> Vec<TypeVarID> {
        self.type_parameters
            .iter()
            .map(|t| t.type_var.clone())
            .collect()
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
