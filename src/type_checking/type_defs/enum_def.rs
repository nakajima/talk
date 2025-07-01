use crate::{
    SymbolID,
    parser::ExprID,
    ty::Ty,
    type_defs::{TypeParams, protocol_def::Conformance, struct_def::Method},
    type_var_id::TypeVarID,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RawEnumVariant {
    pub name: String,
    pub expr_id: ExprID,
    pub values: Vec<ExprID>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumVariant {
    pub name: String,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumDef {
    pub symbol_id: SymbolID,
    pub name_str: String,
    pub type_parameters: TypeParams,
    pub variants: Vec<EnumVariant>,
    pub methods: Vec<Method>,
    pub conformances: Vec<Conformance>,
}

impl EnumDef {
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

    pub fn member_ty(&self, member_name: &str) -> Option<&Ty> {
        if let Some(method) = self.methods.iter().find(|m| m.name == member_name) {
            return Some(&method.ty);
        }

        for variant in self.variants.iter() {
            if variant.name == member_name {
                return Some(&variant.ty);
            }
        }

        None
    }

    pub(crate) fn tag_with_variant_for(&self, name: &str) -> Option<(u16, &EnumVariant)> {
        for (i, variant) in self.variants.iter().enumerate() {
            if variant.name == name {
                return Some((i as u16, variant));
            }
        }

        None
    }
}
