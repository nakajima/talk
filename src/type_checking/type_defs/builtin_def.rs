use crate::{
    SymbolID,
    ty::Ty,
    type_defs::{protocol_def::Conformance, struct_def::Method},
};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BuiltinDef {
    pub symbol_id: SymbolID,
    pub name_str: String,
    pub methods: Vec<Method>,
    pub conformances: Vec<Conformance>,
    pub ty: Ty,
}

impl BuiltinDef {
    pub fn member_ty(&self, name: &str) -> Option<&Ty> {
        if let Some(method) = self.methods.iter().find(|p| p.name == name) {
            return Some(&method.ty);
        }

        None
    }
}
