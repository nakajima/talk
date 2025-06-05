use crate::{SymbolID, type_checker::Ty};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Name {
    Raw(String),
    Resolved(SymbolID, String),
}

impl Name {
    pub fn mangled(&self, _ty: &Ty) -> String {
        match self {
            Name::Raw(_) => panic!("Cannot mangle unresolved Name"),
            Name::Resolved(symbol_id, name_str) => {
                if name_str == "main" {
                    "@main".into()
                } else {
                    format!("@_{:?}_{}", symbol_id.0, name_str)
                }
            }
        }
    }
}

impl From<String> for Name {
    fn from(value: String) -> Self {
        Name::Raw(value)
    }
}

impl From<&str> for Name {
    fn from(value: &str) -> Self {
        Name::Raw(value.to_string())
    }
}

impl From<Name> for SymbolID {
    fn from(value: Name) -> Self {
        let Name::Resolved(id, _) = value else {
            panic!("Tried to convert non-resolved name to symbol")
        };

        id
    }
}
