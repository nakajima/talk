use crate::{SymbolID, ty::Ty};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Name {
    Raw(String),
    Resolved(SymbolID, String),
    _Self(SymbolID),
}

impl Name {
    pub fn mangled(&self, _ty: &Ty) -> String {
        match self {
            Name::Raw(_) => panic!("Cannot mangle unresolved Name"),
            Name::Resolved(symbol_id, name_str) => {
                if name_str == "main" {
                    "@main".into()
                } else {
                    format!("@_{}_{}", symbol_id.0, name_str)
                }
            }
            Name::_Self(_) => {
                todo!()
            }
        }
    }

    pub fn name_str(&self) -> String {
        match self {
            Name::Raw(name_str) => name_str.into(),
            Name::Resolved(_symbol_id, name_str) => name_str.into(),
            Name::_Self(_) => {
                todo!()
            }
        }
    }

    pub fn try_symbol_id(&self) -> SymbolID {
        match self {
            Name::Raw(name_str) => panic!("Cannot get symbol ID from unresolved {name_str:?}"),
            Name::Resolved(symbol_id, _) => *symbol_id,
            Name::_Self(symbol_id) => *symbol_id,
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
