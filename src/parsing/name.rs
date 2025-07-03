use crate::{SymbolID, ty::Ty, type_checker::TypeError};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Name {
    Raw(String),
    Resolved(SymbolID, String),
    _Self(SymbolID),
    SelfType,
}

impl Name {
    pub fn mangled(&self, _ty: &Ty) -> String {
        match self {
            Name::Raw(_) => "Cannot mangle unresolved Name".into(),
            Name::Resolved(symbol_id, name_str) => {
                if name_str == "main" {
                    "@main".into()
                } else {
                    format!("@_{:?}_{}", symbol_id.0, name_str)
                }
            }
            Name::_Self(symbol) => format!("self{symbol:?}"),
            Name::SelfType => "Self".to_string(),
        }
    }

    pub fn name_str(&self) -> String {
        match self {
            Name::Raw(name_str) => name_str.into(),
            Name::Resolved(_symbol_id, name_str) => name_str.into(),
            Name::_Self(_) => "self".into(),
            Name::SelfType => "Self".to_string(),
        }
    }

    pub fn symbol_id(&self) -> Result<SymbolID, TypeError> {
        match self {
            #[allow(clippy::panic)]
            Name::Raw(name_str) => Err(TypeError::Unknown(format!(
                "Cannot get symbol ID from unresolved {name_str:?}"
            ))),
            Name::Resolved(symbol_id, _) => Ok(*symbol_id),
            Name::_Self(symbol_id) => Ok(*symbol_id),
            Name::SelfType => Err(TypeError::Unknown(
                "Cannot get symbol ID from unresolved Self".to_string(),
            )),
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
    #[allow(clippy::panic)]
    fn from(value: Name) -> Self {
        let Name::Resolved(id, _) = value else {
            panic!("Tried to convert non-resolved name to symbol")
        };

        id
    }
}
