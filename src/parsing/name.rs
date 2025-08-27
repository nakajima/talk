use crate::types::symbol::Symbol;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Name {
    Raw(String),
    Resolved(Symbol, String),
    _Self(Symbol),
    SelfType,
}

impl Name {
    pub fn name_str(&self) -> String {
        match self {
            Name::Raw(name_str) => name_str.into(),
            Name::Resolved(_symbol_id, name_str) => name_str.into(),
            Name::_Self(_) => "self".into(),
            Name::SelfType => "Self".to_string(),
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

impl From<Name> for Symbol {
    #[allow(clippy::panic)]
    fn from(value: Name) -> Self {
        let Name::Resolved(id, _) = value else {
            panic!("Tried to convert non-resolved name to symbol")
        };

        id
    }
}
