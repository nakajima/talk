use crate::SymbolID;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Name {
    Raw(String),
    Resolved(SymbolID, String),
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
