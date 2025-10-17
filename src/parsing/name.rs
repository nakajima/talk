use std::fmt::Display;

use crate::name_resolution::{name_resolver::NameResolverError, symbol::Symbol};

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Name {
    Raw(String),
    Resolved(Symbol, String),
    SelfType(Symbol),
}

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Raw(name) => write!(f, "@{}", name),
            Self::Resolved(sym, name) => write!(f, "@{name}:{sym}"),
            Self::SelfType(id) => write!(f, "Self({id})"),
        }
    }
}

impl Name {
    pub fn name_str(&self) -> String {
        match self {
            Name::Raw(name_str) => name_str.into(),
            Name::Resolved(_symbol_id, name_str) => name_str.into(),
            Name::SelfType(..) => "Self".to_string(),
        }
    }

    pub fn symbol(&self) -> Result<Symbol, NameResolverError> {
        if let Name::Resolved(sym, _) = self {
            return Ok(*sym);
        }

        Err(NameResolverError::Unresolved(self.clone()))
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
