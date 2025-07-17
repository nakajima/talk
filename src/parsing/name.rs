use crate::{SymbolID, ty::Ty, type_checker::TypeError};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Name {
    Raw(String),
    Resolved(SymbolID, String),
    _Self(SymbolID),
    SelfType,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ResolvedName(pub SymbolID, pub String);

impl ResolvedName {
    pub fn mangled(&self, _ty: &Ty) -> String {
        if self.1 == "main" {
            "@main".into()
        } else {
            format!("@_{:?}_{}", self.0.0, self.1)
        }
    }

    pub fn init_fn_name(&self) -> String {
        format!("@_{}_{}_init", self.0.0, self.1)
    }

    pub fn method_fn_name(&self, name: &str) -> String {
        format!("@_{}_{}_{name}", self.0.0, self.1)
    }

    pub fn name_str(&self) -> String {
        self.1.to_string()
    }

    pub fn symbol_id(&self) -> SymbolID {
        self.0
    }
}

impl Name {
    pub fn resolved(&self) -> Result<ResolvedName, TypeError> {
        match self {
            Name::Raw(_) => Err(TypeError::Unresolved(format!("{self:?} is unresolved"))),
            Name::Resolved(symbol_id, name_str) => Ok(ResolvedName(*symbol_id, name_str.clone())),
            Name::_Self(symbol_id) => Ok(ResolvedName(*symbol_id, "self".to_string())),
            Name::SelfType => Err(TypeError::Unresolved(format!(
                "Name::SelfType {self:?} is unresolved"
            ))),
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
            Name::Raw(name_str) => Err(TypeError::Unresolved(format!(
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
