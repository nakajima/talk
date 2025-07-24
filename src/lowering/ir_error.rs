use std::fmt::Display;

use crate::{SymbolID, type_def::Property};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IRError {
    ParseError(String),
    InvalidPointer(String),
    PartialInitialization(String, Vec<Property>),
    BuiltinNotFound(SymbolID),
    Unknown(String),
}

impl IRError {
    pub fn message(&self) -> String {
        match self {
            Self::ParseError(string) => format!("IR Parse error: {string}"),
            Self::InvalidPointer(name) => {
                format!("Invalid pointer `{name}`")
            }
            Self::PartialInitialization(_, properties) => format!(
                "Not all properties initialized. Missing: {}",
                properties
                    .iter()
                    .map(|p| p.name.as_str())
                    .collect::<Vec::<&str>>()
                    .join(", ")
            ),
            Self::BuiltinNotFound(symbol_id) => format!("Builtin not found: {symbol_id:?}"),
            Self::Unknown(msg) => msg.clone(),
        }
    }
}

impl Display for IRError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message())
    }
}
