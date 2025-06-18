use crate::environment::Property;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IRError {
    ParseError,
    InvalidPointer(String),
    PartialInitialization(String, Vec<Property>),
    Unknown(String),
}

impl IRError {
    pub fn message(&self) -> String {
        match self {
            Self::ParseError => "Parse error".into(),
            Self::InvalidPointer(name) => {
                format!("Invalid pointer `{name}`")
            },
            Self::PartialInitialization(_, properties) => format!(
                "Not all properties initialized. Missing: {}",
                properties
                    .iter()
                    .map(|p| p.name.as_str())
                    .collect::<Vec::<&str>>()
                    .join(", ")
            ),
            Self::Unknown(msg) => msg.clone(),
        }
    }
}
