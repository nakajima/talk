use std::error::Error;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IRError {
    CouldNotParse(String),
}

impl Error for IRError {}

impl std::fmt::Display for IRError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CouldNotParse(string) => write!(f, "Could not parse IR: {string}"),
        }
    }
}
