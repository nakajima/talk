use std::{error::Error, fmt::Display};

#[derive(Debug, Clone)]
pub enum TypeError {
    Any,
}
impl Error for TypeError {}
impl Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Any => write!(f, ""),
        }
    }
}
