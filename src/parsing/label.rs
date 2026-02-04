use std::{convert::Infallible, fmt::Display, str::FromStr};

use crate::name_resolution::symbol::Symbol;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub enum Label {
    Named(String),
    Positional(usize),
    _Symbol(Symbol),
}

impl<T: Into<String>> From<T> for Label {
    fn from(value: T) -> Self {
        Label::Named(value.into())
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Named(name) => write!(f, "{name}"),
            Self::Positional(i) => write!(f, "{i}"),
            Self::_Symbol(s) => write!(f, "{s}"),
        }
    }
}

impl FromStr for Label {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Ok(i) = str::parse::<usize>(s) {
            return Ok(Label::Positional(i));
        }

        Ok(Label::Named(s.into()))
    }
}
