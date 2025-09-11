use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Label {
    Named(String),
    Positional(usize),
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
        }
    }
}
