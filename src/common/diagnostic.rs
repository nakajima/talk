use std::error::Error;
use std::fmt;

use crate::{
    name_resolution::name_resolver::NameResolverError, node_id::NodeID, parser_error::ParserError,
    types::TypeError,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Severity {
    Warn,
    Error,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Diagnostic<E: Error + std::hash::Hash> {
    pub id: NodeID,
    pub severity: Severity,
    pub kind: E,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AnyDiagnostic {
    Parsing(Diagnostic<ParserError>),
    NameResolution(Diagnostic<NameResolverError>),
    Types(Diagnostic<TypeError>),
}

impl From<Diagnostic<ParserError>> for AnyDiagnostic {
    fn from(value: Diagnostic<ParserError>) -> Self {
        Self::Parsing(value)
    }
}

impl From<Diagnostic<NameResolverError>> for AnyDiagnostic {
    fn from(value: Diagnostic<NameResolverError>) -> Self {
        Self::NameResolution(value)
    }
}

impl From<Diagnostic<TypeError>> for AnyDiagnostic {
    fn from(value: Diagnostic<TypeError>) -> Self {
        Self::Types(value)
    }
}

impl fmt::Display for AnyDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AnyDiagnostic::Parsing(d) => write!(f, "{}", d.kind),
            AnyDiagnostic::NameResolution(d) => write!(f, "{}", d.kind),
            AnyDiagnostic::Types(d) => write!(f, "{}", d.kind),
        }
    }
}
