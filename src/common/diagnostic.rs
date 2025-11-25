use std::error::Error;

use crate::{
    name_resolution::name_resolver::NameResolverError, node_id::NodeID, parser_error::ParserError,
    types::type_error::TypeError,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic<E: Error> {
    pub id: NodeID,
    pub kind: E,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnyDiagnostic {
    Parsing(Diagnostic<ParserError>),
    NameResolution(Diagnostic<NameResolverError>),
    Typing(Diagnostic<TypeError>),
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
