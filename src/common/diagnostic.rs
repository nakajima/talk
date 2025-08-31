use std::error::Error;

use crate::{
    name_resolution::name_resolver::NameResolverError, parser_error::ParserError, span::Span,
    types::type_error::TypeError,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic<E: Error> {
    pub path: String,
    pub span: Span,
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
