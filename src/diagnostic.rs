use crate::{
    lexer::LexerError, name_resolver::NameResolverError, parser::ParserError,
    type_checker::TypeError,
};

#[derive(Debug, Clone)]
pub enum DiagnosticKind {
    Lexer(LexerError),
    Parse(ParserError),
    Resolve(NameResolverError),
    Typing(TypeError),
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    kind: DiagnosticKind,
}

impl Diagnostic {
    pub fn lexer(err: LexerError) -> Diagnostic {
        Self {
            kind: DiagnosticKind::Lexer(err),
        }
    }

    pub fn parser(err: ParserError) -> Diagnostic {
        Self {
            kind: DiagnosticKind::Parse(err),
        }
    }

    pub fn resolve(err: NameResolverError) -> Diagnostic {
        Self {
            kind: DiagnosticKind::Resolve(err),
        }
    }

    pub fn typing(err: TypeError) -> Diagnostic {
        Self {
            kind: DiagnosticKind::Typing(err),
        }
    }
}
