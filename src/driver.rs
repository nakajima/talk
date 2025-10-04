use std::{io, path::PathBuf};

use rustc_hash::FxHashMap;

use crate::{
    ast::{self, AST},
    lexer::Lexer,
    name_resolution::name_resolver::{self, NameResolver},
    node_id::FileID,
    parser::Parser,
    parser_error::ParserError,
    types::{
        passes::{
            dependencies_pass::{DependenciesPass, SCCResolved},
            inference_pass::InferencePass,
            type_headers_pass::TypeHeaderPass,
            type_resolve_pass::TypeResolvePass,
        },
        type_session::TypeSession,
    },
};

pub trait DriverPhase {}

pub struct Initial {}
impl DriverPhase for Initial {}

impl DriverPhase for Parsed {}
pub struct Parsed {
    pub asts: FxHashMap<PathBuf, AST<ast::Parsed>>,
}

impl DriverPhase for NameResolved {}
pub struct NameResolved {
    pub asts: FxHashMap<PathBuf, AST<name_resolver::NameResolved>>,
}

impl DriverPhase for Typed {}
pub struct Typed {
    pub asts: FxHashMap<PathBuf, AST<name_resolver::NameResolved>>,
    pub type_session: TypeSession,
}

pub enum CompileError {
    IO(io::Error),
    Parsing(ParserError),
}

pub struct Driver<Phase: DriverPhase = Initial> {
    files: Vec<PathBuf>,
    phase: Phase,
}

impl Driver {
    pub fn new(files: Vec<PathBuf>) -> Self {
        Self {
            files,
            phase: Initial {},
        }
    }

    pub fn parse(self) -> Result<Driver<Parsed>, CompileError> {
        let mut asts = FxHashMap::default();

        for (i, file) in self.files.iter().enumerate() {
            let input = std::fs::read_to_string(file).map_err(CompileError::IO)?;
            let lexer = Lexer::new(&input);
            let parser = Parser::new(file.clone().to_string_lossy(), FileID(i as u32), lexer);
            asts.insert(file.clone(), parser.parse().map_err(CompileError::Parsing)?);
        }

        Ok(Driver {
            files: self.files,
            phase: Parsed { asts },
        })
    }
}

impl Driver<Parsed> {
    pub fn resolve_names(self) -> Result<Driver<NameResolved>, CompileError> {
        let mut asts = FxHashMap::default();

        for (path, ast) in self.phase.asts {
            let resolved = NameResolver::resolve(ast);
            asts.insert(path, resolved);
        }

        Ok(Driver {
            files: self.files,
            phase: NameResolved { asts },
        })
    }
}

impl Driver<NameResolved> {
    pub fn typecheck(mut self) -> Result<Driver<Typed>, CompileError> {
        let mut type_session = TypeSession::default();

        let raw = TypeHeaderPass::drive_all(&mut type_session, &self.phase.asts);

        for ast in self.phase.asts.values_mut() {
            // TODO: do a drive_all for resolve pass
            TypeResolvePass::drive(ast, &mut type_session, raw.clone());
        }

        let mut scc = SCCResolved::default();
        for ast in self.phase.asts.values_mut() {
            // TODO: do a drive_all for deps pass
            DependenciesPass::drive(&mut type_session, ast, &mut scc);
        }

        for ast in self.phase.asts.values_mut() {
            InferencePass::perform(&mut type_session, &scc, ast);
        }

        Ok(Driver {
            files: self.files,
            phase: Typed {
                asts: self.phase.asts,
                type_session,
            },
        })
    }
}

#[cfg(test)]
pub mod tests {
    #[test]
    fn typechecks_multiple_files() {}
}
