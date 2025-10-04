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

#[derive(Debug)]
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
            tracing::info!("parsing {file:?}");
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
        let resolver = NameResolver::new();

        let (paths, asts): (Vec<_>, Vec<_>) = self.phase.asts.into_iter().unzip();
        let resolved = resolver.resolve(asts);

        let asts = paths.into_iter().zip(resolved).collect();

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
            tracing::info!("resolving types in {:?}", ast.path);
            TypeResolvePass::drive(ast, &mut type_session, raw.clone());
        }

        let mut scc = SCCResolved::default();
        for ast in self.phase.asts.values_mut() {
            // TODO: do a drive_all for deps pass
            tracing::info!("resolving type deps in {:?}", ast.path);
            DependenciesPass::drive(&mut type_session, ast, &mut scc);
        }

        for ast in self.phase.asts.values_mut() {
            tracing::info!("inferencing {:?}", ast.path);
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
    use std::path::PathBuf;

    use crate::{
        driver::Driver,
        types::{ty::Ty, types_tests},
    };

    #[test]
    fn typechecks_multiple_files() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let paths = vec![
            current_dir.join("test/fixtures/a.tlk"),
            current_dir.join("test/fixtures/b.tlk"),
        ];

        let driver = Driver::new(paths);
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        println!("{:?}", typed.phase.asts.keys().collect::<Vec<_>>());
        let ast = typed
            .phase
            .asts
            .get(&current_dir.join("test/fixtures/b.tlk"))
            .unwrap();

        assert_eq!(
            types_tests::tests::ty(1, ast, &typed.phase.type_session),
            Ty::Int
        );
    }
}
