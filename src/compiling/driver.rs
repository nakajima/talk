use std::{io, path::PathBuf, rc::Rc};

use rustc_hash::FxHashMap;

use crate::{
    ast::{self, AST},
    compiling::module::ModuleEnvironment,
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
    pub asts: FxHashMap<Source, AST<ast::Parsed>>,
}

impl DriverPhase for NameResolved {}
pub struct NameResolved {
    pub asts: FxHashMap<Source, AST<name_resolver::NameResolved>>,
}

impl DriverPhase for Typed {}
pub struct Typed {
    pub asts: FxHashMap<Source, AST<name_resolver::NameResolved>>,
    pub type_session: TypeSession,
}

#[derive(Debug)]
pub enum CompileError {
    IO(io::Error),
    Parsing(ParserError),
}

#[derive(Debug, Default)]
pub struct DriverConfig {
    modules: Rc<ModuleEnvironment>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum SourceKind {
    File(PathBuf),
    String(String),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Source {
    kind: SourceKind,
}

impl From<PathBuf> for Source {
    fn from(value: PathBuf) -> Self {
        Source {
            kind: SourceKind::File(value),
        }
    }
}

impl From<&str> for Source {
    fn from(value: &str) -> Self {
        Source {
            kind: SourceKind::String(value.to_string()),
        }
    }
}

impl Source {
    pub fn path(&self) -> &str {
        match &self.kind {
            SourceKind::File(path) => path.to_str().unwrap(),
            SourceKind::String(..) => ":memory:",
        }
    }

    pub fn read(&self) -> Result<String, CompileError> {
        match &self.kind {
            SourceKind::File(path) => std::fs::read_to_string(path).map_err(CompileError::IO),
            SourceKind::String(string) => Ok(string.to_string()),
        }
    }
}

pub struct Driver<Phase: DriverPhase = Initial> {
    files: Vec<Source>,
    config: DriverConfig,
    phase: Phase,
}

impl Driver {
    pub fn new(files: Vec<Source>, config: DriverConfig) -> Self {
        Self {
            files,
            phase: Initial {},
            config,
        }
    }

    pub fn parse(self) -> Result<Driver<Parsed>, CompileError> {
        let mut asts: FxHashMap<Source, AST<_>> = FxHashMap::default();

        for (i, file) in self.files.iter().enumerate() {
            let input = file.read()?;
            let lexer = Lexer::new(&input);
            tracing::info!("parsing {file:?}");
            let parser = Parser::new(file.path(), FileID(i as u32), lexer);
            asts.insert(file.clone(), parser.parse().map_err(CompileError::Parsing)?);
        }

        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: Parsed { asts },
        })
    }
}

impl Driver<Parsed> {
    pub fn resolve_names(self) -> Result<Driver<NameResolved>, CompileError> {
        let mut resolver = NameResolver::new(self.config.modules.clone());

        let (paths, asts): (Vec<_>, Vec<_>) = self.phase.asts.into_iter().unzip();
        let resolved = resolver.resolve(asts);

        let asts = paths.into_iter().zip(resolved).collect();

        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: NameResolved { asts },
        })
    }
}

impl Driver<NameResolved> {
    pub fn typecheck(mut self) -> Result<Driver<Typed>, CompileError> {
        let mut type_session = TypeSession::new(self.config.modules.clone());

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
            config: self.config,
            phase: Typed {
                asts: self.phase.asts,
                type_session,
            },
        })
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::{
        compiling::module::{Module, ModuleId},
        fxhashmap,
        name_resolution::symbol::{GlobalId, ProtocolId, Symbol, TypeId},
        node_id::NodeID,
        types::{ty::Ty, types_tests},
    };
    use std::path::PathBuf;

    #[test]
    fn typechecks_multiple_files() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let paths = vec![
            Source::from(current_dir.join("test/fixtures/a.tlk")),
            Source::from(current_dir.join("test/fixtures/b.tlk")),
        ];

        let driver = Driver::new(paths, Default::default());
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let ast = typed
            .phase
            .asts
            .get(&current_dir.join("test/fixtures/b.tlk").into())
            .unwrap();

        assert_eq!(
            types_tests::tests::ty(1, ast, &typed.phase.type_session.finalize().unwrap()),
            Ty::Int
        );
    }

    #[test]
    fn typechecks_multiple_files_out_of_order() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let paths = vec![
            Source::from(current_dir.join("test/fixtures/b.tlk")),
            Source::from(current_dir.join("test/fixtures/a.tlk")),
        ];

        let driver = Driver::new(paths, Default::default());
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let ast = typed
            .phase
            .asts
            .get(&Source::from(current_dir.join("test/fixtures/b.tlk")))
            .unwrap();

        assert_eq!(
            types_tests::tests::ty(1, ast, &typed.phase.type_session.finalize().unwrap()),
            Ty::Int
        );
    }

    #[test]
    fn conformances_across_modules() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

        let driver_a = Driver::new(
            vec![Source::from(current_dir.join("test/fixtures/protocol.tlk"))],
            Default::default(),
        );
        let type_session_a = driver_a
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap()
            .phase
            .type_session;

        let module_a = Module {
            name: "A".into(),
            types: type_session_a.finalize().unwrap(),
            exports: fxhashmap!(
                "P".into() => Symbol::Protocol(ProtocolId::from(1)),
                "getRequired".into() => Symbol::Global(GlobalId::from(1))
            ),
        };

        let mut module_environment = ModuleEnvironment::default();
        module_environment.import(ModuleId::External(0), module_a);
        let config = DriverConfig {
            modules: Rc::new(module_environment),
        };

        let driver_b = Driver::new(
            vec![Source::from(
                current_dir.join("test/fixtures/conformance.tlk"),
            )],
            config,
        );

        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();
        let ast = typed
            .phase
            .asts
            .get(&Source::from(
                current_dir.join("test/fixtures/conformance.tlk"),
            ))
            .unwrap();

        assert_eq!(
            types_tests::tests::ty(2, ast, &typed.phase.type_session.finalize().unwrap()),
            Ty::Int
        );
    }

    #[test]
    fn compiles_module() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

        let driver_a = Driver::new(
            vec![Source::from(current_dir.join("test/fixtures/a.tlk"))],
            Default::default(),
        );
        let type_session_a = driver_a
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap()
            .phase
            .type_session;

        let module_a = Module {
            name: "A".into(),
            types: type_session_a.finalize().unwrap(),
            exports: fxhashmap!("A".into() => Symbol::Type(TypeId::from(1))),
        };

        let mut module_environment = ModuleEnvironment::default();
        module_environment.import(ModuleId::External(0), module_a);
        let config = DriverConfig {
            modules: Rc::new(module_environment),
        };

        let driver_b = Driver::new(
            vec![Source::from(current_dir.join("test/fixtures/b.tlk"))],
            config,
        );

        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();
        let ast = typed
            .phase
            .asts
            .get(&Source::from(current_dir.join("test/fixtures/b.tlk")))
            .unwrap();

        assert_eq!(
            types_tests::tests::ty(1, ast, &typed.phase.type_session.finalize().unwrap()),
            Ty::Int
        );
    }

    #[test]
    fn compiles_from_string() {
        let driver_a = Driver::new(
            vec![Source::from(
                "
            struct Hello {
                let x: Int
            }
            ",
            )],
            Default::default(),
        );

        let name_resolved = driver_a.parse().unwrap().resolve_names().unwrap();

        let exports =
            name_resolved
                .phase
                .asts
                .values()
                .fold(FxHashMap::default(), |mut acc, ast| {
                    println!("scopes: {:?}", ast.phase.scopes);
                    let root = ast.phase.scopes.get(&NodeID(FileID(0), 0)).unwrap();
                    for (string, sym) in root.types.iter() {
                        acc.insert(string.to_string(), *sym);
                    }

                    for (string, sym) in root.values.iter() {
                        acc.insert(string.to_string(), *sym);
                    }

                    acc
                });

        let type_session_a = name_resolved.typecheck().unwrap().phase.type_session;

        let module_a = Module {
            name: "A".into(),
            types: type_session_a.finalize().unwrap(),
            exports,
        };

        let mut module_environment = ModuleEnvironment::default();
        module_environment.import(ModuleId::External(0), module_a);
        let config = DriverConfig {
            modules: Rc::new(module_environment),
        };

        let driver_b = Driver::new(vec![Source::from("Hello(x: 123).x")], config);

        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();
        let ast = typed
            .phase
            .asts
            .get(&Source::from("Hello(x: 123).x"))
            .unwrap();

        assert_eq!(
            types_tests::tests::ty(0, ast, &typed.phase.type_session.finalize().unwrap()),
            Ty::Int
        );
    }
}
