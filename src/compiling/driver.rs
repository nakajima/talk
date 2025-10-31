use std::{io, path::PathBuf, rc::Rc};

use indexmap::IndexMap;

use crate::{
    ast::{self, AST},
    compiling::module::{Module, ModuleEnvironment, ModuleId},
    ir::{ir_error::IRError, lowerer::Lowerer, program::Program},
    lexer::Lexer,
    name_resolution::{
        name_resolver::{self, NameResolver},
        symbol::{Symbol, Symbols},
    },
    node_id::{FileID, NodeID},
    parser::Parser,
    parser_error::ParserError,
    types::{
        passes::{elaboration_pass::ElaborationPass, inference_pass::InferencePass},
        type_error::TypeError,
        type_session::{TypeSession, Types},
    },
};

pub trait DriverPhase {}

pub struct Initial {}
impl DriverPhase for Initial {}

impl DriverPhase for Parsed {}
pub struct Parsed {
    pub asts: IndexMap<Source, AST<ast::Parsed>>,
}

type Exports = IndexMap<String, Symbol>;

impl DriverPhase for NameResolved {}
pub struct NameResolved {
    pub asts: IndexMap<Source, AST<name_resolver::NameResolved>>,
    pub symbols: Symbols,
}

impl DriverPhase for Typed {}
pub struct Typed {
    pub asts: IndexMap<Source, AST<name_resolver::NameResolved>>,
    pub types: Types,
    pub exports: Exports,
    pub symbols: Symbols,
}

impl DriverPhase for Lowered {}
pub struct Lowered {
    pub asts: IndexMap<Source, AST<name_resolver::NameResolved>>,
    pub types: Types,
    pub exports: Exports,
    pub symbols: Symbols,
    pub program: Program,
}

#[derive(Debug)]
pub enum CompileError {
    IO(io::Error),
    Parsing(ParserError),
    Typing(TypeError),
    Lowering(IRError),
}

#[derive(Debug, Default)]
pub enum CompilationMode {
    Executable,
    #[default]
    Library,
}

#[derive(Debug, Default)]
pub struct DriverConfig {
    pub module_id: ModuleId,
    pub modules: Rc<ModuleEnvironment>,
    pub mode: CompilationMode,
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
    pub config: DriverConfig,
    pub phase: Phase,
}

impl Driver {
    pub fn new(files: Vec<Source>, mut config: DriverConfig) -> Self {
        let mut modules = Rc::into_inner(config.modules).unwrap();
        modules.import(ModuleId::Core, super::core::compile());
        config.modules = Rc::new(modules);

        Self {
            files,
            phase: Initial {},
            config,
        }
    }

    pub fn new_bare(files: Vec<Source>, config: DriverConfig) -> Self {
        Self {
            files,
            phase: Initial {},
            config,
        }
    }

    pub fn parse(self) -> Result<Driver<Parsed>, CompileError> {
        let mut asts: IndexMap<Source, AST<_>> = IndexMap::default();

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
        let mut resolver = NameResolver::new(self.config.modules.clone(), self.config.module_id);

        let (paths, asts): (Vec<_>, Vec<_>) = self.phase.asts.into_iter().unzip();
        let resolved = resolver.resolve(asts);

        let asts = paths.into_iter().zip(resolved).collect();

        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: NameResolved {
                asts,
                symbols: resolver.symbols,
            },
        })
    }
}

impl Driver<NameResolved> {
    pub fn exports(&self) -> Exports {
        self.phase
            .asts
            .values()
            .fold(IndexMap::default(), |mut acc, ast| {
                let root = ast.phase.scopes.get(&NodeID(FileID(0), 0)).unwrap();
                for (string, sym) in root.types.iter() {
                    acc.insert(string.to_string(), *sym);
                }

                for (string, sym) in root.values.iter() {
                    acc.insert(string.to_string(), *sym);
                }

                acc
            })
    }

    pub fn typecheck(self) -> Result<Driver<Typed>, CompileError> {
        let mut session = TypeSession::new(self.config.module_id, self.config.modules.clone());
        let exports = self.exports();

        let (paths, mut asts): (Vec<_>, Vec<_>) = self.phase.asts.into_iter().unzip();
        ElaborationPass::drive(&asts, &mut session);
        InferencePass::drive(&mut asts, &mut session);
        let asts: IndexMap<Source, AST<_>> = paths.into_iter().zip(asts).collect();

        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: Typed {
                asts,
                types: session.finalize().map_err(CompileError::Typing)?,
                exports,
                symbols: self.phase.symbols,
            },
        })
    }
}

impl Driver<Typed> {
    pub fn lower(mut self) -> Result<Driver<Lowered>, CompileError> {
        let lowerer = Lowerer::new(
            &mut self.phase.asts,
            &mut self.phase.types,
            &mut self.phase.symbols,
            &self.config.modules,
        );
        let program = lowerer.lower().map_err(CompileError::Lowering)?;
        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: Lowered {
                asts: self.phase.asts,
                types: self.phase.types,
                exports: self.phase.exports,
                symbols: self.phase.symbols,
                program,
            },
        })
    }
}

impl Driver<Lowered> {
    pub fn module<T: Into<String>>(self, name: T) -> Module {
        Module {
            name: name.into(),
            types: self.phase.types,
            exports: self.phase.exports,
            program: self.phase.program,
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::{
        compiling::module::ModuleId,
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
            .get(&Source::from(current_dir.join("test/fixtures/b.tlk")))
            .unwrap();

        assert_eq!(types_tests::tests::ty(1, ast, &typed.phase.types), Ty::Int);
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

        assert_eq!(types_tests::tests::ty(1, ast, &typed.phase.types), Ty::Int);
    }

    #[test]
    fn conformances_across_modules() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

        let driver_a = Driver::new(
            vec![Source::from(current_dir.join("test/fixtures/protocol.tlk"))],
            Default::default(),
        );

        let typed_a = driver_a
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let module_a = typed_a.lower().unwrap().module("A");
        let mut module_environment = ModuleEnvironment::default();
        module_environment.import(ModuleId::External(0), module_a);
        let config = DriverConfig {
            module_id: ModuleId::Current,
            modules: Rc::new(module_environment),
            mode: CompilationMode::Library,
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

        assert_eq!(types_tests::tests::ty(2, ast, &typed.phase.types), Ty::Int);
    }

    #[test]
    fn compiles_module() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

        let driver_a = Driver::new(
            vec![Source::from(current_dir.join("test/fixtures/a.tlk"))],
            Default::default(),
        );
        let typed_a = driver_a
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let module_a = typed_a.lower().unwrap().module("A");
        let mut module_environment = ModuleEnvironment::default();
        module_environment.import(ModuleId::External(0), module_a);
        let config = DriverConfig {
            module_id: ModuleId::Current,
            modules: Rc::new(module_environment),
            mode: CompilationMode::Library,
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

        assert_eq!(types_tests::tests::ty(1, ast, &typed.phase.types), Ty::Int);
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

        let module_a = driver_a
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap()
            .lower()
            .unwrap()
            .module("A");

        let mut module_environment = ModuleEnvironment::default();
        module_environment.import(ModuleId::External(0), module_a);
        let config = DriverConfig {
            module_id: ModuleId::Current,
            modules: Rc::new(module_environment),
            mode: CompilationMode::Library,
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

        assert_eq!(types_tests::tests::ty(0, ast, &typed.phase.types), Ty::Int);
    }
}
