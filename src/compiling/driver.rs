use crate::{
    ast::{self, AST},
    compiling::module::{Module, ModuleEnvironment, ModuleId, StableModuleId},
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    ir::{ir_error::IRError, lowerer::Lowerer, program::Program},
    lexer::Lexer,
    name_resolution::{
        name_resolver::{NameResolver, ResolvedNames},
        symbol::{Symbol, Symbols},
    },
    node_id::{FileID, NodeID},
    parser::Parser,
    parser_error::ParserError,
    types::{
        matcher,
        passes::{
            inference_pass::InferencePass,
            specialization_pass::{SpecializationPass, SpecializedCallee},
        },
        ty::Ty,
        type_error::TypeError,
        type_session::TypeSession,
        typed_ast::TypedAST,
        types::Types,
    },
};
use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use std::{hash::Hash, hash::Hasher};
use std::{io, path::PathBuf, rc::Rc};

pub trait DriverPhase {}

pub struct Initial {}
impl DriverPhase for Initial {}

impl DriverPhase for Parsed {}
pub struct Parsed {
    pub asts: IndexMap<Source, AST<ast::Parsed>>,
    pub diagnostics: Vec<AnyDiagnostic>,
}

pub type Exports = IndexMap<String, Symbol>;

impl DriverPhase for NameResolved {}
pub struct NameResolved {
    pub asts: IndexMap<Source, AST<crate::parsing::ast::NameResolved>>,
    pub symbols: Symbols,
    pub resolved_names: ResolvedNames,
    pub diagnostics: Vec<AnyDiagnostic>,
}

impl DriverPhase for Typed {}
pub struct Typed {
    pub ast: TypedAST<Ty>,
    pub types: Types,
    pub exports: Exports,
    pub symbols: Symbols,
    pub resolved_names: ResolvedNames,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub specialized_callees: FxHashMap<Symbol, SpecializedCallee>,
    pub specializations: FxHashMap<Symbol, Vec<Symbol>>,
    /// Maps (specialized_caller, call_site_id) -> specialized_callee.
    /// Aligns with the paper's model: each call site is a dimension, resolution maps to the callee.
    pub call_resolutions: FxHashMap<(Symbol, NodeID), Symbol>,
}

impl DriverPhase for Lowered {}
pub struct Lowered {
    pub types: Types,
    pub exports: Exports,
    pub symbol_names: FxHashMap<Symbol, String>,
    pub program: Program,
    pub diagnostics: Vec<AnyDiagnostic>,
}

#[derive(Debug)]
pub enum CompileError {
    IO(io::Error),
    Parsing(ParserError),
    Typing(TypeError),
    Lowering(IRError),
}

#[derive(Debug, Default, PartialEq)]
pub enum CompilationMode {
    Executable,
    #[default]
    Library,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum ParseMode {
    #[default]
    Strict,
    Lenient,
}

#[derive(Debug)]
pub struct DriverConfig {
    pub module_id: ModuleId,
    pub modules: Rc<ModuleEnvironment>,
    pub mode: CompilationMode,
    pub module_name: String,
    pub parse_mode: ParseMode,
    pub preserve_comments: bool,
}

impl DriverConfig {
    pub fn new(module_name: impl Into<String>) -> Self {
        Self {
            module_id: Default::default(),
            modules: Default::default(),
            mode: CompilationMode::default(),
            module_name: module_name.into(),
            parse_mode: ParseMode::default(),
            preserve_comments: false,
        }
    }

    pub fn preserve_comments(mut self, should_preserve: bool) -> Self {
        self.preserve_comments = should_preserve;
        self
    }

    pub fn executable(mut self) -> Self {
        self.mode = CompilationMode::Executable;
        self
    }

    pub fn lenient_parsing(mut self) -> Self {
        self.parse_mode = ParseMode::Lenient;
        self
    }
}

#[derive(Debug, Clone)]
pub enum SourceKind {
    File(PathBuf),
    // Just a string
    String(String),
    // Used for core, since they're not necessarily going to be on the fs
    InMemory { path: PathBuf, text: String },
}

#[derive(Debug, Clone)]
pub struct Source {
    kind: SourceKind,
}

impl PartialEq for Source {
    fn eq(&self, other: &Self) -> bool {
        use SourceKind::*;

        match (&self.kind, &other.kind) {
            (File(a), File(b)) => a == b,
            (File(a), InMemory { path: b, .. }) => a == b,
            (InMemory { path: a, .. }, File(b)) => a == b,
            (InMemory { path: a, .. }, InMemory { path: b, .. }) => a == b,

            (String(a), String(b)) => a == b,

            _ => false,
        }
    }
}

impl Eq for Source {}

impl Hash for Source {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use SourceKind::*;

        match &self.kind {
            File(path) | InMemory { path, .. } => {
                0u8.hash(state);
                path.hash(state);
            }
            String(s) => {
                1u8.hash(state);
                s.hash(state);
            }
        }
    }
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
    pub fn in_memory(path: PathBuf, text: impl Into<String>) -> Self {
        Self {
            kind: SourceKind::InMemory {
                path,
                text: text.into(),
            },
        }
    }

    pub fn path(&self) -> &str {
        #[allow(clippy::unwrap_used)]
        match &self.kind {
            SourceKind::File(path) => path.to_str().unwrap(),
            SourceKind::String(..) => ":memory:",
            SourceKind::InMemory { path, .. } => path.to_str().unwrap(),
        }
    }

    pub fn read(&self) -> Result<String, CompileError> {
        match &self.kind {
            SourceKind::File(path) => std::fs::read_to_string(path).map_err(CompileError::IO),
            SourceKind::String(string) => Ok(string.to_string()),
            SourceKind::InMemory { text, .. } => Ok(text.clone()),
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
        #[allow(clippy::unwrap_used)]
        let mut modules = Rc::into_inner(config.modules).unwrap();
        modules.import_core(super::core::compile());
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
        let mut diagnostics = vec![];

        for (i, file) in self.files.iter().enumerate() {
            let input = file.read()?;
            let lexer = if self.config.preserve_comments {
                Lexer::preserving_comments(&input)
            } else {
                Lexer::new(&input)
            };
            tracing::info!("parsing {file:?}");
            let file_id = FileID(i as u32);
            let parser = Parser::new(file.path(), file_id, lexer);
            match parser.parse() {
                Ok((parsed, ast_diagnostics)) => {
                    diagnostics.extend(ast_diagnostics);
                    asts.insert(file.clone(), parsed);
                }
                Err(err) => {
                    if self.config.parse_mode == ParseMode::Strict {
                        return Err(CompileError::Parsing(err));
                    }

                    diagnostics.push(
                        Diagnostic {
                            id: NodeID(file_id, 0),
                            severity: Severity::Error,
                            kind: err,
                        }
                        .into(),
                    );
                    asts.insert(
                        file.clone(),
                        AST::<ast::Parsed> {
                            path: file.path().to_string(),
                            roots: vec![],
                            meta: Default::default(),
                            phase: ast::Parsed,
                            node_ids: Default::default(),
                            synthsized_ids: Default::default(),
                            file_id,
                        },
                    );
                }
            }
        }

        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: Parsed { asts, diagnostics },
        })
    }
}

impl Driver<Parsed> {
    pub fn resolve_names(mut self) -> Result<Driver<NameResolved>, CompileError> {
        let mut resolver = NameResolver::new(self.config.modules.clone(), self.config.module_id);

        let (paths, asts): (Vec<_>, Vec<_>) = self.phase.asts.into_iter().unzip();
        let (asts, resolved) = resolver.resolve(asts);
        let asts = paths.into_iter().zip(asts).collect();
        self.phase.diagnostics.extend(resolver.phase.diagnostics);

        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: NameResolved {
                asts,
                symbols: resolver.symbols,
                resolved_names: resolved,
                diagnostics: self.phase.diagnostics,
            },
        })
    }
}

fn has_error_diagnostics(diagnostics: &[AnyDiagnostic]) -> bool {
    diagnostics.iter().any(|diag| match diag {
        AnyDiagnostic::Parsing(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::NameResolution(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::Typing(diagnostic) => diagnostic.severity == Severity::Error,
    })
}

impl Driver<NameResolved> {
    pub fn typecheck(mut self) -> Result<Driver<Typed>, CompileError> {
        let mut session = TypeSession::new(
            self.config.module_id,
            self.config.modules.clone(),
            std::mem::take(&mut self.phase.symbols),
            std::mem::take(&mut self.phase.resolved_names),
        );

        let (_paths, mut asts): (Vec<_>, Vec<_>) = self.phase.asts.iter_mut().unzip();

        let (ast, diagnostics) = InferencePass::drive(&mut asts, &mut session);

        self.phase.diagnostics.extend(diagnostics);
        let symbols = std::mem::take(&mut session.symbols);
        let (types, resolved_names) = session.finalize().map_err(CompileError::Typing)?;

        let specialization_pass =
            SpecializationPass::new(ast, symbols, resolved_names, types, &self.config.modules);

        let (ast, symbols, resolved_names, mut types, specializations, specialized_callees, call_resolutions) =
            specialization_pass.drive().map_err(CompileError::Typing)?;

        // Don't bother with matcher diagnostics if we're not well typed already.
        if !has_error_diagnostics(&self.phase.diagnostics) {
            let matcher_result = matcher::check_ast(&ast, &types, &resolved_names.symbol_names);
            self.phase.diagnostics.extend(
                matcher_result
                    .diagnostics
                    .into_iter()
                    .map(AnyDiagnostic::Typing),
            );
            types.match_plans = matcher_result.plans;
        }

        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: Typed {
                ast,
                types,
                exports: resolved_names.exports(),
                symbols,
                resolved_names,
                diagnostics: self.phase.diagnostics,
                specializations,
                specialized_callees,
                call_resolutions,
            },
        })
    }
}

impl Driver<Typed> {
    pub fn lower(mut self) -> Result<Driver<Lowered>, CompileError> {
        let lowerer = Lowerer::new(&mut self.phase, &self.config);
        let program = lowerer.lower().map_err(CompileError::Lowering)?;

        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: Lowered {
                symbol_names: self.phase.resolved_names.symbol_names,
                types: self.phase.types,
                exports: self.phase.exports,
                program,
                diagnostics: self.phase.diagnostics,
            },
        })
    }
}

impl Driver<Lowered> {
    pub fn display_symbol_names(&self) -> FxHashMap<Symbol, String> {
        let mut names = self.phase.symbol_names.clone();
        for (sym, name) in self.config.modules.imported_symbol_names() {
            names.entry(sym).or_insert(name);
        }
        names
    }

    pub fn module<T: Into<String>>(self, name: T) -> Module {
        Module {
            id: StableModuleId::generate(&self.phase.exports),
            name: name.into(),
            types: self.phase.types,
            exports: self.phase.exports,
            program: self.phase.program,
            symbol_names: self.phase.symbol_names,
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
            Source::from(current_dir.join("dev/fixtures/a.tlk")),
            Source::from(current_dir.join("dev/fixtures/b.tlk")),
        ];

        let driver = Driver::new(paths, DriverConfig::new("TestDriver"));
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let ast = typed.phase.ast;
        assert!(typed.phase.diagnostics.is_empty());
        assert_eq!(types_tests::tests::ty(0, &ast, &typed.phase.types), Ty::Int);
    }

    #[test]
    fn typechecks_multiple_files_out_of_order() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let paths = vec![
            Source::from(current_dir.join("dev/fixtures/b.tlk")),
            Source::from(current_dir.join("dev/fixtures/a.tlk")),
        ];

        let driver = Driver::new(paths, DriverConfig::new("TestDriver"));
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let ast = typed.phase.ast;

        assert!(
            typed.phase.diagnostics.is_empty(),
            "{:?}",
            typed.phase.diagnostics
        );
        assert_eq!(types_tests::tests::ty(0, &ast, &typed.phase.types), Ty::Int);
    }

    #[test]
    fn conformances_across_modules() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

        let driver_a = Driver::new(
            vec![Source::from(current_dir.join("dev/fixtures/protocol.tlk"))],
            DriverConfig::new("TestDriver"),
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
        module_environment.import(module_a);
        let config = DriverConfig {
            module_id: ModuleId::Current,
            modules: Rc::new(module_environment),
            mode: CompilationMode::Library,
            module_name: "Test".to_string(),
            parse_mode: ParseMode::Strict,
            preserve_comments: false,
        };

        let driver_b = Driver::new(
            vec![Source::from(
                current_dir.join("dev/fixtures/conformance.tlk"),
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
        let ast = typed.phase.ast;

        assert_eq!(types_tests::tests::ty(0, &ast, &typed.phase.types), Ty::Int);
    }

    #[test]
    fn compiles_module() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

        let driver_a = Driver::new(
            vec![Source::from(current_dir.join("dev/fixtures/a.tlk"))],
            DriverConfig::new("TestDriver"),
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
        module_environment.import(module_a);
        let config = DriverConfig {
            module_id: ModuleId::Current,
            modules: Rc::new(module_environment),
            mode: CompilationMode::Library,
            module_name: "Test".to_string(),
            parse_mode: ParseMode::Strict,
            preserve_comments: false,
        };

        let driver_b = Driver::new(
            vec![Source::from(current_dir.join("dev/fixtures/b.tlk"))],
            config,
        );

        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();
        let ast = typed.phase.ast;

        assert_eq!(types_tests::tests::ty(0, &ast, &typed.phase.types), Ty::Int);
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
            DriverConfig::new("TestDriver"),
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
        module_environment.import(module_a);
        let config = DriverConfig {
            module_id: ModuleId::Current,
            modules: Rc::new(module_environment),
            mode: CompilationMode::Library,
            module_name: "Test".to_string(),
            parse_mode: ParseMode::Strict,
            preserve_comments: false,
        };

        let driver_b = Driver::new(vec![Source::from("Hello(x: 123).x")], config);

        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();
        let ast = typed.phase.ast;

        assert_eq!(types_tests::tests::ty(0, &ast, &typed.phase.types), Ty::Int);
    }
}
