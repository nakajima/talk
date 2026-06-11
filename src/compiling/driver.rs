use crate::{
    ast::{self, AST},
    compiling::module::{Module, ModuleEnvironment, ModuleId, ModuleTypes, StableModuleId},
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    lexer::Lexer,
    name_resolution::{
        name_resolver::{NameResolver, ResolvedNames},
        symbol::{Symbol, Symbols},
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::decl::{DeclKind, ImportPath},
    parser::Parser,
    parser_error::ParserError,
    types::TypeOutput,
};
use indexmap::IndexMap;
use rustc_hash::FxHashSet;
use std::collections::VecDeque;
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

impl DriverPhase for Lowered {}
pub struct Lowered {
    pub program: crate::lambda_g::Program,
    pub main: crate::lambda_g::Label,
    pub result_ty: crate::lambda_g::expr::TyId,
    /// Chunk-forming function labels (demanded specializations + main);
    /// the scheduler turns everything else into blocks.
    pub entry_funcs: rustc_hash::FxHashSet<crate::lambda_g::Label>,
    /// Lowering issues (constructs the backend does not support yet).
    pub diagnostics: Vec<String>,
    pub prior_diagnostics: Vec<AnyDiagnostic>,
}

impl DriverPhase for Typed {}
pub struct Typed {
    pub asts: IndexMap<Source, AST<crate::parsing::ast::NameResolved>>,
    pub symbols: Symbols,
    pub resolved_names: ResolvedNames,
    pub types: TypeOutput,
    pub diagnostics: Vec<AnyDiagnostic>,
}

#[derive(Debug)]
pub enum CompileError {
    IO(io::Error),
    Parsing(ParserError),
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
            SourceKind::File(path) => std::fs::read_to_string(path).map_err(|e| {
                CompileError::IO(std::io::Error::new(
                    e.kind(),
                    format!("{}: {e}", path.display()),
                ))
            }),
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

/// Extract all import paths from a parsed AST
fn extract_import_paths(ast: &AST<ast::Parsed>) -> Vec<ImportPath> {
    let mut paths = Vec::new();
    for root in &ast.roots {
        if let Node::Decl(decl) = root
            && let DeclKind::Import(import) = &decl.kind
        {
            paths.push(import.path.clone());
        }
    }
    paths
}

/// Resolve an import path relative to a source file path.
/// Returns a tuple of (normalized_path for tracking, resolved_path for the source).
/// The resolved_path preserves the relative/absolute nature of the source_path.
fn resolve_import_path(source_path: &str, import_path: &ImportPath) -> Option<(PathBuf, PathBuf)> {
    match import_path {
        ImportPath::Relative(rel_path) => {
            // source_path is the file containing the import
            let source = PathBuf::from(source_path);
            let parent = source.parent()?;

            // Strip leading "./" from relative path before joining (to match name resolver)
            let clean_rel = rel_path.strip_prefix("./").unwrap_or(rel_path);
            let resolved = parent.join(clean_rel);

            // Canonicalize for cycle detection (normalizes .. and symlinks)
            let canonical = resolved.canonicalize().ok()?;

            // Return both the canonical path (for tracking) and the resolved path (for source)
            Some((canonical, resolved))
        }
        ImportPath::Package(_) => {
            // Package imports are handled by the module system, not file discovery
            None
        }
    }
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

        // Track which files we've already processed (by canonical path) to detect cycles
        let mut processed_paths: FxHashSet<PathBuf> = FxHashSet::default();

        // Queue of files to parse - use VecDeque for FIFO ordering
        let mut to_parse: VecDeque<Source> = self.files.iter().cloned().collect();

        // Mark initial files as processed
        for file in &self.files {
            match &file.kind {
                SourceKind::File(path) => {
                    if let Ok(canonical) = path.canonicalize() {
                        processed_paths.insert(canonical);
                    }
                }
                SourceKind::InMemory { path, .. } => {
                    // For in-memory sources, try to canonicalize if the file exists on disk
                    if let Ok(canonical) = path.canonicalize() {
                        processed_paths.insert(canonical);
                    }
                }
                SourceKind::String(_) => {
                    // String sources don't have paths, nothing to track
                }
            }
        }

        let mut file_index = 0u32;

        while let Some(file) = to_parse.pop_front() {
            let input = file.read()?;
            let lexer = if self.config.preserve_comments {
                Lexer::preserving_comments(&input)
            } else {
                Lexer::new(&input)
            };
            tracing::info!("parsing {file:?}");
            let file_id = FileID(file_index);
            file_index += 1;
            let parser = Parser::new(file.path(), file_id, lexer);
            match parser.parse() {
                Ok((mut parsed, ast_diagnostics)) => {
                    parsed.skip_core_prelude = input.starts_with("// no-core");
                    diagnostics.extend(ast_diagnostics);

                    // Discover imports and queue them for parsing
                    let source_path = file.path();
                    for import_path in extract_import_paths(&parsed) {
                        if let Some((canonical, resolved)) =
                            resolve_import_path(source_path, &import_path)
                            && !processed_paths.contains(&canonical)
                        {
                            processed_paths.insert(canonical);
                            to_parse.push_back(Source::from(resolved));
                        }
                    }

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
                            skip_core_prelude: false,
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
        AnyDiagnostic::Types(diagnostic) => diagnostic.severity == Severity::Error,
    })
}

impl Driver<NameResolved> {
    pub fn has_errors(&self) -> bool {
        has_error_diagnostics(&self.phase.diagnostics)
    }

    pub fn diagnostics(&self) -> &[AnyDiagnostic] {
        &self.phase.diagnostics
    }

    pub fn module<T: Into<String>>(self, name: T) -> Module {
        let exports = self.phase.resolved_names.exports();
        Module {
            id: StableModuleId::generate(&exports),
            name: name.into(),
            symbol_names: self.phase.resolved_names.symbol_names,
            exports,
            types: ModuleTypes::default(),
        }
    }

    /// Type check: generate constraints and solve them per SCC binding group
    /// (see src/types). Infallible — failures surface as diagnostics.
    pub fn type_check(self) -> Driver<Typed> {
        let NameResolved {
            asts,
            mut symbols,
            resolved_names,
            mut diagnostics,
        } = self.phase;

        let (types, type_diagnostics) = crate::types::generate::check_types(
            &asts,
            &mut symbols,
            &resolved_names,
            &self.config.modules,
            self.config.module_id,
        );
        diagnostics.extend(type_diagnostics);

        Driver {
            files: self.files,
            config: self.config,
            phase: Typed {
                asts,
                symbols,
                resolved_names,
                types,
                diagnostics,
            },
        }
    }
}

impl Driver<Typed> {
    /// Lower to λ_G (whole-program, with core's typed artifacts — see
    /// src/lower). Infallible; unsupported constructs surface as lowering
    /// diagnostics.
    pub fn lower(self) -> Driver<Lowered> {
        use crate::lower::{LowerUnit, lower_program};

        let Typed {
            asts,
            symbols: _,
            resolved_names,
            types,
            diagnostics,
        } = self.phase;

        let core = if self.config.module_id == ModuleId::Core {
            None
        } else {
            Some(crate::compiling::core::typed())
        };
        let mut units = vec![];
        if let Some(core) = core.as_ref() {
            units.push(LowerUnit {
                asts: &core.asts,
                types: &core.types,
                resolved: &core.resolved_names,
            });
        }
        units.push(LowerUnit {
            asts: &asts,
            types: &types,
            resolved: &resolved_names,
        });
        let entry = units.len() - 1;
        let lowered = lower_program(units, entry);

        Driver {
            files: self.files,
            config: self.config,
            phase: Lowered {
                program: lowered.program,
                main: lowered.main,
                result_ty: lowered.result_ty,
                entry_funcs: lowered.entry_funcs,
                diagnostics: lowered.diagnostics,
                prior_diagnostics: diagnostics,
            },
        }
    }

    pub fn has_errors(&self) -> bool {
        has_error_diagnostics(&self.phase.diagnostics)
    }

    pub fn diagnostics(&self) -> &[AnyDiagnostic] {
        &self.phase.diagnostics
    }

    /// Build a module carrying its type payload: every binder's scheme
    /// (sanitized for export — solver variables don't travel) plus this
    /// module's slice of the type catalog.
    pub fn module<T: Into<String>>(self, name: T) -> Module {
        let exports = self.phase.resolved_names.exports();
        let schemes = self
            .phase
            .types
            .schemes
            .into_iter()
            .map(|(symbol, scheme)| {
                let ty = scheme.ty.sanitize_for_export(symbol);
                (symbol, crate::types::ty::Scheme { ty, ..scheme })
            })
            .collect();
        Module {
            id: StableModuleId::generate(&exports),
            name: name.into(),
            symbol_names: self.phase.resolved_names.symbol_names,
            exports,
            types: ModuleTypes {
                schemes,
                catalog: self.phase.types.catalog,
            },
        }
    }
}

impl Driver<Lowered> {
    /// Execute on the reference evaluator (the trusted baseline the
    /// bytecode VM is tested against). Mutates the program (substitution
    /// adds functions), so schedule for the VM *before* running the
    /// evaluator.
    pub fn eval_for_tests(
        &mut self,
    ) -> Result<crate::lambda_g::eval::EvalValue, crate::lambda_g::eval::EvalError> {
        Ok(self.eval_with_output()?.0)
    }

    /// Reference-evaluator run returning (value, captured stdout).
    pub fn eval_with_output(
        &mut self,
    ) -> Result<(crate::lambda_g::eval::EvalValue, String), crate::lambda_g::eval::EvalError> {
        let mut evaluator = crate::lambda_g::eval::Evaluator::new();
        let value = evaluator.run_main(
            &mut self.phase.program,
            self.phase.main,
            self.phase.result_ty,
        )?;
        Ok((value, String::from_utf8_lossy(&evaluator.out).into_owned()))
    }

    /// Schedule to bytecode and execute on the VM against host stdio.
    pub fn run_vm(&self) -> Result<crate::vm::interp::Value, String> {
        let module = self.schedule()?;
        let mut io = crate::vm::io::StdioIO;
        crate::vm::interp::run(&module, &mut io)
    }

    /// VM run returning (value, captured stdout) — tests and the REPL.
    pub fn run_vm_with_output(&self) -> Result<(crate::vm::interp::Value, String), String> {
        let module = self.schedule()?;
        let mut io = crate::vm::io::CaptureIO::default();
        let value = crate::vm::interp::run(&module, &mut io)?;
        Ok((value, String::from_utf8_lossy(&io.out).into_owned()))
    }

    fn schedule(&self) -> Result<crate::vm::Module, String> {
        crate::vm::schedule::schedule(
            &self.phase.program,
            self.phase.main,
            &self.phase.entry_funcs,
        )
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::compiling::module::ModuleId;
    use std::path::PathBuf;

    #[test]
    fn resolves_multiple_files() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let paths = vec![
            Source::from(current_dir.join("dev/fixtures/a.tlk")),
            Source::from(current_dir.join("dev/fixtures/b.tlk")),
        ];

        let driver = Driver::new(paths, DriverConfig::new("TestDriver"));
        let resolved = driver.parse().unwrap().resolve_names().unwrap();

        assert!(
            !resolved.has_errors(),
            "{:?}",
            resolved.phase.diagnostics
        );
    }

    #[test]
    fn resolves_multiple_files_out_of_order() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let paths = vec![
            Source::from(current_dir.join("dev/fixtures/b.tlk")),
            Source::from(current_dir.join("dev/fixtures/a.tlk")),
        ];

        let driver = Driver::new(paths, DriverConfig::new("TestDriver"));
        let resolved = driver.parse().unwrap().resolve_names().unwrap();

        assert!(
            !resolved.has_errors(),
            "{:?}",
            resolved.phase.diagnostics
        );
    }

    #[test]
    fn compiles_module() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

        let driver_a = Driver::new(
            vec![Source::from(current_dir.join("dev/fixtures/a.tlk"))],
            DriverConfig::new("TestDriver"),
        );
        let resolved_a = driver_a.parse().unwrap().resolve_names().unwrap();
        assert!(!resolved_a.has_errors());

        let module_a = resolved_a.module("A");
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

        let resolved_b = driver_b.parse().unwrap().resolve_names().unwrap();
        assert!(
            !resolved_b.has_errors(),
            "{:?}",
            resolved_b.phase.diagnostics
        );
    }

    #[test]
    fn compiles_from_string() {
        let driver_a = Driver::new(
            vec![Source::from(
                "
            public struct Hello {
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
            .module("A");

        assert!(module_a.exports.contains_key("Hello"));

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

        let resolved_b = driver_b.parse().unwrap().resolve_names().unwrap();
        assert!(
            !resolved_b.has_errors(),
            "{:?}",
            resolved_b.phase.diagnostics
        );
    }

    #[test]
    fn auto_discovers_imports() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let importer_path = current_dir.join("dev/fixtures/importer.tlk");
        let exportee_path = current_dir.join("dev/fixtures/exportee.tlk");

        // Create the test files
        std::fs::write(&exportee_path, "public let exported = 42\n").unwrap();
        std::fs::write(
            &importer_path,
            "import { exported } from ./exportee.tlk\nexported\n",
        )
        .unwrap();

        // Only pass the importer file - the exportee should be auto-discovered
        let driver = Driver::new(
            vec![Source::from(importer_path.clone())],
            DriverConfig::new("TestDriver"),
        );
        let parsed = driver.parse().unwrap();

        // Both files should be parsed
        assert_eq!(
            parsed.phase.asts.len(),
            2,
            "should auto-discover imported file"
        );

        // Verify the files resolve without errors
        let resolved = parsed.resolve_names().unwrap();
        assert!(
            !resolved.has_errors(),
            "no diagnostics: {:?}",
            resolved.phase.diagnostics
        );

        // Cleanup
        let _ = std::fs::remove_file(&importer_path);
        let _ = std::fs::remove_file(&exportee_path);
    }
}
