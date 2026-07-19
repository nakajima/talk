use crate::{
    ast::{self, AST},
    compiling::{
        module::{Module, ModuleEnvironment, ModuleId, ModuleTypes, StableModuleId},
        module_path::LocalModulePaths,
    },
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    lexer::Lexer,
    name::Name,
    name_resolution::{
        name_resolver::{NameResolver, ResolvedNames},
        symbol::{Symbol, Symbols},
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        decl::{DeclKind, ImportPath},
        expr::ExprKind,
        type_annotation::TypeAnnotationKind,
    },
    parser::Parser,
    parser_error::ParserError,
};
use indexmap::IndexMap;
use rustc_hash::FxHashSet;
use std::borrow::Cow;
use std::collections::VecDeque;
use std::{hash::Hash, hash::Hasher};
use std::{
    io,
    path::{Path, PathBuf},
    rc::Rc,
};

pub trait DriverPhase {}

/// An ownership rejection: the message and, when the span maps to a
/// source document, that document's path and byte range.
pub type OwnershipRejection = (String, Option<(String, u32, u32)>);

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
    /// The final frontend artifact: a checked typed program and its semantic
    /// facts. The frontend performs no ownership analysis or code generation.
    pub program: crate::compiling::typed_program::TypedProgram,
    pub diagnostics: Vec<AnyDiagnostic>,
}

#[derive(Debug)]
pub enum CompileError {
    IO(io::Error),
    Parsing(ParserError),
    ImportOutsideWorkspace {
        source: String,
        import_path: String,
        workspace_root: PathBuf,
    },
}

#[derive(Clone, Debug, Default, PartialEq)]
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

#[derive(Clone)]
pub struct DriverConfig {
    pub module_id: ModuleId,
    pub modules: Rc<ModuleEnvironment>,
    pub mode: CompilationMode,
    pub module_name: String,
    pub parse_mode: ParseMode,
    pub preserve_comments: bool,
    pub workspace_root: Option<PathBuf>,
    pub source_root: Option<PathBuf>,
    /// Dependency libraries' typed bodies (package graphs), by the module
    /// id they were compiled and imported under. The backend compiles the
    /// reachable source graph as one unit from these.
    pub libraries: Vec<(
        ModuleId,
        std::sync::Arc<crate::compiling::typed_program::TypedProgram>,
    )>,
}

impl std::fmt::Debug for DriverConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DriverConfig")
            .field("module_id", &self.module_id)
            .field("modules", &self.modules)
            .field("mode", &self.mode)
            .field("module_name", &self.module_name)
            .field("parse_mode", &self.parse_mode)
            .field("preserve_comments", &self.preserve_comments)
            .field("workspace_root", &self.workspace_root)
            .field("source_root", &self.source_root)
            .finish()
    }
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
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        }
    }

    pub fn workspace_root(mut self, root: impl Into<PathBuf>) -> Self {
        self.workspace_root = Some(root.into());
        self
    }

    pub fn source_root(mut self, root: impl Into<PathBuf>) -> Self {
        self.source_root = Some(root.into());
        self
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

    pub fn path(&self) -> Cow<'_, str> {
        match &self.kind {
            SourceKind::File(path) => path.to_string_lossy(),
            SourceKind::String(..) => Cow::Borrowed(":memory:"),
            SourceKind::InMemory { path, .. } => path.to_string_lossy(),
        }
    }

    pub fn source_path(&self) -> Option<&Path> {
        match &self.kind {
            SourceKind::File(path) | SourceKind::InMemory { path, .. } => Some(path),
            SourceKind::String(_) => None,
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

/// Extract all module paths from imports and qualified references in a parsed AST.
fn extract_import_paths(ast: &AST<ast::Parsed>) -> Vec<ImportPath> {
    use derive_visitor::Drive;

    let mut paths = Vec::new();
    for root in &ast.roots {
        if let Node::Decl(decl) = root
            && let DeclKind::Import(import) = &decl.kind
        {
            paths.push(import.path.clone());
        }
    }

    let mut expr_collector =
        derive_visitor::visitor_enter_fn(|expr: &crate::node_kinds::expr::Expr| {
            if let ExprKind::Variable(Name::Raw(raw)) = &expr.kind
                && let Some(path) = qualified_local_module_path(raw)
            {
                paths.push(ImportPath::Local(path));
            }
        });
    for root in &ast.roots {
        root.drive(&mut expr_collector);
    }
    drop(expr_collector);

    let mut type_collector = derive_visitor::visitor_enter_fn(
        |ty: &crate::node_kinds::type_annotation::TypeAnnotation| {
            if let TypeAnnotationKind::Nominal {
                name: Name::Raw(raw),
                ..
            } = &ty.kind
                && let Some(path) = qualified_local_module_path(raw)
            {
                paths.push(ImportPath::Local(path));
            }
        },
    );
    for root in &ast.roots {
        root.drive(&mut type_collector);
    }
    drop(type_collector);

    paths
}

fn qualified_local_module_path(raw: &str) -> Option<String> {
    let (module_path, _) = raw.rsplit_once("::")?;
    LocalModulePaths::is_local(module_path).then(|| module_path.to_string())
}

/// Resolves a local module import to its source path.
fn resolve_import_path(
    source_path: &str,
    import_path: &ImportPath,
    local_modules: &LocalModulePaths,
    workspace_root: Option<&Path>,
) -> Result<Option<(PathBuf, PathBuf)>, CompileError> {
    let ImportPath::Local(module_path) = import_path else {
        // Package imports are handled by the module system, not file discovery.
        return Ok(None);
    };
    let Some(resolved) = local_modules.resolve(source_path, module_path) else {
        return Ok(None);
    };

    // Canonicalize for cycle detection (normalizes symlinks).
    let Ok(canonical) = resolved.canonicalize() else {
        return Ok(None);
    };
    if let Some(root) = workspace_root
        && !canonical.starts_with(root)
    {
        return Err(CompileError::ImportOutsideWorkspace {
            source: source_path.to_string(),
            import_path: module_path.clone(),
            workspace_root: root.to_path_buf(),
        });
    }

    // Return both the canonical path (for tracking) and the resolved path for source.
    Ok(Some((canonical, resolved)))
}

impl Driver {
    pub fn new(files: Vec<Source>, mut config: DriverConfig) -> Self {
        let compiling_stdlib_source = Self::files_are_stdlib_sources(&files);
        {
            let modules = Rc::make_mut(&mut config.modules);
            modules.import_core(super::core::compile());
            if !compiling_stdlib_source {
                for module in super::stdlib::modules() {
                    modules.import((*module).clone());
                }
            }
        }

        Self {
            files,
            phase: Initial {},
            config,
        }
    }

    fn files_are_stdlib_sources(files: &[Source]) -> bool {
        !files.is_empty()
            && files.iter().all(|source| {
                super::stdlib::module_name_for_path(Path::new(source.path().as_ref())).is_some()
            })
    }

    pub fn new_bare(files: Vec<Source>, config: DriverConfig) -> Self {
        Self {
            files,
            phase: Initial {},
            config,
        }
    }

    pub fn parse(mut self) -> Result<Driver<Parsed>, CompileError> {
        if self.config.source_root.is_none() {
            self.config.source_root = LocalModulePaths::infer_source_root(
                self.files
                    .iter()
                    .filter_map(|source| source.source_path().map(Path::to_path_buf)),
            );
        }
        let local_modules =
            LocalModulePaths::new(self.config.source_root.clone().unwrap_or_default());
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
                        if let Some((canonical, resolved)) = resolve_import_path(
                            source_path.as_ref(),
                            &import_path,
                            &local_modules,
                            self.config.workspace_root.as_deref(),
                        )? && !processed_paths.contains(&canonical)
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
        let mut resolver = NameResolver::with_source_root(
            self.config.modules.clone(),
            self.config.module_id,
            self.config.source_root.clone().unwrap_or_default(),
        );

        let (paths, mut asts): (Vec<_>, Vec<_>) = self.phase.asts.into_iter().unzip();
        crate::desugar::desugar(&mut asts);
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

/// The compiled program handed between `compile_executable` and
/// `execute_module`.
pub use crate::backend::Executable;

/// Validate and execute a serialized bytecode image (TOOL-14). Images are
/// untrusted bytes: decoding validates every index, register, and opcode
/// before execution (ADR 0034's trust seam).
pub fn execute_image(
    bytes: &[u8],
    io: &mut dyn talk_runtime::io::IO,
) -> Result<Option<String>, String> {
    let module = talk_runtime::Module::decode_bytecode(bytes)
        .map_err(|error| format!("invalid bytecode image: {error:?}"))?;
    let executable = crate::backend::Executable {
        module,
        names: Default::default(),
    };
    crate::backend::execute(&executable, io)
}

/// The backend's execution seam (ADR 0034): run a compiled program and
/// return its Talk-rendered result (`None` for Unit). Runtime failures and
/// resource leaks come back as the error message.
pub fn execute_module(
    executable: &Executable,
    io: &mut dyn talk_runtime::io::IO,
) -> Result<Option<String>, String> {
    crate::backend::execute(executable, io)
}

fn has_error_diagnostics(diagnostics: &[AnyDiagnostic]) -> bool {
    diagnostics.iter().any(|diag| match diag {
        AnyDiagnostic::Parsing(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::NameResolution(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::Types(diagnostic) => diagnostic.severity == Severity::Error,
    })
}

fn error_diagnostic_files(diagnostics: &[AnyDiagnostic]) -> FxHashSet<FileID> {
    let mut files = FxHashSet::default();
    for diag in diagnostics {
        let (id, severity) = match diag {
            AnyDiagnostic::Parsing(diagnostic) => (diagnostic.id, &diagnostic.severity),
            AnyDiagnostic::NameResolution(diagnostic) => (diagnostic.id, &diagnostic.severity),
            AnyDiagnostic::Types(diagnostic) => (diagnostic.id, &diagnostic.severity),
        };
        if *severity != Severity::Error {
            continue;
        }
        // A synthesized-id diagnostic names no file: it blocks nothing
        // rather than everything (typed-program building tolerates the odd
        // hole — a missing node type bakes as `Ty::Error`).
        if id.0 == FileID::SYNTHESIZED {
            continue;
        }
        files.insert(id.0);
    }
    files
}

impl Driver<NameResolved> {
    pub fn has_errors(&self) -> bool {
        has_error_diagnostics(&self.phase.diagnostics)
    }

    pub fn diagnostics(&self) -> &[AnyDiagnostic] {
        &self.phase.diagnostics
    }

    pub fn module<T: Into<String>>(self, name: T) -> Module {
        let name = name.into();
        let exports = self.phase.resolved_names.exports();
        Module {
            id: StableModuleId::generate(&name, &exports),
            name,
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
        let blocked_files = error_diagnostic_files(&diagnostics);
        let program = crate::compiling::typed_program::TypedProgram::from_checked_asts(
            asts,
            resolved_names,
            types,
            &blocked_files,
        );

        Driver {
            files: self.files,
            config: self.config,
            phase: Typed {
                program,
                diagnostics,
            },
        }
    }
}

impl Driver<Typed> {
    pub fn has_errors(&self) -> bool {
        has_error_diagnostics(&self.phase.diagnostics)
    }

    pub fn diagnostics(&self) -> &[AnyDiagnostic] {
        &self.phase.diagnostics
    }

    /// The backend seam (ADR 0034): compile the checked program and its
    /// reachable dependency bodies into an executable runtime module.
    ///
    /// `entry` selects a zero-parameter public function; without it the
    /// script's top-level statements run and the final top-level expression
    /// is the program result.
    pub fn compile_executable(&self, entry: Option<&str>) -> Result<Executable, String> {
        self.with_backend_inputs(entry, |programs, aliases, entry| {
            crate::backend::compile(programs, aliases, entry)
        })
        .map_err(|error| self.locate_backend_error(&error))
    }

    /// Run the ownership analysis without lowering (`talk check`). A
    /// rejection comes back with its message and, when the span maps to
    /// a source document, that document's path and byte range.
    pub fn check_ownership(&self) -> Result<(), OwnershipRejection> {
        self.with_backend_inputs(None, |programs, aliases, entry| {
            crate::backend::check(programs, aliases, entry)
        })
        .map_err(|error| {
            let span = error.span;
            if span == crate::parsing::span::Span::SYNTHESIZED {
                return (error.message.clone(), None);
            }
            for (source, file) in self.phase.program.files() {
                if file.file_id == span.file_id {
                    return (
                        error.message.clone(),
                        Some((source.path().to_string(), span.start, span.end)),
                    );
                }
            }
            (error.message.clone(), None)
        })
    }

    /// Render the backend's middle representation for inspection
    /// (TOOL-10). Same inputs as `compile_executable`.
    pub fn render_mir(&self, entry: Option<&str>) -> Result<String, String> {
        self.with_backend_inputs(entry, |programs, aliases, entry| {
            crate::backend::render_mir(programs, aliases, entry)
        })
        .map_err(|error| self.locate_backend_error(&error))
    }

    /// Assemble the reachable source graph (this program, core, imported
    /// stdlib modules, dependency libraries) and the module-alias map, and
    /// hand them to the backend.
    fn with_backend_inputs<R>(
        &self,
        entry: Option<&str>,
        run: impl FnOnce(
            &[crate::backend::ProgramInput<'_>],
            rustc_hash::FxHashMap<u16, u16>,
            crate::backend::Entry<'_>,
        ) -> R,
    ) -> R {
        let core = crate::compiling::core::typed_program();
        let entry = match entry {
            Some(name) => crate::backend::Entry::Named(name),
            None => crate::backend::Entry::Script,
        };
        let stdlib = crate::compiling::stdlib::typed_programs();
        // The user program needs a real module stamp: `Current`-tagged
        // symbols re-stamp under whichever program re-canonicalizes them
        // (a core generic instance would file a user type into core's
        // symbol space).
        let user_module = if self.config.module_id == crate::compiling::module::ModuleId::Current {
            crate::compiling::module::ModuleId::Main
        } else {
            self.config.module_id
        };
        let mut programs = vec![
            crate::backend::ProgramInput {
                program: &self.phase.program,
                module: user_module,
            },
            crate::backend::ProgramInput {
                program: &core,
                module: crate::compiling::module::ModuleId::Core,
            },
        ];
        for (name, program) in &stdlib {
            if let Some(module) = self.config.modules.get_module_id_by_name(name) {
                programs.push(crate::backend::ProgramInput { program, module });
            }
        }
        for (module, program) in &self.config.libraries {
            programs.push(crate::backend::ProgramInput {
                program,
                module: *module,
            });
        }
        // One module can carry several local ids in this environment (a
        // direct import plus a re-export); unify them by stable identity.
        let mut canonical_by_stable: rustc_hash::FxHashMap<StableModuleId, ModuleId> =
            rustc_hash::FxHashMap::default();
        let mut aliases: rustc_hash::FxHashMap<u16, u16> = rustc_hash::FxHashMap::default();
        let mut locals: Vec<(ModuleId, StableModuleId)> =
            self.config.modules.locals_with_stable_ids().collect();
        locals.sort_unstable_by_key(|(local, _)| *local);
        for (local, stable) in locals {
            let unified = *canonical_by_stable.entry(stable).or_insert(local);
            if unified != local {
                aliases.insert(local.0, unified.0);
            }
        }
        run(&programs, aliases, entry)
    }

    /// Render a backend rejection with its source location when the span
    /// points into one of this driver's files.
    fn locate_backend_error(&self, error: &crate::backend::BackendError) -> String {
        let span = error.span;
        if span == crate::parsing::span::Span::SYNTHESIZED {
            return error.message.clone();
        }
        for (source, file) in self.phase.program.files() {
            if file.file_id != span.file_id {
                continue;
            }
            let Ok(text) = source.read() else { break };
            let start = usize::try_from(span.start).unwrap_or(0).min(text.len());
            let line = text[..start].bytes().filter(|byte| *byte == b'\n').count() + 1;
            return format!("{} ({}:{line})", error.message, source.path());
        }
        error.message.clone()
    }

    /// Build a module carrying its type payload: every binder's scheme
    /// (sanitized for export — solver variables don't travel) plus this
    /// module's slice of the type catalog.
    ///
    /// Only symbols this module minted (Current-tagged) are exported. The
    /// checker's scheme map also holds every imported module's schemes,
    /// and re-exporting those is corrupting: `Module::import_as` retags
    /// every key to the importer's id for this module, so a foreign
    /// symbol and an own symbol sharing a local id would collapse onto
    /// one key, with hash order deciding which scheme survives.
    pub fn module<T: Into<String>>(self, name: T) -> Module {
        let name = name.into();
        // Own symbols carry no module tag (Current) or the id this
        // compile ran under (core compiles as ModuleId::Core).
        let compiled_as = self.config.module_id;
        let own = move |symbol: &Symbol| match symbol.module_id() {
            None => true,
            Some(id) => id == compiled_as,
        };
        let (resolved_names, types) = self.phase.program.into_semantic_parts();
        let exports = resolved_names.exports();
        let schemes = types
            .schemes
            .into_iter()
            .filter(|(symbol, _)| own(symbol))
            // Scheme-level sanitize: a leftover row/effect tail variable
            // becomes an owner-keyed param AND registers in
            // eff_params/row_params, so instantiation freshens it on the
            // importing side (a rigid tail would reject every ambient row
            // it meets — the http.run regression).
            .map(|(symbol, scheme)| (symbol, scheme.sanitize_for_export(symbol)))
            .collect();
        let symbol_names = resolved_names
            .symbol_names
            .into_iter()
            .filter(|(symbol, _)| own(symbol))
            .collect();
        #[cfg_attr(not(debug_assertions), allow(unused_mut))]
        let mut catalog = types.catalog;
        // A module's types outlive this store: nothing var-shaped may
        // cross. Finalization guarantees it through the same walk this
        // assertion re-runs; a future catalog field that skips the walk
        // fails loudly here in debug builds.
        #[cfg(debug_assertions)]
        catalog.debug_assert_portable();
        Module {
            id: StableModuleId::generate(&name, &exports),
            name,
            symbol_names,
            exports,
            types: ModuleTypes { schemes, catalog },
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::compiling::module::ModuleId;
    use std::path::PathBuf;

    #[test]
    fn typed_module_exports_only_its_own_schemes() {
        // A library's exported schemes must be keyed by its own binders
        // only. Re-exporting the merged core schemes is corrupting:
        // `Module::import_as` retags every key to the importer's id, so a
        // core symbol and one of the module's own symbols with the same
        // local id collapse onto one key — and hash order then decides
        // which scheme survives (the fs `Directory.entries` ->
        // `(&Float, Float) -> Float` bug).
        let typed = Driver::new(
            vec![Source::from(
                "public struct Tiny {\n\tlet x: Int\n\n\tfunc double() -> Int {\n\t\tself.x + self.x\n\t}\n}",
            )],
            DriverConfig::new("TinyLib"),
        )
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
        let module = typed.module("Tiny");
        let foreign: Vec<_> = module
            .types
            .schemes
            .keys()
            .filter(|symbol| symbol.external_module_id().is_some())
            .collect();
        assert!(
            foreign.is_empty(),
            "exported schemes include foreign symbols: {foreign:?}"
        );
        assert!(
            !module.types.schemes.is_empty(),
            "the module's own schemes are exported"
        );
    }

    #[test]
    fn new_does_not_import_bundled_stdlib_when_compiling_stdlib_source() {
        let (_, fs) = crate::compiling::stdlib::stdlib_sources()
            .into_iter()
            .find(|(name, _)| *name == "fs")
            .expect("fs stdlib source");
        let source = Source::in_memory("stdlib/fs.tlk".into(), fs);
        let driver = Driver::new(vec![source], DriverConfig::new("fs"));

        assert!(
            driver
                .config
                .modules
                .get_module_id_by_name("Core")
                .is_some()
        );
        assert!(
            driver.config.modules.get_module_id_by_name("fs").is_none(),
            "compiling stdlib/fs.tlk must not also import bundled fs"
        );
    }

    #[test]
    fn synthesized_error_blocks_no_file() {
        // A solver diagnostic with no origin node (NodeID::SYNTHESIZED)
        // names no file, so it must not block typed-program building for the whole
        // workspace — only diagnostics attributed to a file block that file.
        use crate::diagnostic::{AnyDiagnostic, Diagnostic, Severity};
        use crate::node_id::{FileID, NodeID};
        use crate::types::constraint::CtReason;
        use crate::types::error::TypeError;

        let mismatch = |id: NodeID| {
            AnyDiagnostic::Types(Diagnostic {
                id,
                severity: Severity::Error,
                kind: TypeError::Mismatch {
                    expected: "Int".into(),
                    found: "String".into(),
                    reason: CtReason::Annotation,
                },
            })
        };
        let diagnostics = vec![
            mismatch(NodeID::SYNTHESIZED),
            mismatch(NodeID(FileID(1), 7)),
        ];
        let blocked = error_diagnostic_files(&diagnostics);
        assert!(blocked.contains(&FileID(1)));
        assert!(
            !blocked.contains(&FileID(0)),
            "an unattributed error must not block unrelated files"
        );
    }

    #[test]
    fn resolves_multiple_files() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let paths = vec![
            Source::from(current_dir.join("dev/fixtures/a.tlk")),
            Source::from(current_dir.join("dev/fixtures/b.tlk")),
        ];

        let driver = Driver::new(paths, DriverConfig::new("TestDriver"));
        let resolved = driver.parse().unwrap().resolve_names().unwrap();

        assert!(!resolved.has_errors(), "{:?}", resolved.phase.diagnostics);
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

        assert!(!resolved.has_errors(), "{:?}", resolved.phase.diagnostics);
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
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
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
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        };

        let driver_b = Driver::new(
            vec![Source::from("use A::{ Hello }\nHello(x: 123).x")],
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
    fn imports_stdlib_modules_by_package_name() {
        let driver = Driver::new(
            vec![Source::from(
                "use fs::{ Directory, File, DirectoryEntry }\nlet dir: Directory\nlet file: File\nlet entry: DirectoryEntry\n",
            )],
            DriverConfig::new("TestDriver"),
        );

        let checked = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        assert!(!checked.has_errors(), "{:?}", checked.diagnostics());
    }

    #[test]
    fn auto_discovers_qualified_local_paths() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let importer_path = current_dir.join("dev/fixtures/qualified_importer.tlk");
        let exportee_path = current_dir.join("dev/fixtures/qualified_exportee.tlk");

        std::fs::write(&exportee_path, "public let exported = 42\n").unwrap();
        std::fs::write(&importer_path, "package::qualified_exportee::exported\n").unwrap();

        let driver = Driver::new(
            vec![Source::from(importer_path.clone())],
            DriverConfig::new("TestDriver"),
        );
        let resolved = driver.parse().unwrap().resolve_names().unwrap();
        assert!(
            !resolved.has_errors(),
            "no diagnostics: {:?}",
            resolved.phase.diagnostics
        );

        let _ = std::fs::remove_file(&importer_path);
        let _ = std::fs::remove_file(&exportee_path);
    }

    #[test]
    fn resolves_super_module_imports_and_qualified_paths() {
        let root = std::env::temp_dir().join(format!(
            "talk-super-module-path-test-{}",
            std::process::id()
        ));
        let feature = root.join("feature");
        std::fs::create_dir_all(&feature).unwrap();
        let consumer = feature.join("consumer.tlk");
        let sibling = feature.join("sibling.tlk");
        std::fs::write(&sibling, "public struct Token {}\n").unwrap();
        std::fs::write(
            &consumer,
            "use super::sibling::{ Token }\nToken()\nsuper::sibling::Token()\n",
        )
        .unwrap();

        let config = DriverConfig::new("TestDriver")
            .source_root(root.clone())
            .workspace_root(root.clone());
        let resolved = Driver::new(vec![Source::from(consumer)], config)
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap();
        assert!(
            !resolved.has_errors(),
            "no diagnostics: {:?}",
            resolved.phase.diagnostics
        );

        std::fs::remove_dir_all(root).unwrap();
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
            "use package::exportee::{ exported }\nexported\n",
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
