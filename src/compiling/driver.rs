use crate::{
    ast::{self, AST},
    compiling::module::{Module, ModuleEnvironment, ModuleId, ModuleTypes, StableModuleId},
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
    /// The checked typed program. Later compiler phases must go through this
    /// artifact rather than coordinating a public type side-table with a
    /// separate compiler-tree phase.
    pub program: crate::compiling::typed_program::TypedProgram,
    /// Flow-checked MIR built behind the MIR seam. Lowering consumes this
    /// checked artifact; callers never receive the structural MIR store.
    pub(crate) checked_mir: crate::lower::mir::CheckedMir,
    pub flow: crate::flow::FlowFacts,
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

    pub fn path(&self) -> Cow<'_, str> {
        match &self.kind {
            SourceKind::File(path) => path.to_string_lossy(),
            SourceKind::String(..) => Cow::Borrowed(":memory:"),
            SourceKind::InMemory { path, .. } => path.to_string_lossy(),
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
                && let Some(path) = qualified_relative_module_path(raw)
            {
                paths.push(ImportPath::Relative(path));
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
                && let Some(path) = qualified_relative_module_path(raw)
            {
                paths.push(ImportPath::Relative(path));
            }
        },
    );
    for root in &ast.roots {
        root.drive(&mut type_collector);
    }
    drop(type_collector);

    paths
}

fn qualified_relative_module_path(raw: &str) -> Option<String> {
    let (module_path, _) = raw.rsplit_once("::")?;
    if module_path.starts_with("./") || module_path.starts_with("../") {
        Some(module_path.to_string())
    } else {
        None
    }
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
            let mut resolved = parent.join(clean_rel);
            if resolved.extension().is_none() {
                resolved.set_extension("tlk");
            }

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
                            resolve_import_path(source_path.as_ref(), &import_path)
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

fn has_error_diagnostics(diagnostics: &[AnyDiagnostic]) -> bool {
    diagnostics.iter().any(|diag| match diag {
        AnyDiagnostic::Parsing(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::NameResolution(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::Types(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::Ownership(diagnostic) => diagnostic.severity == Severity::Error,
    })
}

fn error_diagnostic_files(diagnostics: &[AnyDiagnostic]) -> FxHashSet<FileID> {
    let mut files = FxHashSet::default();
    for diag in diagnostics {
        let (id, severity) = match diag {
            AnyDiagnostic::Parsing(diagnostic) => (diagnostic.id, &diagnostic.severity),
            AnyDiagnostic::NameResolution(diagnostic) => (diagnostic.id, &diagnostic.severity),
            AnyDiagnostic::Types(diagnostic) => (diagnostic.id, &diagnostic.severity),
            AnyDiagnostic::Ownership(diagnostic) => (diagnostic.id, &diagnostic.severity),
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
        let blocked_files = error_diagnostic_files(&diagnostics);
        let mut program = crate::compiling::typed_program::TypedProgram::from_checked_asts(
            asts,
            resolved_names,
            types,
            &blocked_files,
        );
        let (checked_mir, flow, flow_diagnostics) =
            crate::lower::mir::build_checked(&mut program, self.config.module_id);
        diagnostics.extend(flow_diagnostics);

        Driver {
            files: self.files,
            config: self.config,
            phase: Typed {
                program,
                checked_mir,
                flow,
                diagnostics,
            },
        }
    }
}

impl Driver<Typed> {
    /// Lower to λ_G (whole-program, with core and stdlib typed artifacts — see
    /// src/lower). Infallible; unsupported constructs surface as lowering
    /// diagnostics.
    pub fn lower(self) -> Driver<Lowered> {
        use crate::lower::{LowerUnit, lower_program};

        let Typed {
            program,
            checked_mir,
            flow: _,
            diagnostics,
        } = self.phase;

        let core = if self.config.module_id == ModuleId::Core {
            None
        } else {
            Some(crate::compiling::core::typed())
        };
        let stdlib = crate::compiling::stdlib::typed_modules(self.config.modules.as_ref());
        let mut units = vec![];
        if let Some(core) = core.as_ref() {
            units.push(LowerUnit {
                asts: core.program.files(),
                types: core.program.types(),
                resolved: core.program.resolved_names(),
                bodies: &core.checked_mir,
            });
        }
        for module in &stdlib {
            units.push(LowerUnit {
                asts: module.program.files(),
                types: module.program.types(),
                resolved: module.program.resolved_names(),
                bodies: &module.checked_mir,
            });
        }
        units.push(LowerUnit {
            asts: program.files(),
            types: program.types(),
            resolved: program.resolved_names(),
            bodies: &checked_mir,
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
    ///
    /// Only symbols this module minted (Current-tagged) are exported. The
    /// checker's scheme map also holds every imported module's schemes,
    /// and re-exporting those is corrupting: `Module::import_as` retags
    /// every key to the importer's id for this module, so a foreign
    /// symbol and an own symbol sharing a local id would collapse onto
    /// one key, with hash order deciding which scheme survives.
    pub fn module<T: Into<String>>(self, name: T) -> Module {
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
            id: StableModuleId::generate(&exports),
            name: name.into(),
            symbol_names,
            exports,
            types: ModuleTypes { schemes, catalog },
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

    /// Reference-evaluator run returning (value, captured stdout). On
    /// success, asserts the leak invariant: every allocation and `'heap`
    /// object torn down by exit. Leak detection is suite policy (CPython's
    /// refleak buildbots), not per-test opt-in.
    pub fn eval_with_output(
        &mut self,
    ) -> Result<(crate::lambda_g::eval::EvalValue, String), crate::lambda_g::eval::EvalError> {
        use crate::lambda_g::eval::EvalValue;
        let (value, out, live_objects, live_allocations) = self.eval_counted()?;
        // A program whose VALUE carries buffers legitimately holds them at
        // exit; exact balance is asserted for scalar-valued programs (the
        // vast majority — and where a leak can hide nowhere else).
        if matches!(
            value,
            EvalValue::I64(_) | EvalValue::F64(_) | EvalValue::Bool(_) | EvalValue::Void
        ) {
            assert_eq!(live_objects, 0, "{live_objects} 'heap objects leaked");
            assert_eq!(live_allocations, 0, "{live_allocations} allocations leaked");
        }
        Ok((value, out))
    }

    fn eval_counted(
        &mut self,
    ) -> Result<
        (crate::lambda_g::eval::EvalValue, String, usize, usize),
        crate::lambda_g::eval::EvalError,
    > {
        let mut evaluator = crate::lambda_g::eval::Evaluator::new();
        let value = evaluator.run_main(
            &mut self.phase.program,
            self.phase.main,
            self.phase.result_ty,
        )?;
        Ok((
            value,
            String::from_utf8_lossy(&evaluator.io.out).into_owned(),
            evaluator.live_objects(),
            evaluator.live_allocations(),
        ))
    }

    /// Schedule to bytecode and execute on the VM against host stdio.
    /// (`&mut`: scheduling computes free-variable caches for closure
    /// environments; the program's terms are untouched.)
    pub fn run_vm(&mut self) -> Result<crate::vm::interp::Value, String> {
        let module = self.schedule()?;
        let mut io = crate::vm::io::StdioIO;
        crate::vm::interp::run(&module, &mut io)
    }

    /// VM run returning (value, captured stdout) — tests and the REPL.
    pub fn run_vm_with_output(&mut self) -> Result<(crate::vm::interp::Value, String), String> {
        let module = self.schedule()?;
        let mut io = crate::vm::io::CaptureIO::default();
        let value = crate::vm::interp::run(&module, &mut io)?;
        Ok((value, String::from_utf8_lossy(&io.out).into_owned()))
    }

    /// VM run returning (value, captured stdout, Talk-style rendering of
    /// the value) — the REPL and the playground display the rendering.
    pub fn run_vm_displayed(
        &mut self,
        names: &crate::vm::interp::ValueNames,
    ) -> Result<(crate::vm::interp::Value, String, String), String> {
        let module = self.schedule()?;
        let mut io = crate::vm::io::CaptureIO::default();
        let (value, display) = crate::vm::interp::run_displayed(&module, &mut io, names)?;
        Ok((
            value,
            String::from_utf8_lossy(&io.out).into_owned(),
            display,
        ))
    }

    fn schedule(&mut self) -> Result<crate::vm::Module, String> {
        crate::vm::schedule::schedule(
            &mut self.phase.program,
            self.phase.main,
            &self.phase.entry_funcs,
        )
    }
}

/// Compile a source string through the whole pipeline and render its
/// λ_G program — the playground's show_ir.
pub fn render_lowered(name: &str, source: &str) -> Result<String, String> {
    render_lowered_from(
        name,
        Source::from(source),
        &crate::lambda_g::print::Styles::plain(),
    )
}

/// `render_lowered` over any Source (`talk lower <file>` reads from disk
/// or stdin); `styles` picks plain or ANSI-colored text.
pub fn render_lowered_from(
    name: &str,
    source: Source,
    styles: &crate::lambda_g::print::Styles,
) -> Result<String, String> {
    let mut lowered = lower_for_display(name, source)?;
    Ok(lowered.phase.program.render_styled(styles))
}

/// Compile and schedule, rendering the VM bytecode (`talk ir <file>`).
pub fn render_bytecode_from(
    name: &str,
    source: Source,
    styles: &crate::lambda_g::print::Styles,
) -> Result<String, String> {
    let mut lowered = lower_for_display(name, source)?;
    let module = lowered.schedule()?;
    let vm_styles = crate::vm::Styles {
        keyword: styles.keyword,
        func: styles.func,
        reset: styles.reset,
    };
    Ok(module.render_styled(&vm_styles))
}

/// Compile, schedule, and encode a VM module as Talk bytecode.
pub fn compile_bytecode_from(name: &str, source: Source) -> Result<Vec<u8>, String> {
    compile_bytecode_sources(name, vec![source])
}

/// Compile sources, schedule, and encode a VM module as Talk bytecode.
pub fn compile_bytecode_sources(name: &str, sources: Vec<Source>) -> Result<Vec<u8>, String> {
    let driver = Driver::new(sources, DriverConfig::new(name));
    let parsed = driver.parse().map_err(|err| format!("{err:?}"))?;
    let resolved = parsed.resolve_names().map_err(|err| format!("{err:?}"))?;
    let typed = resolved.type_check();
    if typed.has_errors() {
        return Err(typed
            .diagnostics()
            .iter()
            .map(|d| d.to_string())
            .collect::<Vec<_>>()
            .join("\n"));
    }
    let mut lowered = typed.lower();
    if !lowered.phase.diagnostics.is_empty() {
        return Err(format!(
            "not yet supported by the backend: {}",
            lowered.phase.diagnostics.join("; ")
        ));
    }
    let module = lowered.schedule()?;
    module.encode_bytecode().map_err(|err| err.to_string())
}

/// Compile and schedule, dumping the raw VM module (`talk bytecode <file>`).
pub fn render_raw_bytecode_from(name: &str, source: Source) -> Result<String, String> {
    let mut lowered = lower_for_display(name, source)?;
    let module = lowered.schedule()?;
    Ok(format!("{module:#?}"))
}

fn lower_for_display(name: &str, source: Source) -> Result<Driver<Lowered>, String> {
    let driver = Driver::new(vec![source], DriverConfig::new(name));
    let parsed = driver.parse().map_err(|err| format!("{err:?}"))?;
    let resolved = parsed.resolve_names().map_err(|err| format!("{err:?}"))?;
    let typed = resolved.type_check();
    if typed.has_errors() {
        return Err(typed
            .diagnostics()
            .iter()
            .map(|d| d.to_string())
            .collect::<Vec<_>>()
            .join("\n"));
    }
    let lowered = typed.lower();
    if !lowered.phase.diagnostics.is_empty() {
        return Err(format!(
            "not yet supported by the backend: {}",
            lowered.phase.diagnostics.join("; ")
        ));
    }
    Ok(lowered)
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
        // names no file, so it must not block typed-program/flow for the whole
        // workspace — only diagnostics attributed to a file block that file.
        use crate::diagnostic::{AnyDiagnostic, Diagnostic, Severity};
        use crate::node_id::{FileID, NodeID};
        use crate::types::error::TypeError;

        let mismatch = |id: NodeID| {
            AnyDiagnostic::Types(Diagnostic {
                id,
                severity: Severity::Error,
                kind: TypeError::Mismatch {
                    expected: "Int".into(),
                    found: "String".into(),
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
    fn render_lowered_shows_the_program_plainly() {
        let ir = render_lowered("IrTest", "func double(x: Int) -> Int { x * 2 }\ndouble(21)")
            .expect("ir");
        assert!(ir.contains("func main(k: fn"), "{ir}");
        assert!(ir.contains("func double(x: int, k: fn(int))"), "{ir}");
        assert!(ir.contains("var double.x"), "{ir}");
        assert!(
            !ir.contains('\u{21a6}') && !ir.contains('\u{22a5}'),
            "no notation: {ir}"
        );
    }

    #[test]
    fn render_lowered_names_types_and_specializations() {
        // Struct heads print by name, and a generic's specialization is
        // named by its concrete types, not a counter.
        let ir = render_lowered("IrTest", "func id(x) { x }\nprint(id(\"hi\"))").expect("ir");
        assert!(ir.contains("id<String>"), "{ir}");
        assert!(ir.contains("boxed(String)"), "{ir}");
        assert!(!ir.contains("Struct(C:"), "{ir}");
    }

    #[test]
    fn render_lowered_annotates_string_statics() {
        // A string literal's static pointer shows the bytes it points at.
        let ir = render_lowered("IrTest", "print(\"hi\")").expect("ir");
        assert!(
            ir.contains("record_new(ByteStorage, static+0) (\"hi\")"),
            "{ir}"
        );
    }

    #[test]
    fn render_lowered_reports_type_errors() {
        let result = render_lowered("IrTest", "let x: Int = \"nope\"\nx");
        assert!(result.is_err());
    }

    #[test]
    fn render_bytecode_lists_chunks() {
        let listing = render_bytecode_from(
            "IrTest",
            Source::from("func double(x: Int) -> Int { x * 2 }\ndouble(21)"),
            &crate::lambda_g::print::Styles::plain(),
        )
        .expect("bytecode");
        assert!(listing.contains("chunk 0: main"), "{listing}");
        assert!(listing.contains("ret r"), "{listing}");
    }

    #[test]
    fn render_raw_bytecode_dumps_module() {
        let dump = render_raw_bytecode_from(
            "BytecodeTest",
            Source::from("func double(x: Int) -> Int { x * 2 }\ndouble(21)"),
        )
        .expect("bytecode");
        assert!(dump.contains("Module {"), "{dump}");
        assert!(dump.contains("chunks:"), "{dump}");
        assert!(dump.contains("code:"), "{dump}");
        assert!(dump.contains("entry:"), "{dump}");
    }

    #[test]
    fn compile_bytecode_from_runs_decoded_module() {
        let bytes = compile_bytecode_from(
            "BytecodeTest",
            Source::from("func double(x: Int) -> Int { x * 2 }\ndouble(21)"),
        )
        .expect("bytecode");
        let module = crate::vm::Module::decode_bytecode(&bytes).expect("decode");
        let mut io = crate::vm::io::CaptureIO::default();
        let value = crate::vm::interp::run(&module, &mut io).expect("vm");
        assert_eq!(value, crate::vm::interp::Value::I64(42));
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

        let driver_b = Driver::new(
            vec![Source::from("use { Hello } from A\nHello(x: 123).x")],
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
                "use { Directory, File, DirectoryEntry } from fs\nlet dir: Directory\nlet file: File\nlet entry: DirectoryEntry\n",
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
    fn auto_discovers_qualified_relative_paths() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let importer_path = current_dir.join("dev/fixtures/qualified_importer.tlk");
        let exportee_path = current_dir.join("dev/fixtures/qualified_exportee.tlk");

        std::fs::write(&exportee_path, "public let exported = 42\n").unwrap();
        std::fs::write(&importer_path, "./qualified_exportee::exported\n").unwrap();

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
    fn auto_discovers_imports() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let importer_path = current_dir.join("dev/fixtures/importer.tlk");
        let exportee_path = current_dir.join("dev/fixtures/exportee.tlk");

        // Create the test files
        std::fs::write(&exportee_path, "public let exported = 42\n").unwrap();
        std::fs::write(
            &importer_path,
            "use { exported } from ./exportee.tlk\nexported\n",
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
