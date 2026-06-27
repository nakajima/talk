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
    ownership::OwnershipOutput,
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
    /// The program lowered to HIR (one entry per analyzed file). Built in
    /// `type_check`; consumed by lowering (and the ownership re-point).
    pub hir: IndexMap<Source, crate::hir::HirFile>,
    pub symbols: Symbols,
    pub resolved_names: ResolvedNames,
    pub types: TypeOutput,
    pub ownership: OwnershipOutput,
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
        AnyDiagnostic::Ownership(diagnostic) => diagnostic.severity == Severity::Error,
    })
}

fn error_diagnostic_files(diagnostics: &[AnyDiagnostic]) -> Option<FxHashSet<FileID>> {
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
        if id.0 == FileID::SYNTHESIZED {
            return None;
        }
        files.insert(id.0);
    }
    Some(files)
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
        // The HIR (once, NodeID-preserving) for the error-free asts that ownership analyzes
        // and lowering will consume. Stored in `Typed`; not yet consumed by ownership/lowering.
        let mut hir: IndexMap<Source, crate::hir::HirFile> = IndexMap::default();
        let build_hir_for = |hir: &mut IndexMap<Source, crate::hir::HirFile>,
                             source: &Source,
                             ast: &AST<crate::parsing::ast::NameResolved>| {
            hir.insert(source.clone(), crate::hir::build::build_file(ast));
        };

        let blocked_files = error_diagnostic_files(&diagnostics);
        let (ownership, ownership_diagnostics) = match blocked_files {
            None => (OwnershipOutput::default(), vec![]),
            Some(blocked_files) if blocked_files.is_empty() => {
                for (source, ast) in &asts {
                    build_hir_for(&mut hir, source, ast);
                }
                crate::ownership::check_ownership(
                    &hir,
                    &types,
                    &resolved_names,
                    self.config.module_id,
                )
            }
            Some(blocked_files) => {
                let clean_asts: IndexMap<Source, AST<crate::parsing::ast::NameResolved>> = asts
                    .iter()
                    .filter(|(_, ast)| !blocked_files.contains(&ast.file_id))
                    .map(|(source, ast)| (source.clone(), ast.clone()))
                    .collect();
                for (source, ast) in &clean_asts {
                    build_hir_for(&mut hir, source, ast);
                }
                if clean_asts.is_empty() {
                    (OwnershipOutput::default(), vec![])
                } else {
                    crate::ownership::check_ownership(
                        &hir,
                        &types,
                        &resolved_names,
                        self.config.module_id,
                    )
                }
            }
        };
        diagnostics.extend(ownership_diagnostics);

        Driver {
            files: self.files,
            config: self.config,
            phase: Typed {
                asts,
                hir,
                symbols,
                resolved_names,
                types,
                ownership,
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
            asts: _,
            hir,
            symbols: _,
            resolved_names,
            types,
            ownership,
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
                asts: &core.hir,
                types: &core.types,
                resolved: &core.resolved_names,
                ownership: &core.ownership,
            });
        }
        units.push(LowerUnit {
            asts: &hir,
            types: &types,
            resolved: &resolved_names,
            ownership: &ownership,
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
        Ok((
            value,
            String::from_utf8_lossy(&evaluator.io.out).into_owned(),
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
