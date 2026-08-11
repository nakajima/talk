use crate::{
    ast::{self, AST},
    compiling::{
        module::{Module, ModuleEnvironment, ModuleId, ModuleTypes, StableModuleId},
        module_path::LocalModulePaths,
    },
    diagnostic::{AnyDiagnostic, Severity},
    name::Name,
    name_resolution::{
        name_resolver::{NameResolver, ResolvedNames},
        symbol::{Symbol, Symbols},
    },
    node::Node,
    node_id::FileID,
    node_kinds::{
        decl::{DeclKind, ImportPath},
        expr::ExprKind,
        type_annotation::TypeAnnotationKind,
    },
    parser_error::ParserError,
};
use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use std::borrow::Cow;
use std::collections::VecDeque;
use std::sync::Arc;
use std::{hash::Hash, hash::Hasher};
use std::{
    io,
    path::{Path, PathBuf},
    rc::Rc,
};

pub trait DriverPhase {}

/// An ownership rejection: the message and, when the rejection carries a
/// real span, the file it belongs to with its byte range. The file id
/// indexes the compile's document list directly — a path string would
/// force every consumer to re-derive the mapping it already has.
pub type OwnershipRejection = (String, Option<(FileID, u32, u32)>);

pub struct Initial {}
impl DriverPhase for Initial {}

impl DriverPhase for Parsed {}
pub struct Parsed {
    pub asts: IndexMap<Source, AST<ast::Parsed>>,
    pub source_texts: std::collections::HashMap<FileID, Arc<str>>,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub procedural_macros: crate::procedural_macros::ProceduralMacroEnvironment,
    /// Canonical local import edges (importer, imported) recorded
    /// during parse discovery (CLEAN-03): explicit `use` decls and
    /// qualified local references alike, keyed by FileID rather than
    /// reconstructed from paths or file stems later.
    pub file_dependencies: Vec<(FileID, FileID)>,
}

/// Exported names, each carrying its full overload set (ADR 0041):
/// public declarations with one base but different full callable names
/// must not overwrite one another in the export table.
pub type Exports = IndexMap<String, Vec<Symbol>>;

impl DriverPhase for NameResolved {}
pub struct NameResolved {
    pub asts: IndexMap<Source, AST<crate::parsing::ast::NameResolved>>,
    pub symbols: Symbols,
    pub resolved_names: ResolvedNames,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub procedural_macros: Option<crate::procedural_macros::ProceduralMacroArtifact>,
    pub file_dependencies: Vec<(FileID, FileID)>,
}

impl DriverPhase for Typed {}
pub struct Typed {
    /// The final frontend artifact: a checked typed program and its semantic
    /// facts. The frontend performs no ownership analysis or code generation.
    pub program: crate::compiling::typed_program::TypedProgram,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub procedural_macros: Option<crate::procedural_macros::ProceduralMacroArtifact>,
}

#[derive(Debug)]
pub enum CompileError {
    IO(io::Error),
    Parsing(ParserError),
    Macro(String),
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

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum ParseMode {
    #[default]
    Strict,
    Lenient,
}

/// The compilation's one fact table (ADR 0053): every module's typecheck
/// reads and writes this catalog; imported modules' slices are seeded
/// exactly once, in import order. Shared across the drivers of one
/// compilation (package graphs, workspaces) via `DriverConfig::catalog`.
#[derive(Default)]
pub struct SharedCatalog {
    pub types: crate::types::catalog::TypeCatalog,
    seeded: rustc_hash::FxHashSet<crate::compiling::module::StableModuleId>,
}

impl SharedCatalog {
    /// Insert a module's fact slice unless this table has already seen
    /// it. Slices are own-filtered at export, so inserts are disjoint.
    pub fn seed(&mut self, module: &crate::compiling::module::Module) {
        if self.seeded.insert(module.id) {
            self.types.insert_slice(&module.types.catalog);
        }
    }
}

#[derive(Clone)]
pub struct DriverConfig {
    pub module_id: ModuleId,
    pub modules: Rc<ModuleEnvironment>,
    /// ADR 0053: the shared fact table this compilation accumulates into.
    pub catalog: Rc<std::cell::RefCell<SharedCatalog>>,
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
    /// Local imports resolving to these canonical source paths bind
    /// against the named precompiled module's exports instead of
    /// re-compiling the file (ADR 0056): a package's root library rides
    /// into its own binary and test compiles as a finished module, so
    /// its closure is never re-parsed by the importing compile.
    pub precompiled_sources: FxHashMap<PathBuf, String>,
    /// An explicit parser session for the strict path: bootstrap stage 2
    /// parses with the stage-1 candidate (ADR 0043 §3). `None` is the
    /// shared embedded artifact.
    pub parser: Option<std::sync::Arc<crate::compiling::frontend::ParserSession>>,
    /// Per-file parse results reused across compilations (the LSP's
    /// analysis worker rebuilds its workspace on every edit burst, but
    /// unchanged files parse to identical output). `None` compiles cold.
    /// Only consulted when `parser` is `None`: a candidate session's
    /// output is not stable across the bootstrap fixed point.
    pub parse_cache: Option<Rc<std::cell::RefCell<ParseCache>>>,
}

/// A per-file parse cache. A file's parse output is a pure function of
/// (file id, path, parse mode, source text): unchanged files across
/// workspace rebuilds skip the frontend entirely, which is the bulk of
/// an LSP rebuild's cost. Entries replace in place — one per file
/// slot, never accumulating stale texts' ASTs.
#[derive(Default)]
pub struct ParseCache {
    entries: rustc_hash::FxHashMap<ParseCacheKey, ParseCacheEntry>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ParseCacheKey {
    file_id: FileID,
    path: String,
    mode: ParseMode,
}

struct ParseCacheEntry {
    text_hash: u64,
    ast: AST<ast::Parsed>,
    diagnostics: Vec<AnyDiagnostic>,
}

impl ParseCache {
    fn text_hash(text: &str) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = rustc_hash::FxHasher::default();
        text.as_bytes().hash(&mut hasher);
        text.len().hash(&mut hasher);
        hasher.finish()
    }

    /// A cached parse AST by identity, validated against the current
    /// text: semantic-token collection reuses the workspace build's
    /// parse instead of re-parsing the document.
    pub fn get_ast(
        &self,
        file_id: FileID,
        path: &str,
        mode: ParseMode,
        text: &str,
    ) -> Option<AST<ast::Parsed>> {
        self.get(
            &ParseCacheKey {
                file_id,
                path: path.to_string(),
                mode,
            },
            text,
        )
        .map(|(ast, _)| ast)
    }

    /// The cached parse for this exact text, cloned out (the driver's
    /// AST map takes ownership).
    fn get(
        &self,
        key: &ParseCacheKey,
        text: &str,
    ) -> Option<(AST<ast::Parsed>, Vec<AnyDiagnostic>)> {
        let entry = self.entries.get(key)?;
        if entry.text_hash != Self::text_hash(text) {
            return None;
        }
        Some((entry.ast.clone(), entry.diagnostics.clone()))
    }

    fn insert(
        &mut self,
        key: ParseCacheKey,
        text: &str,
        ast: &AST<ast::Parsed>,
        diagnostics: &[AnyDiagnostic],
    ) {
        self.entries.insert(
            key,
            ParseCacheEntry {
                text_hash: Self::text_hash(text),
                ast: ast.clone(),
                diagnostics: diagnostics.to_vec(),
            },
        );
    }
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
            // Absolute identity at mint (ADR 0038): the program under
            // compilation stamps its symbols `Main` unless the config
            // assigns a real module id (libraries, stdlib, core).
            module_id: crate::compiling::module::ModuleId::Main,
            modules: Default::default(),
            catalog: Default::default(),
            mode: CompilationMode::default(),
            module_name: module_name.into(),
            parse_mode: ParseMode::default(),
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
            precompiled_sources: FxHashMap::default(),
            parser: None,
            parse_cache: None,
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

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum SourceKind {
    File(PathBuf),
    // Just a string
    String(Arc<str>),
    // Used for core, since they're not necessarily going to be on the fs
    InMemory { path: PathBuf, text: Arc<str> },
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
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
            kind: SourceKind::String(Arc::from(value)),
        }
    }
}

impl Source {
    pub fn in_memory(path: PathBuf, text: impl Into<Arc<str>>) -> Self {
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

    pub fn read(&self) -> Result<Arc<str>, CompileError> {
        match &self.kind {
            SourceKind::File(path) => std::fs::read_to_string(path).map(Arc::from).map_err(|e| {
                CompileError::IO(std::io::Error::new(
                    e.kind(),
                    format!("{}: {e}", path.display()),
                ))
            }),
            SourceKind::String(string) => Ok(string.clone()),
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
#[cfg(test)]
mod frontend_parse_tests {
    use super::*;

    /// The Stage 4 driver seam: one source parsed through the
    /// frontend artifact assembles into the compiler's parse AST with
    /// per-file identity and continued id minting. (Byte equivalence
    /// with the retired Rust parser was proven by the migration
    /// harness; the goldens pin the format.)
    #[test]
    fn frontend_parse_matches() {
        let source = "struct Pair {\n\tlet a: Int\n}\n\nfunc make() -> Pair {\n\tPair(a: 4)\n}\n";
        let file_id = FileID(3);
        let (ast, diagnostics) =
            crate::compiling::frontend::parse_ast(source, file_id, "seam.tlk").expect("parses");
        assert!(diagnostics.is_empty());
        assert_eq!(ast.roots.len(), 2);
        assert_eq!(ast.file_id, file_id);
        assert!(ast.node_ids.last > 0);
        let crate::node::Node::Decl(first) = &ast.roots[0] else {
            panic!("expected a decl root");
        };
        assert_eq!(first.span.start, 0);
        assert_eq!(first.span.file_id, file_id);
        assert!(ast.meta.get(&first.id).is_some());
    }
}

/// An import edge discovered while parsing: either one module file or a
/// glob (`use package::foo::*`) covering the module file plus every
/// `.tlk` under its directory.
enum DiscoveredImport {
    Single(ImportPath),
    /// Local module path of a glob import. A glob over a compiled package
    /// module has no source tree and stays `Single`.
    Glob(String),
}

fn extract_import_paths(ast: &AST<ast::Parsed>) -> Vec<DiscoveredImport> {
    use derive_visitor::Drive;

    let mut paths = Vec::new();
    for root in &ast.roots {
        if let Node::Decl(decl) = root
            && let DeclKind::Import(import) = &decl.kind
        {
            match (&import.symbols, &import.path) {
                (crate::node_kinds::decl::ImportedSymbols::Glob, ImportPath::Local(path)) => {
                    paths.push(DiscoveredImport::Glob(path.clone()));
                }
                _ => paths.push(DiscoveredImport::Single(import.path.clone())),
            }
        }
    }

    let mut expr_collector =
        derive_visitor::visitor_enter_fn(|expr: &crate::node_kinds::expr::Expr| {
            if let ExprKind::Variable(Name::Raw(raw)) = &expr.kind
                && let Some(path) = qualified_local_module_path(raw)
            {
                paths.push(DiscoveredImport::Single(ImportPath::Local(path)));
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
                paths.push(DiscoveredImport::Single(ImportPath::Local(path)));
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

    let Some(canonical) = canonicalize_import(source_path, module_path, &resolved, workspace_root)?
    else {
        return Ok(None);
    };

    // Return both the canonical path (for tracking) and the resolved path for source.
    Ok(Some((canonical, resolved)))
}

/// Canonicalizes a discovered source path for the import graph
/// (normalizes symlinks) and checks workspace confinement. Returns None
/// when the path does not exist on disk; in-memory sources are matched
/// separately.
fn canonicalize_import(
    source_path: &str,
    import_path: &str,
    resolved: &Path,
    workspace_root: Option<&Path>,
) -> Result<Option<PathBuf>, CompileError> {
    let Ok(canonical) = resolved.canonicalize() else {
        return Ok(None);
    };
    if let Some(root) = workspace_root {
        let canonical_root = root.canonicalize().map_err(CompileError::IO)?;
        if !canonical.starts_with(&canonical_root) {
            return Err(CompileError::ImportOutsideWorkspace {
                source: source_path.to_string(),
                import_path: import_path.to_string(),
                workspace_root: root.to_path_buf(),
            });
        }
    }
    Ok(Some(canonical))
}

/// Enters a discovered source into the parse queue (unless already
/// tracked) and records the importer's edge to it.
fn queue_discovered(
    canonical: PathBuf,
    resolved: PathBuf,
    importer_id: FileID,
    file_ids: &mut FxHashMap<PathBuf, FileID>,
    next_file_id: &mut u32,
    to_parse: &mut VecDeque<(Source, FileID)>,
    file_dependencies: &mut Vec<(FileID, FileID)>,
) {
    let target_id = match file_ids.get(&canonical) {
        Some(target_id) => *target_id,
        None => {
            let target_id = FileID(*next_file_id);
            *next_file_id += 1;
            file_ids.insert(canonical, target_id);
            to_parse.push_back((Source::from(resolved), target_id));
            target_id
        }
    };
    record_edge(importer_id, target_id, file_dependencies);
}

fn record_edge(
    importer_id: FileID,
    target_id: FileID,
    file_dependencies: &mut Vec<(FileID, FileID)>,
) {
    if target_id != importer_id && !file_dependencies.contains(&(importer_id, target_id)) {
        file_dependencies.push((importer_id, target_id));
    }
}

impl Driver {
    pub fn new(files: Vec<Source>, mut config: DriverConfig) -> Self {
        {
            let modules = Rc::make_mut(&mut config.modules);
            modules.import_core(super::core::compile());
            // Stdlib modules register on demand: `use` discovery during
            // parsing activates exactly the modules a program names.
        }

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

    pub fn parse(mut self) -> Result<Driver<Parsed>, CompileError> {
        crate::profile::init();
        profiling::scope!("compiler.parse");
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
        let mut source_texts = std::collections::HashMap::new();
        let mut diagnostics = vec![];

        // Canonical import graph (CLEAN-03): file ids are pre-assigned
        // as a source enters the queue, so an import edge can name its
        // target before the target is parsed. The map doubles as the
        // cycle guard the old processed-paths set provided.
        let mut file_ids: FxHashMap<PathBuf, FileID> = FxHashMap::default();
        let mut file_dependencies: Vec<(FileID, FileID)> = Vec::new();

        // Queue of files to parse, FIFO, with their pre-assigned ids.
        let mut next_file_id = 0u32;
        let mut to_parse: VecDeque<(Source, FileID)> = VecDeque::new();
        // In-memory sources never exist on disk, so they never
        // canonicalize; their edges match the resolved path directly.
        let mut in_memory_ids: FxHashMap<PathBuf, FileID> = FxHashMap::default();
        for file in &self.files {
            let file_id = FileID(next_file_id);
            next_file_id += 1;
            // For in-memory sources, try to canonicalize if the file
            // exists on disk; string sources have no path to track.
            if let SourceKind::InMemory { path, .. } = &file.kind {
                in_memory_ids.insert(path.clone(), file_id);
            }
            if let Some(path) = file.source_path()
                && let Ok(canonical) = path.canonicalize()
            {
                file_ids.insert(canonical, file_id);
            }
            to_parse.push_back((file.clone(), file_id));
        }

        while let Some((file, file_id)) = to_parse.pop_front() {
            profiling::scope!("compiler.parse_file");
            let input = file.read()?;
            tracing::info!("parsing {file:?}");
            source_texts.insert(file_id, input.clone());
            let parse = |driver: &Self| match driver.config.parse_mode {
                // The strict compile path parses through the frontend
                // artifact (ADR 0043 Stage 4): the checked-in bytecode
                // is the parser; there is no fallback. The lenient
                // editor path migrates with the LSP consumer.
                // The strict compile path parses through the frontend
                // artifact (ADR 0043 Stage 4): the checked-in bytecode
                // is the parser; there is no fallback. Core's compile
                // products come from the disk cache, so the interpreted
                // parse cost is paid once per compiler build.
                ParseMode::Strict => crate::compiling::frontend::parse_ast_in(
                    driver.config.parser.as_deref(),
                    &input,
                    file_id,
                    file.path().as_ref(),
                ),
                // The lenient contract (ADR 0043): a hard failure
                // degrades to an empty AST plus the failure as a
                // diagnostic.
                ParseMode::Lenient => Ok(crate::compiling::frontend::parse_ast_lenient(
                    &input,
                    file_id,
                    file.path().as_ref(),
                )),
            };
            // Unchanged files skip the frontend: the cache key pins the
            // file's identity in this compile (id, path, mode), the
            // entry validates the text itself. Candidate parser
            // sessions bypass the cache (their output is not stable).
            let parse_cache = self
                .config
                .parse_cache
                .clone()
                .filter(|_| self.config.parser.is_none());
            let result = match parse_cache {
                Some(cache) => {
                    let key = ParseCacheKey {
                        file_id,
                        path: file.path().into_owned(),
                        mode: self.config.parse_mode,
                    };
                    if let Some(hit) = cache.borrow().get(&key, &input) {
                        Ok(hit)
                    } else {
                        let result = parse(&self);
                        if let Ok((ast, ast_diagnostics)) = &result {
                            cache.borrow_mut().insert(key, &input, ast, ast_diagnostics);
                        }
                        result
                    }
                }
                None => parse(&self),
            };
            match result {
                Ok((mut parsed, ast_diagnostics)) => {
                    parsed.skip_core_prelude = input.starts_with("// no-core");
                    diagnostics.extend(ast_diagnostics);

                    // Discover imports and queue them for parsing,
                    // recording the canonical edge either way.
                    let source_path = file.path();
                    for discovered in extract_import_paths(&parsed) {
                        let import_path = match discovered {
                            DiscoveredImport::Single(import_path) => import_path,
                            // Glob import: the module file plus every
                            // .tlk under its directory, one edge each.
                            DiscoveredImport::Glob(module_path) => {
                                let Some(base) =
                                    local_modules.resolve_base(source_path.as_ref(), &module_path)
                                else {
                                    continue;
                                };
                                let members = LocalModulePaths::expand_glob(&base);
                                // Every glob member rides precompiled
                                // (ADR 0056): the resolver binds the
                                // glob against the module's exports
                                // instead of re-parsing the files.
                                if !members.is_empty()
                                    && members.iter().all(|path| {
                                        path.canonicalize().ok().is_some_and(|canonical| {
                                            self.config.precompiled_sources.contains_key(&canonical)
                                        })
                                    })
                                {
                                    continue;
                                }
                                for resolved in members {
                                    let Some(canonical) = canonicalize_import(
                                        source_path.as_ref(),
                                        &module_path,
                                        &resolved,
                                        self.config.workspace_root.as_deref(),
                                    )?
                                    else {
                                        continue;
                                    };
                                    queue_discovered(
                                        canonical,
                                        resolved,
                                        file_id,
                                        &mut file_ids,
                                        &mut next_file_id,
                                        &mut to_parse,
                                        &mut file_dependencies,
                                    );
                                }
                                // In-memory sources never canonicalize; match
                                // them against the glob base by path.
                                for (path, target_id) in &in_memory_ids {
                                    if LocalModulePaths::glob_member(&base, path) {
                                        record_edge(file_id, *target_id, &mut file_dependencies);
                                    }
                                }
                                continue;
                            }
                        };
                        if let ImportPath::Package(package) = &import_path {
                            if self.config.modules.get_module_by_name(package).is_none()
                                && let Some((id, module)) =
                                    super::stdlib::try_module_with_id(package)
                            {
                                Rc::make_mut(&mut self.config.modules)
                                    .import_shared(module.clone(), id)
                                    .expect("stdlib module registers once per session");
                            }
                            continue;
                        }
                        if let Some((canonical, resolved)) = resolve_import_path(
                            source_path.as_ref(),
                            &import_path,
                            &local_modules,
                            self.config.workspace_root.as_deref(),
                        )? {
                            // The target rides precompiled (ADR 0056):
                            // the resolver binds the import against the
                            // module's exports; the file never enters
                            // this compile.
                            if self.config.precompiled_sources.contains_key(&canonical) {
                                continue;
                            }
                            queue_discovered(
                                canonical,
                                resolved,
                                file_id,
                                &mut file_ids,
                                &mut next_file_id,
                                &mut to_parse,
                                &mut file_dependencies,
                            );
                        } else if let ImportPath::Local(module_path) = &import_path {
                            // The target never canonicalized: match it
                            // against the session's in-memory sources.
                            if let Some(resolved) =
                                local_modules.resolve(source_path.as_ref(), module_path)
                                && let Some(target_id) = in_memory_ids.get(&resolved).copied()
                            {
                                record_edge(file_id, target_id, &mut file_dependencies);
                            }
                        }
                    }

                    asts.insert(file.clone(), parsed);
                }
                Err(err) => {
                    return Err(CompileError::Parsing(err));
                }
            }
        }

        // Imports discovered while parsing may have activated stdlib
        // modules that carry procedural macros (html): load the macro
        // environment only now, from the final module set.
        let procedural_macros = if self.config.module_name != "PackageMacros" {
            let local = self
                .config
                .workspace_root
                .as_deref()
                .map(crate::procedural_macros::ProceduralMacroService::discover)
                .transpose()
                .map_err(CompileError::Macro)?
                .flatten();
            crate::procedural_macros::ProceduralMacroEnvironment::load(local, &self.config.modules)
                .map_err(CompileError::Macro)?
        } else {
            Default::default()
        };

        Ok(Driver {
            files: self.files,
            config: self.config,
            phase: Parsed {
                asts,
                source_texts,
                diagnostics,
                procedural_macros,
                file_dependencies,
            },
        })
    }
}

impl Driver<Parsed> {
    pub fn resolve_names(mut self) -> Result<Driver<NameResolved>, CompileError> {
        crate::profile::init();
        profiling::scope!("compiler.resolve_names");
        let mut resolver = NameResolver::with_source_root(
            self.config.modules.clone(),
            self.config.module_id,
            self.config.source_root.clone().unwrap_or_default(),
        )
        .with_precompiled_sources(self.config.precompiled_sources.clone());

        let procedural_macros = self.phase.procedural_macros.local_artifact();
        let file_dependencies = self.phase.file_dependencies;
        let (paths, mut asts): (Vec<_>, Vec<_>) = self.phase.asts.into_iter().unzip();
        self.phase.diagnostics.extend(
            crate::macro_expansion::expand_macros_with_sources_and_service(
                &mut asts,
                &self.phase.source_texts,
                Some(&self.phase.procedural_macros),
            ),
        );
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
                procedural_macros,
                file_dependencies,
            },
        })
    }
}

/// The compiled program handed between `compile_executable` and
/// execution, re-exported from the bytecode adapter (ADR 0047).
pub use talk_bytecode::Executable;

pub use crate::compiling::mir::{OptimizationPassStats, OptimizationStats};

/// How the published MIR module is entered (ADR 0047): a script's
/// top-level statements, a named zero-parameter public function, or a
/// service's named exports with its capability list.
pub enum MirEntry<'a> {
    Script,
    Named(&'a str),
    Exports {
        names: &'a [String],
        allowed_effects: &'a [String],
    },
}

/// The finalized public MIR module plus the compiler's own optimization
/// statistics. Bytecode-adapter and VM statistics stay with their
/// owners; this is the compiler's share.
pub struct MirOutput {
    pub module: talk_mir::Module,
    pub optimizations: OptimizationStats,
}

fn has_error_diagnostics(diagnostics: &[AnyDiagnostic]) -> bool {
    diagnostics.iter().any(|diag| match diag {
        AnyDiagnostic::Parsing(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::Macro(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::NameResolution(diagnostic) => diagnostic.severity == Severity::Error,
        AnyDiagnostic::Types(diagnostic) => diagnostic.severity == Severity::Error,
    })
}

fn error_diagnostic_files(diagnostics: &[AnyDiagnostic]) -> FxHashSet<FileID> {
    let mut files = FxHashSet::default();
    for diag in diagnostics {
        let (id, severity) = match diag {
            AnyDiagnostic::Parsing(diagnostic) => (diagnostic.id, &diagnostic.severity),
            AnyDiagnostic::Macro(diagnostic) => (diagnostic.id, &diagnostic.severity),
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
            id: StableModuleId::generate(&name, &exports, &Default::default(), &[]),
            name,
            symbol_names: self.phase.resolved_names.symbol_names,
            exports,
            types: ModuleTypes::default(),
            procedural_macros: None,
            dependencies: module_dependencies(&self.config.modules),
        }
        .with_procedural_macros(self.phase.procedural_macros)
    }

    /// Type check: generate constraints and solve them per SCC binding group
    /// (see src/types). Infallible — failures surface as diagnostics.
    pub fn type_check(self) -> Driver<Typed> {
        crate::profile::init();
        profiling::scope!("compiler.type_check");
        let NameResolved {
            asts,
            mut symbols,
            resolved_names,
            mut diagnostics,
            procedural_macros,
            file_dependencies,
        } = self.phase;

        let (types, type_diagnostics) = crate::types::generate::check_types(
            &asts,
            &mut symbols,
            &resolved_names,
            &self.config.modules,
            self.config.module_id,
            &mut self.config.catalog.borrow_mut(),
        );
        diagnostics.extend(type_diagnostics);
        let blocked_files = error_diagnostic_files(&diagnostics);
        let program = crate::compiling::typed_program::TypedProgram::from_checked_asts(
            asts,
            resolved_names,
            types,
            &blocked_files,
            file_dependencies,
        );

        Driver {
            files: self.files,
            config: self.config,
            phase: Typed {
                program,
                diagnostics,
                procedural_macros,
            },
        }
    }
}

impl Driver<Typed> {
    /// The one target compilation interface (ADR 0047): publish the
    /// finalized, target-independent MIR module. C, bytecode, and LLVM
    /// adapters consume exactly this output.
    pub fn compile_mir(&self, entry: MirEntry<'_>) -> Result<MirOutput, String> {
        let entry = match entry {
            MirEntry::Script => crate::compiling::mir::Entry::Script,
            MirEntry::Named(name) => crate::compiling::mir::Entry::Named(name),
            MirEntry::Exports {
                names,
                allowed_effects,
            } => crate::compiling::mir::Entry::Exports {
                names,
                allowed_effects,
            },
        };
        self.with_backend_inputs(entry, |programs, entry| {
            crate::compiling::mir::compile_mir(programs, entry)
        })
        .map(|(module, optimizations)| MirOutput {
            module,
            optimizations,
        })
        .map_err(|error| self.locate_backend_error(&error))
    }

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
        let entry = match entry {
            Some(name) => MirEntry::Named(name),
            None => MirEntry::Script,
        };
        let output = self.compile_mir(entry)?;
        talk_bytecode::compile(&output.module).map_err(|error| error.message().to_string())
    }

    /// Compile a service module (ADR 0043 call ABI): each named public
    /// function becomes a host-callable export in the module's export
    /// table, dispatched by `Executable::run_export`. `allowed_effects`
    /// is the service's capability list — compilation rejects an export
    /// whose effect row reaches outside it.
    pub fn compile_service(
        &self,
        exports: &[String],
        allowed_effects: &[String],
    ) -> Result<Executable, String> {
        crate::profile::init();
        profiling::scope!("compiler.compile_service");
        let output = self.compile_mir(MirEntry::Exports {
            names: exports,
            allowed_effects,
        })?;
        talk_bytecode::compile(&output.module).map_err(|error| error.message().to_string())
    }

    /// Run the ownership analysis without lowering (`talk check`). A
    /// rejection comes back with its message and, when the span maps to
    /// a source document, that document's path and byte range.
    pub fn check_ownership(&self) -> Result<(), OwnershipRejection> {
        self.with_backend_inputs(crate::compiling::mir::Entry::Script, |programs, entry| {
            crate::compiling::mir::check(programs, entry)
        })
        .map_err(|error| {
            let span = error.span;
            if span == crate::parsing::span::Span::SYNTHESIZED {
                return (error.message.clone(), None);
            }
            (error.message, Some((span.file_id, span.start, span.end)))
        })
    }

    /// Render the backend's middle representation for inspection
    /// (TOOL-10). Same inputs as `compile_executable`. `debug`
    /// annotates the dump with source provenance; it survives
    /// optimization, so the flags combine freely.
    pub fn render_mir(
        &self,
        entry: Option<&str>,
        optimized: bool,
        debug: bool,
    ) -> Result<String, String> {
        let entry = match entry {
            Some(name) => crate::compiling::mir::Entry::Named(name),
            None => crate::compiling::mir::Entry::Script,
        };
        self.with_backend_inputs(entry, |programs, entry| {
            crate::compiling::mir::render_mir(programs, entry, optimized, debug)
        })
        .map_err(|error| self.locate_backend_error(&error))
    }

    /// Assemble the reachable source graph (this program, core, imported
    /// stdlib modules, dependency libraries) and the module-alias map, and
    /// hand them to the backend.
    fn with_backend_inputs<R>(
        &self,
        entry: crate::compiling::mir::Entry<'_>,
        run: impl FnOnce(
            &[crate::compiling::mir::ProgramInput<'_>],
            crate::compiling::mir::Entry<'_>,
        ) -> R,
    ) -> R {
        let core = crate::compiling::core::typed_program();
        // Bare services, including the service used to compile stdlib-owned
        // macros, carry no stdlib modules. Avoid initializing the global
        // stdlib just to produce an empty backend input set; doing so while a
        // stdlib module is itself compiling would recursively enter its
        // OnceLock.
        let mut stdlib_names: Vec<&'static str> = crate::compiling::stdlib::stdlib_sources()
            .iter()
            .filter(|(name, _)| self.config.modules.get_module_id_by_name(name).is_some())
            .map(|(name, _)| *name)
            .collect();
        // Library modules (package dependencies, a cached root library)
        // record every module they were compiled against (CLEAN-03):
        // their stdlib edges name bodies the program under compilation
        // may never import itself, so seed the body set from every
        // registered module's edges, not just the program's own.
        let registered_edges: Vec<ModuleId> = self
            .config
            .modules
            .iter_modules()
            .flat_map(|(_, module)| module.dependencies.iter().copied())
            .collect();
        for edge in registered_edges {
            if let Some(name) = crate::compiling::stdlib::name_for_module_id(edge)
                && !stdlib_names.contains(&name)
            {
                stdlib_names.push(name);
            }
        }
        // Stdlib modules' bodies may call into the modules they `use`
        // (testing calls into ansi): close the body set over the edges
        // each compiled stdlib module recorded when it was built, even
        // when the program never names them itself. Modules nobody
        // registered are materialized through the stdlib cache so their
        // own edges still count (full transitivity).
        let mut index = 0;
        while index < stdlib_names.len() {
            let name = stdlib_names[index];
            let dependencies: Vec<ModuleId> = match self.config.modules.get_module_by_name(name) {
                Some(module) => module.dependencies.clone(),
                None => crate::compiling::stdlib::module_with_id(name)
                    .map(|(_, module)| module.dependencies.clone())
                    .unwrap_or_default(),
            };
            for dependency in dependencies {
                if let Some(dependency) = crate::compiling::stdlib::name_for_module_id(dependency)
                    && !stdlib_names.contains(&dependency)
                {
                    stdlib_names.push(dependency);
                }
            }
            index += 1;
        }
        let stdlib = stdlib_names
            .iter()
            .filter_map(|name| {
                crate::compiling::stdlib::typed_program(name).map(|program| (*name, program))
            })
            .collect::<Vec<_>>();
        // Absolute identity at mint (ADR 0038): every program's symbols
        // already carry their real module stamp.
        let user_module = self.config.module_id;
        let mut programs = vec![
            crate::compiling::mir::ProgramInput {
                program: &self.phase.program,
                module: user_module,
            },
            crate::compiling::mir::ProgramInput {
                program: &core,
                module: crate::compiling::module::ModuleId::Core,
            },
        ];
        for (name, program) in &stdlib {
            // The session module table only names the modules the
            // program imported itself; the dependency closure above can
            // add modules nobody named (fs's bodies call into os). Their
            // ids are fixed either way (WellKnown), so mint them
            // directly rather than consulting the session table.
            if let Some(module) = crate::compiling::stdlib::module_id_for_name(name) {
                programs.push(crate::compiling::mir::ProgramInput { program, module });
            }
        }
        for (module, program) in &self.config.libraries {
            programs.push(crate::compiling::mir::ProgramInput {
                program,
                module: *module,
            });
        }
        run(&programs, entry)
    }

    /// Render a backend rejection with its source location when the span
    /// points into one of this driver's files.
    fn locate_backend_error(&self, error: &crate::compiling::mir::BackendError) -> String {
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
    /// Only symbols this module minted are exported (ADR 0053: a slice
    /// is the module's own facts; imported facts already live in their
    /// declarers' slices, and shipping copies would reintroduce the
    /// multi-copy divergence this architecture removed).
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
        // Ship the module's fact slice (ADR 0053): its own facts, whole,
        // plus its amendments to foreign entities. Privacy is enforced at
        // use sites (ADR 0042), never by withholding facts.
        // Scheme-level sanitize inside: a leftover
        // row/effect tail variable becomes an owner-keyed param AND
        // registers in eff_params/row_params, so instantiation freshens
        // it on the importing side (a rigid tail would reject every
        // ambient row it meets — the http.run regression).
        #[cfg_attr(not(debug_assertions), allow(unused_mut))]
        let mut interface =
            crate::compiling::interface::module_slice(&resolved_names, types, own, compiled_as);
        // A module's types outlive this store: nothing var-shaped may
        // cross. Finalization guarantees it through the same walk this
        // assertion re-runs; a future catalog field that skips the walk
        // fails loudly here in debug builds.
        #[cfg(debug_assertions)]
        interface.types.catalog.debug_assert_portable();
        Module {
            id: StableModuleId::generate(
                &name,
                &exports,
                &interface.types.catalog.callable_contracts,
                &[],
            ),
            name,
            symbol_names: interface.symbol_names,
            exports,
            types: interface.types,
            procedural_macros: None,
            dependencies: module_dependencies(&self.config.modules),
        }
        .with_procedural_macros(self.phase.procedural_macros)
    }
}

/// The modules one compilation imported, excluding core: the canonical
/// module-level dependency edges (CLEAN-03), recorded from the module
/// environment import discovery populated rather than scraped from
/// source text afterwards.
fn module_dependencies(modules: &crate::compiling::module::ModuleEnvironment) -> Vec<ModuleId> {
    let mut dependencies: Vec<ModuleId> = modules
        .iter_modules()
        .map(|(module_id, _)| module_id)
        .filter(|module_id| *module_id != ModuleId::Core)
        .collect();
    dependencies.sort();
    dependencies
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::compiling::module::ModuleId;
    use std::path::PathBuf;
    use talk_vm::interp::{Budgets, HostValue, Value};
    use talk_vm::io::CaptureIO;

    fn service_with_effects(
        source: &str,
        exports: &[&str],
        allowed_effects: &[&str],
    ) -> Result<Executable, String> {
        let typed = Driver::new(vec![Source::from(source)], DriverConfig::new("Svc"))
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
        let names: Vec<String> = exports.iter().map(|name| name.to_string()).collect();
        let allowed: Vec<String> = allowed_effects
            .iter()
            .map(|name| name.to_string())
            .collect();
        typed.compile_service(&names, &allowed)
    }

    fn service_executable(source: &str, exports: &[&str]) -> Result<Executable, String> {
        service_with_effects(source, exports, &["io", "alloc", "async", "panic"])
    }

    #[test]
    fn service_export_calls_with_scalar_and_string_arguments() {
        let exe = service_executable(
            "pub func double(n: Int) -> Int { n * 2 }\n\npub func shout(text: String) -> String { text + \"!\" }\n",
            &["double", "shout"],
        )
        .expect("service compiles");

        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export("double", &[HostValue::Int(21)], Budgets::default(), &mut io)
            .expect("double runs");
        assert_eq!(outcome.value, Value::I64(42));

        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export(
                "shout",
                &[HostValue::String(b"hey".to_vec())],
                Budgets::default(),
                &mut io,
            )
            .expect("shout runs");
        assert_eq!(
            outcome.string_bytes(&outcome.value).expect("string result"),
            b"hey!"
        );
        let balance = outcome.balance();
        if balance.result_exact {
            assert_eq!(
                balance.live_allocations, balance.result_allocations,
                "export call leaked allocations"
            );
        }
    }

    #[test]
    fn executable_stats_stay_with_their_owners() {
        let source = "pub func answer() -> Int { 20 + 22 }\n";
        let typed = Driver::new(vec![Source::from(source)], DriverConfig::new("Svc"))
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());

        // Compiler counts come from MIR publication.
        let output = typed
            .compile_mir(MirEntry::Exports {
                names: &["answer".to_string()],
                allowed_effects: &[],
            })
            .expect("service publishes MIR");
        assert!(
            output
                .optimizations
                .passes
                .iter()
                .any(|pass| pass.name == "inline_small" && pass.applied > 0),
            "expected inlining in {:?}",
            output.optimizations
        );
        assert!(
            output
                .optimizations
                .passes
                .iter()
                .any(|pass| pass.name == "dead_functions" && pass.applied > 0),
            "expected function DCE in {:?}",
            output.optimizations
        );
        assert!(
            output
                .optimizations
                .passes
                .iter()
                .any(|pass| pass.name == "dead_handlers" && pass.applied > 0),
            "expected handler DCE in {:?}",
            output.optimizations
        );

        // The adapter reports its own counts; the VM accumulates per run.
        let exe = talk_bytecode::compile(&output.module).expect("module lowers");
        let mut stats = exe.vm_stats();
        assert_eq!(stats.runs(), 0);
        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export_with_stats("answer", &[], Budgets::default(), &mut io, &mut stats)
            .expect("answer runs");
        assert_eq!(outcome.value, Value::I64(42));
        assert_eq!(stats.runs(), 1);
    }

    // The checked-load fusion matches a compiler-emitted instruction
    // shape; any change to lowering or to the pass's own rewrite that
    // stops the pattern matching would silently disable it. This pins
    // that a real indexed read keeps fusing.
    #[test]
    fn array_indexing_keeps_the_checked_load_fusion() {
        let source = "pub func pick() -> Int {\n\tlet values = [10, 20, 30]\n\tvalues.get(1)\n}\n";
        let exe = service_executable(source, &["pick"]).expect("service compiles");
        assert!(
            exe.adapter_stats().checked_indexed_loads > 0,
            "expected checked indexed loads to fuse"
        );
    }

    #[test]
    fn enum_matches_lower_to_runtime_switch_dispatch() {
        let source = "enum Choice {\n\tcase zero, one, two\n}\npub func choose() -> Int {\n\tlet choice = Choice.two\n\tmatch choice {\n\t\t.zero -> 0,\n\t\t.one -> 1,\n\t\t.two -> 2\n\t}\n}\n";
        let exe = service_executable(source, &["choose"]).expect("service compiles");
        assert!(exe.render_bytecode().contains("switch r"));

        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export("choose", &[], Budgets::default(), &mut io)
            .expect("choose runs");
        assert_eq!(outcome.value, Value::I64(2));
    }

    #[test]
    fn service_export_effects_reach_the_host() {
        let exe = service_executable(
            "pub func speak() -> Int {\n\tprint(\"hi\")\n\t7\n}\n",
            &["speak"],
        )
        .expect("service compiles");
        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export("speak", &[], Budgets::default(), &mut io)
            .expect("speak runs");
        assert_eq!(outcome.value, Value::I64(7));
        assert_eq!(io.out, b"hi\n");
    }

    #[test]
    fn service_export_sees_top_level_globals() {
        let exe = service_executable(
            "let base = 40\n\npub func plus(n: Int) -> Int { base + n }\n",
            &["plus"],
        )
        .expect("service compiles");
        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export("plus", &[HostValue::Int(2)], Budgets::default(), &mut io)
            .expect("plus runs");
        assert_eq!(outcome.value, Value::I64(42));
    }

    #[test]
    fn service_export_contract_violations_are_compile_errors() {
        let private = service_executable("func hidden() -> Int { 1 }\n", &["hidden"]);
        assert!(private.err().expect("private export").contains("public"));

        let generic = service_executable("pub func same<T>(value: T) -> T { value }\n", &["same"]);
        assert!(generic.err().expect("generic export").contains("generic"));

        let mutable = service_executable(
            "pub func bump(mut n: Int) -> Int {\n\tn = n + 1\n\tn\n}\n",
            &["bump"],
        );
        assert!(mutable.err().expect("mut-param export").contains("mut"));

        let missing = service_executable("pub func real() -> Int { 1 }\n", &["fake"]);
        assert!(
            missing
                .err()
                .expect("missing export")
                .contains("no function named")
        );
    }

    #[test]
    fn sequential_borrowed_if_lets_compile_and_run() {
        // Bug: the for-loop payload `item` is borrow-typed (`&Shade` out
        // of `next()`'s Optional), but `settle_owned_match` registered it
        // as an arm-owned temporary with its borrow stripped — so each
        // sequential `if let` compiled as an owning match and released it,
        // a double release the balance verifier panics on at compile.
        let source = "enum Shade {\n\
            \tcase light(String)\n\
            \tcase dark(String)\n\
            }\n\
            \n\
            func bump(mut buf: [Int], x: &String) -> Void {\n\
            \tbuf.push(x.byte_count)\n\
            }\n\
            \n\
            pub func tally() -> Int {\n\
            \tlet shades = [Shade.light(\"day\"), Shade.dark(\"noon\")]\n\
            \tlet buf: [Int] = []\n\
            \tfor item in shades {\n\
            \t\tif let .light(x) = item {\n\
            \t\t\tbump(buf: buf, x: x)\n\
            \t\t}\n\
            \t\tif let .dark(x) = item {\n\
            \t\t\tbump(buf: buf, x: x)\n\
            \t\t}\n\
            \t}\n\
            \tbuf.count\n\
            }\n";
        let exe = service_executable(source, &["tally"]).expect("service compiles");
        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export("tally", &[], Budgets::default(), &mut io)
            .expect("tally runs");
        assert_eq!(outcome.value, Value::I64(2));
        let balance = outcome.balance();
        if balance.result_exact {
            assert_eq!(
                balance.live_allocations, balance.result_allocations,
                "sequential if-lets unbalanced the refcounts"
            );
        }
    }

    #[test]
    fn array_literal_of_borrowed_param_at_call_argument() {
        // A literal argument checks against the callee's borrow-by-default
        // param type: the peel must keep pushing the element type inward
        // so a borrowed element coerces by donation, exactly as it does
        // through an annotated let or a constructor argument. Array,
        // tuple, and record constructions all share the peel path.
        let source = "func show(items: [String]) -> Int {\n\
            \titems.count\n\
            }\n\
            \n\
            func pair(items: (String, Int)) -> Int {\n\
            \titems.1\n\
            }\n\
            \n\
            func rec(entry: { name: String }) -> Int {\n\
            \tentry.name.byte_count\n\
            }\n\
            \n\
            pub func direct(lhs: String) -> Int {\n\
            \tshow(items: [lhs]) + pair(items: (lhs, 2)) + rec(entry: { name: lhs })\n\
            }\n";
        let exe = service_executable(source, &["direct"]).expect("service compiles");
        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export(
                "direct",
                &[HostValue::String(b"hey".to_vec())],
                Budgets::default(),
                &mut io,
            )
            .expect("direct runs");
        assert_eq!(outcome.value, Value::I64(6));
        let balance = outcome.balance();
        if balance.result_exact {
            assert_eq!(
                balance.live_allocations, balance.result_allocations,
                "borrowed element donation unbalanced the refcounts"
            );
        }
    }

    #[test]
    fn control_flow_arguments_of_borrowed_param() {
        // Checking mode must propagate through every construction under a
        // peeled borrow-by-default param — match (and the ifs that desugar
        // to it), blocks, and literals whose element type only the callee
        // knows (the unannotated let resolves through the deferred
        // donation judgment when the call pins its element type).
        let source = "func show(items: [String]) -> Int {\n\
            \titems.count\n\
            }\n\
            \n\
            func via_if(lhs: String, flag: Bool) -> Int {\n\
            \tshow(items: if flag { [lhs] } else { [] })\n\
            }\n\
            \n\
            func via_match(lhs: String, flag: Bool) -> Int {\n\
            \tshow(items: match flag {\n\
            \t\ttrue -> [lhs, lhs],\n\
            \t\tfalse -> []\n\
            \t})\n\
            }\n\
            \n\
            func via_block(lhs: String) -> Int {\n\
            \tshow(items: {\n\
            \t\tlet tag = 1;\n\
            \t\t[lhs, lhs, lhs]\n\
            \t})\n\
            }\n\
            \n\
            func via_plain_let(lhs: String) -> Int {\n\
            \tlet items = [lhs, lhs, lhs, lhs]\n\
            \tshow(items: items)\n\
            }\n\
            \n\
            pub func tally(lhs: String) -> Int {\n\
            \tvia_if(lhs: lhs, flag: true) + via_match(lhs: lhs, flag: true) + via_block(lhs: lhs) + via_plain_let(lhs: lhs)\n\
            }\n";
        let exe = service_executable(source, &["tally"]).expect("service compiles");
        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export(
                "tally",
                &[HostValue::String(b"hey".to_vec())],
                Budgets::default(),
                &mut io,
            )
            .expect("tally runs");
        assert_eq!(outcome.value, Value::I64(10));
        let balance = outcome.balance();
        if balance.result_exact {
            assert_eq!(
                balance.live_allocations, balance.result_allocations,
                "borrowed donations through control flow unbalanced the refcounts"
            );
        }
    }

    #[test]
    fn compiled_images_are_deterministic_in_process() {
        // Two full pipelines over the same source must encode identical
        // images — the in-process half of the ADR 0043 fixed-point
        // requirement (the cross-process half lives in talk_tests.rs).
        let source = "pub func shout(text: String) -> String { text + \"!\" }\n\npub func nap() -> Int { sleep(ms: 0) }\n";
        let compile = || {
            service_with_effects(source, &["shout", "nap"], &["io", "alloc"])
                .expect("service compiles")
                .encode_bytecode()
                .expect("encode")
        };
        assert_eq!(
            compile(),
            compile(),
            "the same source compiled to different images in one process"
        );
    }

    #[test]
    fn service_effect_gate_is_a_subset_check() {
        // `sleep` performs 'io through the effect wrapper; `print` would
        // not do — it writes through the raw io instruction and carries
        // no effect (the "print is not interceptable" decision).
        let effectful = "pub func nap() -> Int { sleep(ms: 0) }\n";

        // A pure export compiles under an empty capability list.
        service_with_effects(
            "pub func double(n: Int) -> Int { n * 2 }\n",
            &["double"],
            &[],
        )
        .expect("pure export needs no capabilities");

        // 'io within the allowed list compiles and runs.
        let exe =
            service_with_effects(effectful, &["nap"], &["io"]).expect("allowed effect compiles");
        let mut io = CaptureIO::default();
        let outcome = exe
            .run_export("nap", &[], Budgets::default(), &mut io)
            .expect("nap runs");
        assert_eq!(outcome.value, Value::I64(0));

        // 'io outside the allowed list is a compile error naming the
        // effect — the denial is the row check, not a runtime trap.
        let denied = service_with_effects(effectful, &["nap"], &["alloc"]);
        let message = denied.err().expect("denied effect");
        assert!(message.contains("'io"), "{message}");
        assert!(message.contains("does not allow"), "{message}");
    }

    #[test]
    fn service_exports_survive_the_wire_format() {
        let exe = service_executable("pub func double(n: Int) -> Int { n * 2 }\n", &["double"])
            .expect("service compiles");
        let encoded = exe.encode_bytecode().expect("encode");
        let decoded = talk_vm::Module::decode_bytecode(&encoded).expect("decode");
        let mut io = CaptureIO::default();
        let outcome = talk_vm::interp::run_export(
            &decoded,
            "double",
            &[HostValue::Int(21)],
            crate::compiling::mir::string_shape(),
            Budgets::default(),
            &mut io,
        )
        .expect("decoded module runs");
        assert_eq!(outcome.value, Value::I64(42));
    }

    #[test]
    fn typed_module_exports_only_its_own_schemes() {
        // A library's exported schemes must be keyed by its own binders
        // only (ADR 0053: slices carry own facts; imported facts travel
        // in their declarers' slices).
        let typed = Driver::new(
            vec![Source::from(
                "pub struct Tiny {\n\tlet x: Int\n\n\tfunc double() -> Int {\n\t\tself.x + self.x\n\t}\n}",
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
        // Own symbols carry the compile's module stamp (Main here);
        // anything else in the export is a foreign leak.
        let foreign: Vec<_> = module
            .types
            .schemes
            .keys()
            .filter(|symbol| symbol.module_id() != Some(crate::compiling::module::ModuleId::Main))
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

        let id_a = ModuleId::External(0);
        let mut config_a = DriverConfig::new("TestDriver");
        config_a.module_id = id_a;
        let driver_a = Driver::new(
            vec![Source::from(current_dir.join("dev/fixtures/a.tlk"))],
            config_a,
        );
        let resolved_a = driver_a.parse().unwrap().resolve_names().unwrap();
        assert!(!resolved_a.has_errors());

        let module_a = resolved_a.module("A");
        let mut module_environment = ModuleEnvironment::default();
        module_environment.import_compiled(module_a, id_a).unwrap();
        let config = DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(module_environment),
            mode: CompilationMode::Library,
            module_name: "Test".to_string(),
            parse_mode: ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
            catalog: Default::default(),
            parser: None,
            parse_cache: None,
            precompiled_sources: Default::default(),
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
    fn sibling_conformance_rows_collide_at_collection() {
        // ADR 0053 global coherence: module B re-declaring a conformance
        // module A already ships errors when B COLLECTS — no co-importing
        // consumer required. (Inherent extend members deliberately keep
        // the old use-site-ambiguity rule; only conformance rows are
        // globally coherent.)
        let id_a = ModuleId::External(0);
        let mut config_a = DriverConfig::new("TestDriver");
        config_a.module_id = id_a;
        let driver_a = Driver::new(
            vec![Source::from(
                "\npub protocol Mark {\n\tfunc mark() -> Int\n}\nextend Int: Mark {\n\tpub func mark() -> Int { 1 }\n}\n",
            )],
            config_a,
        );
        let typed_a = driver_a
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        assert!(!typed_a.has_errors(), "{:?}", typed_a.diagnostics());
        let module_a = typed_a.module("A");

        let mut module_environment = ModuleEnvironment::default();
        module_environment.import_compiled(module_a, id_a).unwrap();
        let mut config = DriverConfig::new("TestDriver");
        config.mode = CompilationMode::Library;
        config.modules = Rc::new(module_environment);
        let driver_b = Driver::new(
            vec![Source::from(
                "use A::{ Mark }\nextend Int: Mark {\n\tpub func mark() -> Int { 2 }\n}\n",
            )],
            config,
        );
        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        assert!(typed.has_errors(), "the duplicate row must collide");
        let rendered = typed
            .diagnostics()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            rendered.contains("Overlapping conformance"),
            "expected a collection-time overlap diagnostic: {rendered}"
        );
    }

    #[test]
    fn multi_module_compiles_are_deterministic_in_process() {
        // The one-table architecture makes slot order a function of
        // insertion order; two identical two-module compiles must produce
        // byte-identical fact slices (the cross-module half of the
        // determinism gate).
        let compile = || {
            let id_a = ModuleId::External(0);
            let mut config_a = DriverConfig::new("TestDriver");
            config_a.module_id = id_a;
            let driver_a = Driver::new(
                vec![Source::from(
                    "\npub protocol Tag {\n\tfunc tag() -> Int\n}\npub struct Box {\n\tpub let n: Int\n}\nextend Box: Tag {\n\tpub func tag() -> Int { self.n }\n}\nextend Int: Tag {\n\tpub func tag() -> Int { 7 }\n}\n",
                )],
                config_a,
            );
            let typed_a = driver_a
                .parse()
                .unwrap()
                .resolve_names()
                .unwrap()
                .type_check();
            assert!(!typed_a.has_errors(), "{:?}", typed_a.diagnostics());
            let module_a = typed_a.module("A");
            let mut module_environment = ModuleEnvironment::default();
            module_environment.import_compiled(module_a, id_a).unwrap();
            let mut config = DriverConfig::new("TestDriver");
            config.mode = CompilationMode::Library;
            config.modules = Rc::new(module_environment);
            let driver_b = Driver::new(
                vec![Source::from(
                    "use A::{ Tag, Box }\npub func total(box: Box) -> Int { box.tag() + 1.tag() }\n",
                )],
                config,
            );
            let typed = driver_b
                .parse()
                .unwrap()
                .resolve_names()
                .unwrap()
                .type_check();
            assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
            let module_b = typed.module("B");
            bincode::serialize(&(&module_b.types.catalog, &module_b.types.schemes))
                .expect("serialize slice")
        };
        assert_eq!(
            compile(),
            compile(),
            "identical multi-module compiles encoded different fact slices"
        );
    }

    #[test]
    fn compiles_from_string() {
        let id_a = ModuleId::External(0);
        let mut config_a = DriverConfig::new("TestDriver");
        config_a.module_id = id_a;
        let driver_a = Driver::new(
            vec![Source::from(
                "
            pub struct Hello {
                let x: Int
            }
            ",
            )],
            config_a,
        );

        let module_a = driver_a
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .module("A");

        assert!(module_a.exports.contains_key("Hello"));

        let mut module_environment = ModuleEnvironment::default();
        module_environment.import_compiled(module_a, id_a).unwrap();
        let config = DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(module_environment),
            mode: CompilationMode::Library,
            module_name: "Test".to_string(),
            parse_mode: ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
            catalog: Default::default(),
            parser: None,
            parse_cache: None,
            precompiled_sources: Default::default(),
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
    fn executes_stdlib_html_macro() {
        let source = r#"
use html::{ html, PreEscaped }
let name = "<Ada & friends>"
let rendered = @html {
    DOCTYPE;
    main #content .page.primary data-name=(name) hidden {
        h1 { "Hello, " (name) }
        @if true { p { "visible" } } @else { p { "hidden" } }
        @for number in [1, 2, 3] { span { (number) } }
        (PreEscaped(value: "<b>raw</b>"))
        br;
    }
}
print_raw(rendered.into_string())
0
"#;
        let typed = Driver::new(
            vec![Source::from(source)],
            DriverConfig::new("HtmlMacroTest").executable(),
        )
        .parse()
        .expect("HTML source parses")
        .resolve_names()
        .expect("HTML source resolves")
        .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());

        let executable = typed
            .compile_executable(None)
            .expect("HTML source compiles");
        let mut io = talk_vm::io::CaptureIO::default();
        let value = executable.run(&mut io).expect("HTML source executes");
        assert_eq!(value.as_deref(), Some("0"));
        assert_eq!(
            String::from_utf8(io.out).expect("HTML output is UTF-8"),
            "<!DOCTYPE html><main id=\"content\" class=\"page primary\" data-name=\"&lt;Ada &amp; friends&gt;\" hidden><h1>Hello, &lt;Ada &amp; friends&gt;</h1><p>visible</p><span>1</span><span>2</span><span>3</span><b>raw</b><br></main>"
        );
    }

    #[test]
    fn executes_maud_compatible_html_controls_and_attributes() {
        let source = r#"
use html::{ html }
enum State {
    case ready(String)
    case waiting
}
let state = State.ready("go")
let title: String? = .some("tip")
let missing: String? = .none
let enabled = true
let disabled = false
let identifier = "panel"
let severity = "critical"
let rendered = @html {
    @let local: String = "local";
    div #(identifier) .base."quoted-class".active[enabled].hidden[disabled].{ "severity-" (severity) }
        contenteditable[enabled] draggable[disabled] readonly?
        title=[title] data-missing=[missing]
        href={ "/users/" (identifier) } {
        @if false {
            p { "wrong" }
        } @else if true {
            p { "else-if" }
        } @else {
            p { "also wrong" }
        }
        @if let .some(heading) = title {
            span { (heading) }
        }
        @match state {
            .ready(message) -> { strong { (message) } },
            .waiting -> em { "waiting" }
        }
        @for number in 0..<3 { i { (number) } }
        @for character in "ab" { u { (character) } }
        (local)
    }
}
print_raw(rendered.into_string())
0
"#;
        let typed = Driver::new(
            vec![Source::from(source)],
            DriverConfig::new("HtmlCompatibilityTest").executable(),
        )
        .parse()
        .expect("HTML compatibility source parses")
        .resolve_names()
        .expect("HTML compatibility source resolves")
        .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());

        let executable = typed
            .compile_executable(None)
            .expect("HTML compatibility source compiles");
        let mut io = talk_vm::io::CaptureIO::default();
        let value = executable
            .run(&mut io)
            .expect("HTML compatibility source executes");
        assert_eq!(value.as_deref(), Some("0"));
        assert_eq!(
            String::from_utf8(io.out).expect("HTML output is UTF-8"),
            "<div id=\"panel\" class=\"base quoted-class active severity-critical\" contenteditable readonly title=\"tip\" href=\"/users/panel\"><p>else-if</p><span>tip</span><strong>go</strong><i>0</i><i>1</i><i>2</i><u>a</u><u>b</u>local</div>"
        );
    }

    #[test]
    fn auto_discovers_qualified_local_paths() {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let importer_path = current_dir.join("dev/fixtures/qualified_importer.tlk");
        let exportee_path = current_dir.join("dev/fixtures/qualified_exportee.tlk");

        std::fs::write(&exportee_path, "pub let exported = 42\n").unwrap();
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
        std::fs::write(&sibling, "pub struct Token {}\n").unwrap();
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
        std::fs::write(&exportee_path, "pub let exported = 42\n").unwrap();
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

    /// A temporary source tree for dependency-graph tests; removed on drop.
    struct SourceTree(PathBuf);

    impl SourceTree {
        fn new(name: &str, files: &[(&str, &str)]) -> Self {
            let root =
                std::env::temp_dir().join(format!("talk-graph-{name}-{}", std::process::id()));
            let _ = std::fs::remove_dir_all(&root);
            for (relative, text) in files {
                let path = root.join(relative);
                std::fs::create_dir_all(path.parent().expect("parent dir")).unwrap();
                std::fs::write(path, text).unwrap();
            }
            Self(root)
        }

        fn path(&self, relative: &str) -> PathBuf {
            self.0.join(relative)
        }

        fn config(&self) -> DriverConfig {
            DriverConfig::new("TestDriver")
                .source_root(self.0.clone())
                .workspace_root(self.0.clone())
        }
    }

    impl Drop for SourceTree {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn parse_records_canonical_file_edges() {
        let tree = SourceTree::new(
            "edges",
            &[
                ("main.tlk", "use package::lib::util::{ answer }\nanswer()\n"),
                ("lib/util.tlk", "pub func answer() -> Int {\n\t42\n}\n"),
            ],
        );
        let parsed = Driver::new(vec![Source::from(tree.path("main.tlk"))], tree.config())
            .parse()
            .unwrap();
        assert_eq!(parsed.phase.asts.len(), 2, "the import is discovered");
        assert_eq!(
            parsed.phase.file_dependencies,
            vec![(FileID(0), FileID(1))],
            "the edge names canonical file ids, not paths or stems"
        );
    }

    #[test]
    fn recursive_glob_discovers_module_and_submodules() {
        let tree = SourceTree::new(
            "recursive-glob",
            &[
                (
                    "main.tlk",
                    "use package::foo::*\nroot_value\nchild_value\ndeep_value\n",
                ),
                ("foo.tlk", "pub let root_value = 1\n"),
                ("foo/child.tlk", "pub let child_value = 2\n"),
                ("foo/nested/deep.tlk", "pub let deep_value = 3\n"),
            ],
        );
        let parsed = Driver::new(vec![Source::from(tree.path("main.tlk"))], tree.config())
            .parse()
            .unwrap();
        assert_eq!(parsed.phase.asts.len(), 4);
        assert_eq!(parsed.phase.file_dependencies.len(), 3);

        let resolved = parsed.resolve_names().unwrap();
        assert!(
            !resolved.has_errors(),
            "glob symbols resolve: {:?}",
            resolved.phase.diagnostics
        );
    }

    #[test]
    fn recursive_glob_reports_symbol_collisions() {
        let tree = SourceTree::new(
            "recursive-glob-collision",
            &[
                ("main.tlk", "use package::foo::*\n"),
                ("foo/a.tlk", "pub let shared = 1\n"),
                ("foo/nested/b.tlk", "pub let shared = 2\n"),
            ],
        );
        let resolved = Driver::new(vec![Source::from(tree.path("main.tlk"))], tree.config())
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap();
        assert!(
            resolved.phase.diagnostics.iter().any(|diagnostic| matches!(
                diagnostic,
                crate::common::diagnostic::AnyDiagnostic::NameResolution(
                    crate::common::diagnostic::Diagnostic {
                        kind: crate::name_resolution::name_resolver::NameResolverError::ImportCollision { .. },
                        ..
                    }
                )
            )),
            "expected glob collision, got {:?}",
            resolved.phase.diagnostics
        );
    }

    #[test]
    fn parse_records_qualified_reference_edges_without_a_use_decl() {
        let tree = SourceTree::new(
            "qualified",
            &[
                ("main.tlk", "package::dep::answer()\n"),
                ("dep.tlk", "pub func answer() -> Int {\n\t42\n}\n"),
            ],
        );
        let parsed = Driver::new(vec![Source::from(tree.path("main.tlk"))], tree.config())
            .parse()
            .unwrap();
        assert_eq!(
            parsed.phase.asts.len(),
            2,
            "the reference discovers the file"
        );
        assert_eq!(parsed.phase.file_dependencies, vec![(FileID(0), FileID(1))]);
    }

    #[test]
    fn parse_distinguishes_duplicate_file_stems() {
        let tree = SourceTree::new(
            "stems",
            &[
                (
                    "main.tlk",
                    "use package::a::util::{ from_a }\nuse package::b::util::{ from_b }\nfrom_a + from_b\n",
                ),
                ("a/util.tlk", "pub let from_a = 1\n"),
                ("b/util.tlk", "pub let from_b = 2\n"),
            ],
        );
        let parsed = Driver::new(vec![Source::from(tree.path("main.tlk"))], tree.config())
            .parse()
            .unwrap();
        assert_eq!(parsed.phase.asts.len(), 3);
        // Both `util` files are distinct edge targets; stem matching
        // could only ever name one of them.
        assert_eq!(
            parsed.phase.file_dependencies,
            vec![(FileID(0), FileID(1)), (FileID(0), FileID(2))]
        );
    }

    #[test]
    fn initialization_order_follows_the_recorded_edges() {
        // main references dep only through a qualified path, so no
        // Import decl exists for stem matching to find; the recorded
        // edge still orders dep's globals before main's.
        let tree = SourceTree::new(
            "order",
            &[
                (
                    "main.tlk",
                    "let value = package::dep::answer()\nprint(value)\n",
                ),
                ("dep.tlk", "pub func answer() -> Int {\n\t42\n}\n"),
            ],
        );
        let typed = Driver::new(
            vec![
                Source::from(tree.path("main.tlk")),
                Source::from(tree.path("dep.tlk")),
            ],
            tree.config(),
        )
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
        let order: Vec<FileID> = typed
            .phase
            .program
            .files()
            .values()
            .map(|file| file.file_id)
            .collect();
        let main = order.iter().position(|id| *id == FileID(0)).unwrap();
        let dep = order.iter().position(|id| *id == FileID(1)).unwrap();
        assert!(dep < main, "dep initializes before main: {order:?}");
    }
}
