use std::{
    error::Error,
    fmt::Display,
    path::{Path, PathBuf},
    rc::Rc,
};

use derive_visitor::{DriveMut, VisitorMut};
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::{AST, NameResolved, Parsed},
    compiling::{
        driver::Exports,
        module::{ModuleEnvironment, ModuleId},
        module_path::LocalModulePaths,
    },
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    label::Label,
    name::Name,
    name_resolution::{
        builtins,
        decl_declarer::DeclDeclarer,
        symbol::{Symbol, SymbolKind, Symbols},
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind, Import, ImportPath, ImportedSymbols, Visibility},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        inline_ir_instruction::InlineIRInstructionKind,
        match_arm::MatchArm,
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    on,
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NameResolverError {
    UndefinedName(String),
    Unresolved(Name),
    AmbiguousName(Name, Vec<Symbol>),
    ShadowedEffectHandler(String),
    ModuleNotFound(String),
    SymbolNotFoundInModule(String),
    SymbolNotPublic(String),
    DuplicateExport(String),
    DuplicateDeclaration(String),
    /// A bare reference or unresolvable call into an overload set
    /// (ADR 0041): several full callable names remain viable.
    AmbiguousCallable {
        name: String,
        candidates: Vec<String>,
    },
    /// A `pub` member declared inside a nominal that is not itself
    /// public (ADR 0042): rejected rather than accepted as an
    /// unreachable export.
    PublicMemberPrivateOwner {
        member: String,
        owner: String,
    },
    /// An import binding collides with an existing declaration or
    /// import of the same name (ADR 0042): never resolved by insertion
    /// order.
    ImportCollision {
        name: String,
        existing: Symbol,
        imported: Symbol,
    },
}

impl Error for NameResolverError {}
impl Display for NameResolverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefinedName(name) => write!(f, "Undefined name: {name}"),
            Self::Unresolved(name) => write!(f, "Unresolved symbol: {name:?}"),
            Self::AmbiguousName(name, candidates) => {
                write!(f, "Ambiguous: {name:?}, candidates: {candidates:?}")
            }
            Self::ShadowedEffectHandler(name) => {
                write!(f, "Effect handler shadowed: {name}")
            }
            Self::ModuleNotFound(path) => {
                write!(f, "Cannot find module: {path}")
            }
            Self::SymbolNotFoundInModule(name) => {
                write!(f, "Symbol '{name}' not found in module")
            }
            Self::SymbolNotPublic(name) => {
                write!(f, "Symbol '{name}' is not public")
            }
            Self::DuplicateExport(name) => {
                write!(f, "Duplicate export: '{name}'")
            }
            Self::DuplicateDeclaration(name) => {
                write!(f, "'{name}' is declared more than once in this scope")
            }
            Self::AmbiguousCallable { name, candidates } => {
                write!(
                    f,
                    "Ambiguous reference to '{name}': candidates are {}",
                    candidates.join(", ")
                )
            }
            Self::PublicMemberPrivateOwner { member, owner } => {
                write!(
                    f,
                    "'{member}' cannot be public because its owner '{owner}' is not public"
                )
            }
            Self::ImportCollision { name, .. } => {
                write!(
                    f,
                    "'{name}' is already bound in this file; rename the import with `as` or remove one of the bindings"
                )
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub node_id: NodeID,
    pub parent_id: Option<NodeID>,
    pub values: FxHashMap<String, Symbol>,
    pub types: FxHashMap<String, Symbol>,
    pub handlers: FxHashMap<Symbol, (Symbol, NodeID)>,
    /// Named-callable overload sets by base name (ADR 0041). Every
    /// func-valued binder registers here; a set of two or more supersedes
    /// the single `types` entry (which keeps the last declaration for
    /// name-keyed consumers) and calls select among it by written labels.
    pub overloads: FxHashMap<String, Vec<Symbol>>,
    pub depth: u32,
}

impl Scope {
    pub fn new(node_id: NodeID, parent_id: Option<NodeID>, depth: u32) -> Self {
        Scope {
            node_id,
            parent_id,
            depth,
            values: Default::default(),
            types: Default::default(),
            handlers: Default::default(),
            overloads: Default::default(),
        }
    }
}

/// One resolver-owned record per declared symbol (ADR 0042): the
/// defining file, owning nominal, declaration role, the visibility the
/// author wrote, and the visibility the compiler concluded. This table
/// is the single visibility authority; every accessibility question
/// reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeclarationRecord {
    pub file: FileID,
    pub owner: Option<Symbol>,
    pub role: SymbolKind,
    pub declared: Visibility,
    pub effective: Visibility,
}

#[derive(Clone, Debug, Default)]
pub struct ResolvedNames {
    pub scopes: FxHashMap<NodeID, Scope>,
    /// Declared external label sequences for named callables (ADR 0041),
    /// used for resolution-time overload selection. Labels are syntactic,
    /// so resolution reads them off declarations directly; typing's
    /// callable contracts remain the checking authority.
    pub callable_labels: FxHashMap<Symbol, Vec<crate::types::callables::ArgumentLabel>>,
    pub symbol_names: FxHashMap<Symbol, String>,
    pub symbols_to_node: FxHashMap<Symbol, NodeID>,
    pub child_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub mutated_symbols: IndexSet<Symbol>,
    /// Per-symbol visibility records (ADR 0042).
    pub declarations: FxHashMap<Symbol, DeclarationRecord>,
}

impl ResolvedNames {
    /// Whether a locally declared symbol is visible outside its file.
    pub fn is_public(&self, symbol: &Symbol) -> bool {
        self.declarations
            .get(symbol)
            .is_some_and(|record| record.effective == Visibility::Public)
    }

    /// Locally declared symbols visible outside their file.
    pub fn public_symbols(&self) -> impl Iterator<Item = Symbol> + '_ {
        self.declarations
            .iter()
            .filter(|(_, record)| record.effective == Visibility::Public)
            .map(|(&symbol, _)| symbol)
    }
}

impl ResolvedNames {
    pub fn exports(&self) -> Exports {
        let mut res = Exports::default();
        let mut file_scopes = self
            .scopes
            .iter()
            .filter(|(scope_id, _)| scope_id.1 == 0)
            .collect_vec();
        file_scopes.sort_by_key(|(scope_id, _)| **scope_id);

        for (_, scope) in file_scopes {
            // Only file-level scopes (node index 0)

            for (name, &symbol) in &scope.types {
                if self.is_public(&symbol) && !matches!(symbol, Symbol::Builtin(..)) {
                    res.entry(name.clone()).or_default().push(symbol);
                }
            }
            for (name, &symbol) in &scope.values {
                if self.is_public(&symbol) && !matches!(symbol, Symbol::Builtin(..)) {
                    res.entry(name.clone()).or_default().push(symbol);
                }
            }
            // Overloaded callables export their whole public set; the
            // single scope entry above only carried the last declaration.
            for (name, set) in &scope.overloads {
                if set.len() < 2 {
                    continue;
                }
                let public: Vec<Symbol> = set
                    .iter()
                    .copied()
                    .filter(|symbol| self.is_public(symbol))
                    .collect();
                if public.len() < 2 {
                    continue;
                }
                res.insert(name.clone(), public);
            }
        }
        for set in res.values_mut() {
            set.dedup();
        }
        res
    }
}

#[derive(Debug, VisitorMut)]
#[visitor(
    Func(enter, exit),
    FuncSignature,
    Stmt(enter, exit),
    MatchArm(enter, exit),
    Decl(enter, exit),
    Expr(enter, exit),
    TypeAnnotation(enter),
    Pattern(enter),
    Block(enter, exit)
)]
pub struct NameResolver {
    pub symbols: Symbols,
    diagnostics: IndexSet<Diagnostic<NameResolverError>>,

    pub phase: ResolvedNames,

    pub(super) current_module_id: crate::compiling::module::ModuleId,
    pub(super) modules: Rc<ModuleEnvironment>,
    path_to_file_id: FxHashMap<String, FileID>,
    file_path_by_id: FxHashMap<FileID, String>,
    local_modules: LocalModulePaths,

    // Scope stuff
    pub(super) scopes: FxHashMap<NodeID, Scope>,
    pub(super) current_scope_id: Option<NodeID>,
    // A local `let`'s binders become visible *after* its initializer:
    // they are staged here on decl entry and inserted into the enclosing
    // scope on decl exit, so the rhs resolves against outer bindings.
    pending_locals: Vec<Vec<(String, Symbol)>>,
    // Call callees already bound by overload selection (ADR 0041); the
    // generic variable pass must not re-resolve them by base name.
    overload_selected: FxHashSet<NodeID>,
    // Predeclared public module binders by pattern node (ADR 0041): the
    // declaring pass reuses the exact symbol, never reuse-by-name, so
    // overload siblings keep distinct declarations.
    pub(super) predeclared: FxHashMap<NodeID, Symbol>,
    // Explicit `use` bindings by file scope and local name (ADR 0042):
    // the collision authority for import-vs-import and
    // declaration-vs-import conflicts.
    explicit_imports: FxHashMap<(NodeID, String), Symbol>,

    // For figuring out child types
    pub(super) nominal_stack: Vec<(Symbol, NodeID)>,
    // Pattern roots of in-flight `for` statements: a loop binder pattern
    // declares fresh locals on entry (there is no `let` to declare them).
    for_pattern_roots: Vec<NodeID>,
}

#[allow(clippy::expect_used)]
impl NameResolver {
    pub fn new(modules: Rc<ModuleEnvironment>, current_module_id: ModuleId) -> Self {
        Self::with_source_root(modules, current_module_id, PathBuf::new())
    }

    pub fn with_source_root(
        modules: Rc<ModuleEnvironment>,
        current_module_id: ModuleId,
        source_root: PathBuf,
    ) -> Self {
        let mut resolver = Self {
            symbols: Default::default(),
            diagnostics: Default::default(),
            phase: ResolvedNames::default(),
            current_module_id,
            scopes: Default::default(),
            current_scope_id: None,
            pending_locals: Default::default(),
            overload_selected: Default::default(),
            predeclared: Default::default(),
            explicit_imports: Default::default(),
            nominal_stack: Default::default(),
            for_pattern_roots: Default::default(),
            modules,
            path_to_file_id: Default::default(),
            file_path_by_id: Default::default(),
            local_modules: LocalModulePaths::new(source_root),
        };

        resolver.init_root_scope();
        resolver
    }

    fn init_root_scope(&mut self) {
        // This is kept for backwards compatibility but doesn't add builtins
        // Builtins are added per-file in resolve()
    }

    /// Create a root scope for a specific file and import builtins into it
    fn init_file_scope(&mut self, file_id: FileID, path: &str, skip_core_prelude: bool) {
        let scope_id = NodeID(file_id, 0);
        // Always create fresh scope with builtins
        let mut scope = Scope::new(scope_id, None, 1);
        builtins::import_builtins(&mut scope);

        // Import Core module exports as prelude (unless the file opts out)
        if !skip_core_prelude && let Some(core_module) = self.modules.get_module_by_name("Core") {
            let mut pairs = Vec::new();
            for (name, set) in &core_module.exports {
                Self::bind_export_set(&mut scope, name, set);
                pairs.extend(Self::collect_module_labels(core_module, set));
            }
            self.apply_callable_labels(pairs);
        }

        if Path::new(path).file_name().and_then(|name| name.to_str()) == Some("package.tlk")
            && let Some(package_module) = self.modules.get_module_by_name("Package")
        {
            let mut pairs = Vec::new();
            for (name, set) in &package_module.exports {
                Self::bind_export_set(&mut scope, name, set);
                pairs.extend(Self::collect_module_labels(package_module, set));
            }
            self.apply_callable_labels(pairs);
        }

        self.scopes.insert(scope_id, scope);
        self.current_scope_id = Some(scope_id);
    }

    pub fn resolve(
        &mut self,
        mut asts: Vec<AST<Parsed>>,
    ) -> (Vec<AST<NameResolved>>, ResolvedNames) {
        // Create per-file scopes with builtins for module isolation
        for ast in &asts {
            self.init_file_scope(ast.file_id, &ast.path, ast.skip_core_prelude);
        }

        // Predeclare module-scope nominals across all ASTs first, so `extend` resolution
        // doesn't depend on file order. Core well-known structs are assigned reserved
        // symbols by name when they are declared, not by declaration order.
        for ast in asts.iter_mut() {
            let file_scope_id = NodeID(ast.file_id, 0);
            self.current_scope_id = Some(file_scope_id);
            let mut declarer = DeclDeclarer::new(self, &mut ast.node_ids);
            let decls: Vec<&Decl> = ast
                .roots
                .iter()
                .filter_map(|r| {
                    if let Node::Decl(decl) = r {
                        Some(decl)
                    } else {
                        None
                    }
                })
                .collect();
            declarer.predeclare_nominals(&decls);
            declarer.predeclare_values(&decls);
        }

        // Predeclare effects in a separate pass after all nominals, so cross-file
        // effect references resolve without changing nominal predeclaration behavior.
        for ast in asts.iter_mut() {
            let file_scope_id = NodeID(ast.file_id, 0);
            self.current_scope_id = Some(file_scope_id);
            let mut declarer = DeclDeclarer::new(self, &mut ast.node_ids);
            let decls: Vec<&Decl> = ast
                .roots
                .iter()
                .filter_map(|r| {
                    if let Node::Decl(decl) = r {
                        Some(decl)
                    } else {
                        None
                    }
                })
                .collect();
            declarer.predeclare_effects(&decls);
        }

        // Predeclare module-scope type aliases after nominals/effects so imports can
        // see public aliases without changing nominal predeclaration behavior.
        for ast in asts.iter_mut() {
            let file_scope_id = NodeID(ast.file_id, 0);
            self.current_scope_id = Some(file_scope_id);
            let mut declarer = DeclDeclarer::new(self, &mut ast.node_ids);
            let decls: Vec<&Decl> = ast
                .roots
                .iter()
                .filter_map(|r| {
                    if let Node::Decl(decl) = r {
                        Some(decl)
                    } else {
                        None
                    }
                })
                .collect();
            declarer.predeclare_type_aliases(&decls);
        }

        // ADR 0042: a public type name may be exported by only one
        // declaration per module. Runs after predeclaration (each file
        // scope holds only its own declarations) and before imports
        // (which add foreign bindings to file scopes).
        self.check_duplicate_type_exports();

        // Process imports (before full declaration phase so extends can see imported types)
        {
            // Build a map from normalized module path keys to FileIDs.
            self.file_path_by_id = asts
                .iter()
                .map(|ast| (ast.file_id, ast.path.clone()))
                .collect();
            self.path_to_file_id = asts
                .iter()
                .flat_map(|ast| {
                    module_path_keys(&ast.path)
                        .into_iter()
                        .map(move |key| (key, ast.file_id))
                })
                .collect();

            // Build a map of private let binding names per file (for better error messages)
            let private_let_names: FxHashMap<FileID, FxHashSet<String>> = asts
                .iter()
                .map(|ast| {
                    let names: FxHashSet<String> = ast
                        .roots
                        .iter()
                        .filter_map(|root| {
                            if let Node::Decl(Decl {
                                visibility: Visibility::Private,
                                kind: DeclKind::Let { lhs, .. },
                                ..
                            }) = root
                                && let PatternKind::Bind(name) = &lhs.kind
                            {
                                return Some(name.name_str());
                            }
                            None
                        })
                        .collect();
                    (ast.file_id, names)
                })
                .collect();

            // Collect imports for each file (to avoid borrow conflicts)
            // (file_id, source_path, vec of (import, decl_node_id))
            #[allow(clippy::type_complexity)]
            let mut file_imports: Vec<(FileID, String, Vec<(Import, NodeID)>)> = Vec::new();
            for ast in &asts {
                let mut imports = Vec::new();
                if Path::new(&ast.path)
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.ends_with(".test.tlk"))
                {
                    imports.push((
                        Import {
                            symbols: ImportedSymbols::All,
                            path: ImportPath::Package("testing".into()),
                            path_span: Span {
                                start: 0,
                                end: 0,
                                file_id: ast.file_id,
                            },
                        },
                        NodeID(ast.file_id, 0),
                    ));
                }
                for root in &ast.roots {
                    if let Node::Decl(Decl {
                        id,
                        kind: DeclKind::Import(import),
                        ..
                    }) = root
                    {
                        imports.push((import.clone(), *id));
                    }
                }
                if !imports.is_empty() {
                    file_imports.push((ast.file_id, ast.path.clone(), imports));
                }
            }

            // Process each file's imports
            for (file_id, source_path, imports) in file_imports {
                let source_scope_id = NodeID(file_id, 0);

                for (import, decl_id) in imports {
                    let mut imported_module = false;
                    let mut imported_file_id = None;

                    let mut harvested = Vec::new();
                    let target_symbols: Vec<(String, Vec<Symbol>, bool)> = match &import.path {
                        ImportPath::Package(pkg_name) => {
                            let Some(module) = self.modules.get_module_by_name(pkg_name) else {
                                self.diagnostic(
                                    decl_id,
                                    NameResolverError::ModuleNotFound(pkg_name.clone()),
                                );
                                continue;
                            };
                            imported_module = true;
                            let symbols: Vec<(String, Vec<Symbol>, bool)> = module
                                .exports
                                .iter()
                                .map(|(name, set)| {
                                    let is_type =
                                        set.last().is_some_and(|symbol| is_type_symbol(symbol));
                                    (name.clone(), set.clone(), is_type)
                                })
                                .collect();
                            for (_, set, _) in &symbols {
                                harvested.extend(Self::collect_module_labels(module, set));
                            }
                            symbols
                        }
                        ImportPath::Local(module_path) => {
                            let Some(resolved) =
                                self.local_modules.resolve(&source_path, module_path)
                            else {
                                self.diagnostic(
                                    decl_id,
                                    NameResolverError::ModuleNotFound(module_path.clone()),
                                );
                                continue;
                            };
                            let target_path = resolved.to_string_lossy().to_string();

                            let Some(target_file_id) = module_path_keys(&target_path)
                                .into_iter()
                                .find_map(|key| self.path_to_file_id.get(&key).copied())
                            else {
                                self.diagnostic(
                                    decl_id,
                                    NameResolverError::ModuleNotFound(module_path.clone()),
                                );
                                continue;
                            };
                            imported_file_id = Some(target_file_id);

                            let target_scope_id = NodeID(target_file_id, 0);

                            // Get symbols from the target scope. If the target is a core file
                            // and we have the pre-compiled Core module, use its exports instead
                            // to avoid type identity conflicts from re-compiling core sources.
                            let core_module = is_core_source_path(&target_path)
                                .then(|| self.modules.get_module_by_name("Core"))
                                .flatten();
                            if let Some(core) = core_module {
                                imported_module = true;
                                let symbols: Vec<(String, Vec<Symbol>, bool)> = core
                                    .exports
                                    .iter()
                                    .map(|(name, set)| {
                                        let is_type = set
                                            .last()
                                            .is_some_and(|symbol| is_type_symbol(symbol));
                                        (name.clone(), set.clone(), is_type)
                                    })
                                    .collect();
                                for (_, set, _) in &symbols {
                                    harvested.extend(Self::collect_module_labels(core, set));
                                }
                                symbols
                            } else {
                                let Some(target_scope) = self.scopes.get(&target_scope_id) else {
                                    continue;
                                };
                                let mut symbols: Vec<(String, Vec<Symbol>, bool)> = Vec::new();
                                for (name, &symbol) in &target_scope.values {
                                    // A sibling file's overload set travels
                                    // whole (ADR 0041); labels are already in
                                    // this session's table.
                                    let set = match target_scope.overloads.get(name) {
                                        Some(set) if set.len() > 1 => set.clone(),
                                        _ => vec![symbol],
                                    };
                                    symbols.push((name.clone(), set, is_type_symbol(&symbol)));
                                }
                                for (name, &symbol) in &target_scope.types {
                                    symbols.push((
                                        name.clone(),
                                        vec![symbol],
                                        is_type_symbol(&symbol),
                                    ));
                                }
                                symbols
                            }
                        }
                    };

                    self.apply_callable_labels(harvested);
                    // Import the requested symbols
                    match &import.symbols {
                        ImportedSymbols::All => {
                            // Import all public non-builtin symbols
                            let public_symbols: FxHashSet<Symbol> =
                                self.phase.public_symbols().collect();
                            for (name, set, _) in target_symbols {
                                // Skip builtins and private symbols
                                // (core exports are public by definition)
                                let set: Vec<Symbol> = set
                                    .into_iter()
                                    .filter(|symbol| {
                                        !matches!(symbol, Symbol::Builtin(..))
                                            && (imported_module
                                                || public_symbols.contains(symbol))
                                    })
                                    .collect();
                                self.bind_import(source_scope_id, &name, &set, decl_id);
                            }
                        }
                        ImportedSymbols::Named(named_imports) => {
                            for imported in named_imports {
                                let name_to_find = &imported.name;
                                let local_name = imported.alias.as_ref().unwrap_or(name_to_find);

                                // Find the symbol in target
                                let found =
                                    target_symbols.iter().find(|(n, _, _)| n == name_to_find);

                                match found {
                                    Some((_, set, _)) => {
                                        // Check if the set is public
                                        // (core exports are public by definition)
                                        let set: Vec<Symbol> = set
                                            .iter()
                                            .copied()
                                            .filter(|symbol| {
                                                imported_module
                                                    || self.phase.is_public(symbol)
                                            })
                                            .collect();
                                        if set.is_empty() {
                                            self.diagnostic(
                                                decl_id,
                                                NameResolverError::SymbolNotPublic(
                                                    name_to_find.clone(),
                                                ),
                                            );
                                            continue;
                                        }
                                        self.bind_import(
                                            source_scope_id,
                                            local_name,
                                            &set,
                                            decl_id,
                                        );
                                    }
                                    None => {
                                        // Check if the symbol is a private let binding
                                        let is_private = imported_file_id
                                            .and_then(|target_file_id| {
                                                private_let_names.get(&target_file_id)
                                            })
                                            .map(|names| names.contains(name_to_find))
                                            .unwrap_or(false);
                                        if is_private {
                                            self.diagnostic(
                                                decl_id,
                                                NameResolverError::SymbolNotPublic(
                                                    name_to_find.clone(),
                                                ),
                                            );
                                        } else {
                                            self.diagnostic(
                                                decl_id,
                                                NameResolverError::SymbolNotFoundInModule(
                                                    name_to_find.clone(),
                                                ),
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Move any diagnostics accumulated during import processing
            for diagnostic in std::mem::take(&mut self.diagnostics) {
                self.phase.diagnostics.push(diagnostic.into());
            }
        }

        // Full declaration phase - process all declarations including extends
        // (now that imports are resolved, extends can see imported types)
        for ast in asts.iter_mut() {
            let file_scope_id = NodeID(ast.file_id, 0);
            self.current_scope_id = Some(file_scope_id);
            let mut declarer = DeclDeclarer::new(self, &mut ast.node_ids);
            for root in &mut ast.roots {
                root.drive_mut(&mut declarer);
            }
        }

        // Second pass: resolve all names

        for ast in asts.iter_mut() {
            let file_scope_id = NodeID(ast.file_id, 0);
            // Borrow &mut self only while walking each root, then drop immediately.
            for root in &mut ast.roots {
                self.current_scope_id = Some(file_scope_id);
                root.drive_mut(self);
            }

            // Move any diagnostics accumulated on self into this AST.
            for diagnostic in std::mem::take(&mut self.diagnostics) {
                self.phase.diagnostics.push(diagnostic.into());
            }
        }

        self.phase.scopes = self.scopes.clone();

        (
            asts.into_iter().map(|a| a.into()).collect_vec(),
            self.phase.clone(),
        )
    }

    pub(super) fn current_scope(&self) -> Option<&Scope> {
        if let Some(current_scope_id) = self.current_scope_id {
            return self.scopes.get(&current_scope_id);
        }

        None
    }

    pub(super) fn current_scope_mut(&mut self) -> Option<&mut Scope> {
        if let Some(current_scope_id) = self.current_scope_id {
            return self.scopes.get_mut(&current_scope_id);
        }

        None
    }

    /// Returns true if the current scope is the module's root scope (not nested)
    pub(super) fn at_module_scope(&self) -> bool {
        matches!(self.current_scope_id, Some(NodeID(_, 0)))
    }

    fn lookup_in_scope(&mut self, name: &Name, scope_id: NodeID) -> Option<Symbol> {
        if let Name::Raw(raw) = name
            && raw.contains("::")
        {
            return self.lookup_qualified(raw, scope_id);
        }

        let scope = self
            .scopes
            .get(&scope_id)
            .unwrap_or_else(|| unreachable!("scope not found: {scope_id:?}, {:?}", name));

        if let Some(symbol) = scope.types.get(&name.name_str()) {
            return Some(*symbol);
        }

        if let Some(symbol) = scope.values.get(&name.name_str()) {
            return Some(*symbol);
        }

        if let Some(parent) = scope.parent_id
            && parent != scope_id
        {
            return self.lookup_in_scope(name, parent);
        }

        None
    }

    /// Diagnose public type names exported by more than one declaration
    /// in this module (ADR 0042). Values coexist through ADR 0041
    /// callable names and diagnose separately during predeclaration.
    fn check_duplicate_type_exports(&mut self) {
        let mut by_name: FxHashMap<String, Vec<Symbol>> = FxHashMap::default();
        for scope in self.scopes.values() {
            if scope.node_id.1 != 0 {
                continue;
            }
            for (name, &symbol) in &scope.types {
                if self.phase.is_public(&symbol)
                    && matches!(
                        SymbolKind::of(&symbol),
                        Some(
                            SymbolKind::Struct
                                | SymbolKind::Enum
                                | SymbolKind::Protocol
                                | SymbolKind::TypeAlias
                        )
                    )
                {
                    by_name.entry(name.clone()).or_default().push(symbol);
                }
            }
        }
        for (name, mut symbols) in by_name {
            symbols.dedup();
            if symbols.len() < 2 {
                continue;
            }
            // Deterministic: diagnose every declaration after the first
            // in file order.
            let mut nodes: Vec<NodeID> = symbols
                .iter()
                .filter_map(|symbol| self.phase.symbols_to_node.get(symbol).copied())
                .collect();
            nodes.sort();
            for node in nodes.into_iter().skip(1) {
                self.diagnostic(node, NameResolverError::DuplicateExport(name.clone()));
            }
        }
    }

    /// Insert an explicit import binding (ADR 0042). Import insertion
    /// never overwrites an existing declaration or a different earlier
    /// import; those are collision diagnostics. Prelude and builtin
    /// bindings are not declarations of this module and may be shadowed
    /// by an explicit import.
    fn bind_import(
        &mut self,
        source_scope_id: NodeID,
        local_name: &str,
        set: &[Symbol],
        decl_id: NodeID,
    ) {
        let Some(&last) = set.last() else {
            return;
        };
        let key = (source_scope_id, local_name.to_string());
        let existing = if let Some(&previous) = self.explicit_imports.get(&key) {
            Some(previous)
        } else {
            self.scopes
                .get(&source_scope_id)
                .and_then(|scope| {
                    scope
                        .types
                        .get(local_name)
                        .or_else(|| scope.values.get(local_name))
                })
                .copied()
                // Only this module's own declarations collide; prelude
                // bindings came from other modules and are shadowable.
                .filter(|symbol| self.phase.declarations.contains_key(symbol))
        };
        if let Some(existing) = existing
            && existing != last
            && !set.contains(&existing)
        {
            self.diagnostic(
                decl_id,
                NameResolverError::ImportCollision {
                    name: local_name.to_string(),
                    existing,
                    imported: last,
                },
            );
            return;
        }
        let Some(scope) = self.scopes.get_mut(&source_scope_id) else {
            return;
        };
        Self::bind_export_set(scope, local_name, set);
        self.explicit_imports.insert(key, last);
    }

    /// Bind an exported set into a scope (ADR 0041): the last symbol takes
    /// the plain name entry, and a multi-symbol callable set registers for
    /// label selection.
    fn bind_export_set(scope: &mut Scope, name: &str, set: &[Symbol]) {
        let Some(&last) = set.last() else {
            return;
        };
        if is_type_symbol(&last) {
            scope.types.insert(name.to_string(), last);
        } else {
            scope.values.insert(name.to_string(), last);
        }
        if set.len() > 1 {
            scope.overloads.insert(name.to_string(), set.to_vec());
        }
    }

    /// Harvest exported callables' labels from a module's contracts so
    /// overload selection can run in the importing module (ADR 0041).
    /// Collect-then-apply, because the module handle borrows the resolver.
    fn collect_module_labels(
        module: &crate::compiling::module::Module,
        set: &[Symbol],
    ) -> Vec<(Symbol, Vec<crate::types::callables::ArgumentLabel>)> {
        set.iter()
            .filter_map(|symbol| {
                let contract = module.types.catalog.callable_contracts.get(symbol)?;
                Some((*symbol, contract.name.labels.clone()))
            })
            .collect()
    }

    fn apply_callable_labels(
        &mut self,
        pairs: Vec<(Symbol, Vec<crate::types::callables::ArgumentLabel>)>,
    ) {
        for (symbol, labels) in pairs {
            self.phase.callable_labels.insert(symbol, labels);
        }
    }

    /// Resolve `Module::name` to its exported symbol set, silently: the
    /// diagnosing wrapper and the call-site overload selection share this.
    /// The bool is the set's visibility to the requesting file.
    fn lookup_qualified_set(
        &mut self,
        raw: &str,
        scope_id: NodeID,
    ) -> Result<(Vec<Symbol>, bool), NameResolverError> {
        let Some((module_path, symbol_name)) = raw.rsplit_once("::") else {
            return Err(NameResolverError::ModuleNotFound(raw.to_string()));
        };
        if LocalModulePaths::is_local(module_path) {
            let source_file = scope_id.0;
            let source_path = self
                .file_path_by_id
                .get(&source_file)
                .cloned()
                .ok_or_else(|| NameResolverError::ModuleNotFound(module_path.to_string()))?;
            let resolved = self
                .local_modules
                .resolve(&source_path, module_path)
                .ok_or_else(|| NameResolverError::ModuleNotFound(module_path.to_string()))?;
            let target_path = resolved.to_string_lossy().to_string();
            let target_file_id = module_path_keys(&target_path)
                .into_iter()
                .find_map(|key| self.path_to_file_id.get(&key).copied())
                .ok_or_else(|| NameResolverError::ModuleNotFound(module_path.to_string()))?;
            let target_scope_id = NodeID(target_file_id, 0);
            if let Some(core) = is_core_source_path(&target_path)
                .then(|| self.modules.get_module_by_name("Core"))
                .flatten()
            {
                let set = core
                    .exports
                    .get(symbol_name)
                    .cloned()
                    .ok_or_else(|| {
                        NameResolverError::SymbolNotFoundInModule(symbol_name.to_string())
                    })?;
                let pairs = Self::collect_module_labels(core, &set);
                self.apply_callable_labels(pairs);
                return Ok((set, true));
            }
            let target_scope = self
                .scopes
                .get(&target_scope_id)
                .ok_or_else(|| NameResolverError::ModuleNotFound(module_path.to_string()))?;
            if let Some(set) = target_scope.overloads.get(symbol_name)
                && set.len() > 1
            {
                let set = set.clone();
                let public: Vec<Symbol> = set
                    .iter()
                    .copied()
                    .filter(|symbol| self.phase.is_public(symbol))
                    .collect();
                if public.is_empty() {
                    return Err(NameResolverError::SymbolNotPublic(symbol_name.to_string()));
                }
                return Ok((public, true));
            }
            let symbol = target_scope
                .values
                .get(symbol_name)
                .or_else(|| target_scope.types.get(symbol_name))
                .copied()
                .ok_or_else(|| {
                    NameResolverError::SymbolNotFoundInModule(symbol_name.to_string())
                })?;
            let public = self.phase.is_public(&symbol);
            if !public {
                return Err(NameResolverError::SymbolNotPublic(symbol_name.to_string()));
            }
            Ok((vec![symbol], true))
        } else {
            let Some(module) = self.modules.get_module_by_name(module_path) else {
                return Err(NameResolverError::ModuleNotFound(module_path.to_string()));
            };
            let set = module.exports.get(symbol_name).cloned().ok_or_else(|| {
                NameResolverError::SymbolNotFoundInModule(symbol_name.to_string())
            })?;
            let pairs = Self::collect_module_labels(module, &set);
            self.apply_callable_labels(pairs);
            Ok((set, true))
        }
    }

    fn lookup_qualified(&mut self, raw: &str, scope_id: NodeID) -> Option<Symbol> {
        match self.lookup_qualified_set(raw, scope_id) {
            Err(error) => {
                self.diagnostic(scope_id, error);
                None
            }
            Ok((set, _)) => match set.as_slice() {
                [] => None,
                [one] => Some(*one),
                _ => {
                    let name = raw.to_string();
                    let candidates = set
                        .iter()
                        .filter_map(|symbol| {
                            Some(
                                crate::types::callables::CallableName {
                                    base: name.clone(),
                                    labels: self.phase.callable_labels.get(symbol)?.clone(),
                                }
                                .to_string(),
                            )
                        })
                        .collect();
                    self.diagnostic(
                        scope_id,
                        NameResolverError::AmbiguousCallable { name, candidates },
                    );
                    set.first().copied()
                }
            },
        }
    }

    pub(super) fn lookup(&mut self, name: &Name) -> Option<Name> {
        let symbol = self.lookup_in_scope(
            name,
            self.current_scope_id
                .unwrap_or_else(|| unreachable!("no scope to declare in. name: {name:?}")),
        )?;

        Some(Name::Resolved(symbol, name.name_str()))
    }

    /// Resolve a possibly-dotted nominal path (`Res.A`): the head segment
    /// resolves in scope, every later segment walks the nominal's child
    /// types. A dotless name is an ordinary lookup.
    pub(super) fn lookup_nominal_path(&mut self, name: &Name) -> Option<Name> {
        let text = name.name_str();
        if !text.contains('.') {
            return self.lookup(name);
        }
        let mut segments = text.split('.');
        let head: Name = segments.next()?.to_string().into();
        let mut symbol = self.lookup(&head)?.symbol().ok()?;
        let current_file = self.current_scope_id.map(|scope| scope.0);
        for segment in segments {
            symbol = *self
                .phase
                .child_types
                .get(&symbol)?
                .get(&Label::Named(segment.to_string()))?;
            // ADR 0042: a nested type is a member — file-private unless
            // marked `pub`. Foreign children carry no record and are
            // public by construction.
            if let Some(record) = self.phase.declarations.get(&symbol)
                && record.effective != Visibility::Public
                && Some(record.file) != current_file
            {
                return None;
            }
        }
        Some(Name::Resolved(symbol, text))
    }

    /// The intrinsic effect is reserved independently of ordinary value
    /// shadowing, so a local named `unsafe` cannot change effect syntax.
    fn lookup_effect(&mut self, name: &Name) -> Option<Name> {
        if name.name_str() == "unsafe" {
            return Some(Name::Resolved(Symbol::Unsafe, "unsafe".into()));
        }
        self.lookup(name)
    }

    pub(super) fn diagnostic(&mut self, id: NodeID, err: NameResolverError) {
        self.diagnostics.insert(Diagnostic::<NameResolverError> {
            kind: err,
            severity: Severity::Error,
            id,
        });
    }

    pub(super) fn warning(&mut self, id: NodeID, err: NameResolverError) {
        self.diagnostics.insert(Diagnostic::<NameResolverError> {
            kind: err,
            severity: Severity::Warn,
            id,
        });
    }

    #[instrument(skip(self))]
    fn enter_scope(&mut self, node_id: NodeID) {
        self.current_scope_id = Some(node_id);
    }

    #[instrument(skip(self))]
    fn exit_scope(&mut self, node_id: NodeID) {
        let current_scope_id = self.current_scope_id.expect("no scope to exit");
        let current_scope = self.scopes.get(&current_scope_id).unwrap_or_else(|| {
            unreachable!(
                "did not get current scope ({:?}). {:?}",
                current_scope_id, self.scopes
            )
        });

        self.current_scope_id = current_scope.parent_id;
    }

    pub(super) fn declare(
        &mut self,
        name: &Name,
        kind: SymbolKind,
        node_id: NodeID,
        span: Span,
    ) -> Name {
        let at_module_scope = self.at_module_scope();
        let scope_id = self.current_scope_id.expect("no scope to declare in");
        let name_str = name.name_str();

        // Sequential `let` rebinding never lands here (those binders are
        // staged via mint_pattern), so a same-scope hit is a genuine
        // duplicate: one pattern binding a name twice, or two same-named
        // local funcs hoisted in one block — each would silently orphan
        // the other in the name-keyed map.
        if !at_module_scope
            && matches!(
                kind,
                SymbolKind::DeclaredLocal | SymbolKind::PatternBindLocal
            )
            && self
                .scopes
                .get(&scope_id)
                .and_then(|scope| scope.types.get(&name_str))
                .is_some_and(|existing| {
                    matches!(
                        existing,
                        Symbol::DeclaredLocal(..) | Symbol::PatternBindLocal(..)
                    )
                })
        {
            self.diagnostic(
                node_id,
                NameResolverError::DuplicateDeclaration(name_str.clone()),
            );
        }

        // Check if this is a nominal type or effect that was already predeclared
        // If so, return the existing symbol to avoid duplicate creation
        if matches!(
            kind,
            SymbolKind::Struct
                | SymbolKind::Enum
                | SymbolKind::Protocol
                | SymbolKind::Effect
                | SymbolKind::TypeAlias
        ) && let Some(&existing) = self
            .scopes
            .get(&scope_id)
            .and_then(|s| s.types.get(&name_str))
            && SymbolKind::of(&existing) == Some(kind)
        {
            return Name::Resolved(existing, name_str);
        }

        // Check for predeclared Globals at module scope
        // This handles public Let bindings that were predeclared for import resolution
        // Only reuse if the existing Global is public (i.e., was predeclared)
        // Non-public Globals should allow shadowing (create new symbol)
        // Note: Don't record span here - it was already recorded during predeclaration
        if at_module_scope
            && matches!(kind, SymbolKind::Global)
            && let Some(&existing) = self
                .scopes
                .get(&scope_id)
                .and_then(|s| s.types.get(&name_str))
            && matches!(existing, Symbol::Global(..))
            && self.phase.is_public(&existing)
        {
            return Name::Resolved(existing, name_str);
        }

        // A module-scope declaration never silently overwrites an
        // explicit import of the same name (ADR 0042). Predeclared
        // symbols returning through the reuse paths above never reach
        // here, so this fires once per genuinely new declaration.
        if at_module_scope
            && let Some(&imported) = self.explicit_imports.get(&(scope_id, name_str.clone()))
        {
            self.diagnostic(
                node_id,
                NameResolverError::ImportCollision {
                    name: name_str.clone(),
                    existing: imported,
                    imported,
                },
            );
        }

        let resolved = self.mint(name, kind, node_id, span);

        tracing::debug!(
            "declare type {name} {} -> {resolved:?} {:?}",
            name_str,
            self.current_scope_id
        );

        let scope = self
            .scopes
            .get_mut(&scope_id)
            .unwrap_or_else(|| unreachable!("scope not found: {:?}", scope_id));
        scope.types.insert(
            name_str,
            resolved.symbol().unwrap_or_else(|_| unreachable!()),
        );

        resolved
    }

    /// Bind a name to a symbol in the current scope without minting or
    /// reuse — the overload-sibling predeclare path (ADR 0041).
    pub(super) fn bind_value(&mut self, name: &str, symbol: Symbol) {
        let Some(scope_id) = self.current_scope_id else {
            return;
        };
        if let Some(scope) = self.scopes.get_mut(&scope_id) {
            scope.types.insert(name.to_string(), symbol);
        }
    }

    /// Register a func-valued binder in its scope's overload set
    /// (ADR 0041). A same-scope callable with an identical external-label
    /// sequence is a duplicate declaration; differing sequences coexist
    /// and calls select among them by written labels.
    pub(super) fn register_callable(
        &mut self,
        symbol: Symbol,
        base: &str,
        params: &[crate::node_kinds::parameter::Parameter],
        node_id: NodeID,
    ) {
        use crate::types::callables::ArgumentLabel;
        let labels: Vec<ArgumentLabel> = params
            .iter()
            .map(|param| match param.external_label() {
                Some(name) => ArgumentLabel::Named(name),
                None => ArgumentLabel::Omitted,
            })
            .collect();
        let Some(scope_id) = self.current_scope_id else {
            return;
        };
        let existing = self
            .scopes
            .get(&scope_id)
            .and_then(|scope| scope.overloads.get(base));
        if let Some(set) = existing {
            if set.contains(&symbol) {
                return;
            }
            if set
                .iter()
                .any(|candidate| self.phase.callable_labels.get(candidate) == Some(&labels))
            {
                self.diagnostic(
                    node_id,
                    NameResolverError::DuplicateDeclaration(
                        crate::types::callables::CallableName {
                            base: base.to_string(),
                            labels: labels.clone(),
                        }
                        .to_string(),
                    ),
                );
                return;
            }
        }
        self.phase.callable_labels.insert(symbol, labels);
        if let Some(scope) = self.scopes.get_mut(&scope_id) {
            scope
                .overloads
                .entry(base.to_string())
                .or_default()
                .push(symbol);
        }
    }

    /// The overload set visible for `base`: from the nearest scope that
    /// defines the name at all, and only when it holds two or more
    /// callables (an inner single binding shadows any outer set).
    fn visible_overloads(&self, base: &str) -> Option<Vec<Symbol>> {
        let mut scope_id = self.current_scope_id?;
        loop {
            let scope = self.scopes.get(&scope_id)?;
            if let Some(set) = scope.overloads.get(base)
                && set.len() > 1
            {
                return Some(set.clone());
            }
            if scope.types.contains_key(base) || scope.values.contains_key(base) {
                return None;
            }
            scope_id = scope.parent_id.filter(|parent| *parent != scope_id)?;
        }
    }

    /// Select one callable from an overload set by the call's written
    /// labels (ADR 0041). Trailing blocks and paren-less leading strings
    /// omit their labels by syntax and match any declared label. One exact
    /// match selects; otherwise a unique same-arity candidate recovers
    /// (typing reports its label mismatch); anything else is ambiguous.
    fn select_overload(
        &mut self,
        name: &mut Name,
        node_id: NodeID,
        set: &[Symbol],
        args: &[crate::node_kinds::call_arg::CallArg],
    ) {
        use crate::types::callables::{WrittenSlot, labels_admit};

        let slots: Vec<WrittenSlot> = args.iter().map(WrittenSlot::of).collect();
        let exact: Vec<Symbol> = set
            .iter()
            .copied()
            .filter(|symbol| {
                self.phase
                    .callable_labels
                    .get(symbol)
                    .is_some_and(|declared| labels_admit(declared, &slots))
            })
            .collect();
        let selected = match exact.as_slice() {
            [one] => Some(*one),
            [] => {
                let same_arity: Vec<Symbol> = set
                    .iter()
                    .copied()
                    .filter(|symbol| {
                        self.phase
                            .callable_labels
                            .get(symbol)
                            .is_some_and(|declared| declared.len() == slots.len())
                    })
                    .collect();
                match same_arity.as_slice() {
                    [one] => Some(*one),
                    _ => None,
                }
            }
            _ => None,
        };
        match selected {
            Some(symbol) => *name = Name::Resolved(symbol, name.name_str()),
            None => {
                let candidates = set
                    .iter()
                    .filter_map(|symbol| {
                        Some(
                            crate::types::callables::CallableName {
                                base: name.name_str(),
                                labels: self.phase.callable_labels.get(symbol)?.clone(),
                            }
                            .to_string(),
                        )
                    })
                    .collect();
                self.diagnostic(
                    node_id,
                    NameResolverError::AmbiguousCallable {
                        name: name.name_str(),
                        candidates,
                    },
                );
                // Recover to the first candidate so checking continues.
                if let Some(first) = set.first() {
                    *name = Name::Resolved(*first, name.name_str());
                }
            }
        }
    }

    /// Mint a fresh symbol for `name` (recording its defining node and
    /// name string) without making it visible in any scope. Local `let`
    /// binders go through this at their declaration point and only insert
    /// into scope once their initializer has resolved (rule 1 of
    /// docs/sequential-scoping-plan.md).
    pub(super) fn mint(
        &mut self,
        name: &Name,
        kind: SymbolKind,
        node_id: NodeID,
        span: Span,
    ) -> Name {
        let name_str = name.name_str();
        let module_id = self.current_module_id;
        let well_known_core_symbol = if self.at_module_scope() && module_id == ModuleId::Core {
            match kind {
                SymbolKind::Struct => Symbol::well_known_core_struct(&name_str),
                SymbolKind::Protocol => Symbol::well_known_core_protocol(&name_str),
                SymbolKind::Global => Symbol::well_known_core_global(&name_str),
                _ => None,
            }
        } else {
            None
        };
        let symbol = if let Some(symbol) = well_known_core_symbol {
            symbol
        } else {
            match kind {
                SymbolKind::Effect => Symbol::Effect(self.symbols.next_effect(module_id)),
                SymbolKind::Struct => Symbol::Struct(self.symbols.next_struct(module_id)),
                SymbolKind::Enum => Symbol::Enum(self.symbols.next_enum(module_id)),
                SymbolKind::TypeAlias => Symbol::TypeAlias(self.symbols.next_type_alias(module_id)),
                SymbolKind::TypeParameter => {
                    Symbol::TypeParameter(self.symbols.next_type_parameter(module_id))
                }
                SymbolKind::Global => Symbol::Global(self.symbols.next_global(module_id)),
                SymbolKind::DeclaredLocal => Symbol::DeclaredLocal(self.symbols.next_local()),
                SymbolKind::PatternBindLocal => {
                    Symbol::PatternBindLocal(self.symbols.next_pattern_bind())
                }
                SymbolKind::ParamLocal => Symbol::ParamLocal(self.symbols.next_param()),
                SymbolKind::Property => Symbol::Property(self.symbols.next_property(module_id)),
                SymbolKind::Synthesized => {
                    Symbol::Synthesized(self.symbols.next_synthesized(module_id))
                }
                SymbolKind::InstanceMethod => {
                    Symbol::InstanceMethod(self.symbols.next_instance_method(module_id))
                }
                SymbolKind::Initializer => {
                    Symbol::Initializer(self.symbols.next_initializer(module_id))
                }
                SymbolKind::MethodRequirement => {
                    Symbol::MethodRequirement(self.symbols.next_method_requirement(module_id))
                }
                SymbolKind::StaticMethod => {
                    Symbol::StaticMethod(self.symbols.next_static_method(module_id))
                }
                SymbolKind::Variant => Symbol::Variant(self.symbols.next_variant(module_id)),
                SymbolKind::Protocol => Symbol::Protocol(self.symbols.next_protocol(module_id)),
                SymbolKind::AssociatedType => {
                    Symbol::AssociatedType(self.symbols.next_associated_type(module_id))
                }
            }
        };

        self.phase.symbols_to_node.insert(symbol, node_id);
        self.phase.symbol_names.insert(symbol, name_str.clone());
        self.phase.declarations.insert(
            symbol,
            DeclarationRecord {
                file: node_id.0,
                owner: self.nominal_stack.last().map(|(owner, _)| *owner),
                role: kind,
                declared: Visibility::Private,
                effective: Visibility::Private,
            },
        );

        let _ = span;

        Name::Resolved(symbol, name_str)
    }

    /// Mark a symbol as public (visible outside its file)
    pub(super) fn mark_public(&mut self, symbol: Symbol) {
        if let Some(record) = self.phase.declarations.get_mut(&symbol) {
            record.effective = Visibility::Public;
        }
    }

    /// Record the visibility the author wrote on a declaration
    /// (ADR 0042). Effective visibility is concluded separately.
    pub(super) fn record_declared_visibility(&mut self, symbol: Symbol, visibility: Visibility) {
        if let Some(record) = self.phase.declarations.get_mut(&symbol) {
            record.declared = visibility;
        }
    }

    /// Declare a pattern's binders into the current scope. At module
    /// scope, simple binds become Globals; everywhere else they take
    /// `bind_type`.
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn declare_pattern(&mut self, pattern: &mut Pattern, bind_type: SymbolKind) {
        let Pattern { kind, span, .. } = pattern;
        let span = *span;

        match kind {
            PatternKind::Bind(name @ Name::Raw(_)) => {
                *name = if self.at_module_scope() {
                    self.declare(name, SymbolKind::Global, pattern.id, span)
                } else {
                    self.declare(name, bind_type, pattern.id, span)
                }
            }
            PatternKind::Or(patterns) => {
                // Declare the binds in the first pattern, the following patterns will get resolved from those
                self.declare_pattern(&mut patterns[0], bind_type);
            }
            PatternKind::Bind(..) => {}
            PatternKind::Variant { fields, .. } => {
                for field in fields.iter_mut() {
                    self.declare_pattern(field, SymbolKind::PatternBindLocal);
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    match &mut field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            *name = self.declare(
                                name,
                                SymbolKind::PatternBindLocal,
                                pattern.id,
                                field.span,
                            );
                        }
                        RecordFieldPatternKind::Equals {
                            name,
                            name_span,
                            value,
                        } => {
                            *name = self.declare(
                                name,
                                SymbolKind::PatternBindLocal,
                                pattern.id,
                                *name_span,
                            );
                            self.declare_pattern(value, SymbolKind::PatternBindLocal);
                        }
                        RecordFieldPatternKind::Rest => (),
                    }
                }
            }
            PatternKind::Struct { fields, .. } => {
                for field in fields {
                    if let Node::Pattern(pattern) = field {
                        self.declare_pattern(pattern, SymbolKind::PatternBindLocal);
                    }
                }
            }
            PatternKind::Tuple(values) => {
                for value in values {
                    self.declare_pattern(value, bind_type);
                }
            }
            PatternKind::Wildcard => (),
            PatternKind::LiteralFalse
            | PatternKind::LiteralTrue
            | PatternKind::LiteralInt(..)
            | PatternKind::LiteralFloat(..)
            | PatternKind::LiteralCharacter(..)
            | PatternKind::LiteralString(..) => (),
        }
    }

    /// [`Self::declare_pattern`] without the scope insertion: a local
    /// `let`'s binders resolve to fresh symbols here, at their point of
    /// declaration, and stage into `out` — they become visible only when
    /// the decl exits. Already-resolved binds (hoisted func-valued lets)
    /// stage their existing symbol. Or-patterns can't appear on a let lhs
    /// (the parser desugars them to a single-arm match).
    fn mint_pattern(
        &mut self,
        pattern: &mut Pattern,
        bind_type: SymbolKind,
        out: &mut Vec<(String, Symbol)>,
    ) {
        let Pattern { kind, span, .. } = pattern;
        let span = *span;

        match kind {
            PatternKind::Bind(name) => {
                if matches!(name, Name::Raw(_)) {
                    *name = self.mint(name, bind_type, pattern.id, span);
                }
                if let Ok(symbol) = name.symbol() {
                    out.push((name.name_str(), symbol));
                }
            }
            PatternKind::Or(patterns) => {
                for pattern in patterns {
                    self.mint_pattern(pattern, bind_type, out);
                }
            }
            PatternKind::Variant { fields, .. } => {
                for field in fields.iter_mut() {
                    self.mint_pattern(field, SymbolKind::PatternBindLocal, out);
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    match &mut field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            if matches!(name, Name::Raw(_)) {
                                *name = self.mint(
                                    name,
                                    SymbolKind::PatternBindLocal,
                                    pattern.id,
                                    field.span,
                                );
                            }
                            if let Ok(symbol) = name.symbol() {
                                out.push((name.name_str(), symbol));
                            }
                        }
                        RecordFieldPatternKind::Equals {
                            name,
                            name_span,
                            value,
                        } => {
                            if matches!(name, Name::Raw(_)) {
                                *name = self.mint(
                                    name,
                                    SymbolKind::PatternBindLocal,
                                    pattern.id,
                                    *name_span,
                                );
                            }
                            if let Ok(symbol) = name.symbol() {
                                out.push((name.name_str(), symbol));
                            }
                            self.mint_pattern(value, SymbolKind::PatternBindLocal, out);
                        }
                        RecordFieldPatternKind::Rest => (),
                    }
                }
            }
            PatternKind::Tuple(values) => {
                for value in values {
                    self.mint_pattern(value, bind_type, out);
                }
            }
            PatternKind::Struct { fields, .. } => {
                for field in fields {
                    if let Node::Pattern(pattern) = field {
                        self.mint_pattern(pattern, SymbolKind::PatternBindLocal, out);
                    }
                }
            }
            PatternKind::Wildcard
            | PatternKind::LiteralFalse
            | PatternKind::LiteralTrue
            | PatternKind::LiteralInt(..)
            | PatternKind::LiteralFloat(..)
            | PatternKind::LiteralCharacter(..)
            | PatternKind::LiteralString(..) => (),
        }
    }

    /// Create a scope for `node_id` under the current scope and enter it.
    fn push_scope(&mut self, node_id: NodeID) {
        let parent_id = self.current_scope_id;
        let depth = self.current_scope().map(|s| s.depth + 1).unwrap_or(1);
        self.scopes
            .insert(node_id, Scope::new(node_id, parent_id, depth));
        self.enter_scope(node_id);
    }

    fn enter_pattern(&mut self, pattern: &mut Pattern) {
        if self.for_pattern_roots.last().copied() == Some(pattern.id) {
            self.declare_pattern(pattern, SymbolKind::PatternBindLocal);
        }

        match &mut pattern.kind {
            PatternKind::Bind(name @ Name::Raw(_)) => {
                *name = self.lookup(name).unwrap_or_else(|| {
                    self.diagnostic(pattern.id, NameResolverError::Unresolved(name.clone()));
                    name.clone()
                })
            }
            PatternKind::Bind(_) => {} // Already resolved in declaration pass, keep existing symbol
            PatternKind::Or(subpatterns) => {
                for pattern in subpatterns {
                    self.enter_pattern(pattern);
                }
            }
            PatternKind::Variant {
                enum_name: Some(enum_name),
                fields,
                ..
            } => {
                // enum_name doesn't have a dedicated span; use pattern span
                let Some(resolved) = self.lookup_nominal_path(enum_name) else {
                    self.diagnostic(
                        pattern.id,
                        NameResolverError::UndefinedName(enum_name.name_str()),
                    );
                    return;
                };

                *enum_name = resolved;

                for field in fields {
                    self.enter_pattern(field);
                }
            }
            PatternKind::Variant {
                enum_name: None,
                fields,
                ..
            } => {
                for field in fields {
                    self.enter_pattern(field);
                }
            }
            PatternKind::Tuple(patterns) => {
                for pattern in patterns.iter_mut() {
                    self.enter_pattern(pattern);
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    match &mut field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            *name = self.lookup(name).unwrap_or_else(|| {
                                tracing::error!("Lookup failed for {name:?}");
                                name.clone()
                            });
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            *name = self.lookup(name).unwrap_or_else(|| {
                                tracing::error!("Lookup failed for {name:?}");
                                name.clone()
                            });
                            self.enter_pattern(value);
                        }
                        RecordFieldPatternKind::Rest => (),
                    }
                }
            }
            PatternKind::LiteralInt(..)
            | PatternKind::LiteralFloat(..)
            | PatternKind::LiteralCharacter(..)
            | PatternKind::LiteralString(..)
            | PatternKind::LiteralTrue
            | PatternKind::LiteralFalse => (),
            PatternKind::Wildcard => (),
            PatternKind::Struct {
                struct_name,
                fields,
                ..
            } => {
                if let Some(name) = struct_name {
                    match self.lookup_nominal_path(name) {
                        Some(resolved) => *name = resolved,
                        None => {
                            self.diagnostic(
                                pattern.id,
                                NameResolverError::UndefinedName(name.name_str()),
                            );
                        }
                    }
                }
                for field in fields {
                    if let Node::Pattern(pattern) = field {
                        self.enter_pattern(pattern);
                    }
                }
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Type lookups
    ///////////////////////////////////////////////////////////////////////////
    fn enter_type_annotation(&mut self, ty: &mut TypeAnnotation) {
        if let TypeAnnotationKind::Nominal { name, .. } = &mut ty.kind {
            if let Some(resolved_name) = self.lookup(name) {
                *name = resolved_name
            } else {
                self.diagnostic(ty.id, NameResolverError::UndefinedName(name.name_str()));
            }
        }

        if let TypeAnnotationKind::SelfType(name) = &mut ty.kind {
            if let Some(resolved_name) = self.lookup(name) {
                *name = resolved_name
            } else {
                self.diagnostic(ty.id, NameResolverError::UndefinedName(name.name_str()));
            }
        }

        if let TypeAnnotationKind::Func { effects, .. } = &mut ty.kind {
            for name in effects.names.iter_mut() {
                let Some(resolved_name) = self.lookup_effect(name) else {
                    self.diagnostic(ty.id, NameResolverError::Unresolved(name.clone()));
                    continue;
                };
                *name = resolved_name;
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block expr decls
    ///////////////////////////////////////////////////////////////////////////
    // Every block gets a fresh scope on entry: locals insert here
    // sequentially, at their point of declaration, so a binding is
    // visible from just after its initializer to the end of the block
    // (docs/sequential-scoping-plan.md). Blocks synthesized between the
    // passes (e.g. generated inits) need no special case — the scope is
    // always built here.
    fn enter_block(&mut self, block: &mut Block) {
        self.push_scope(block.id);

        for arg in &mut block.args {
            arg.name = self.declare(&arg.name, SymbolKind::ParamLocal, arg.id, arg.name_span);
        }

        // Func-valued let binders are items (Rust's fn-in-block): hoisted
        // block-wide so local funcs can be mutually recursive and
        // self-recursive regardless of declaration order.
        for node in &mut block.body {
            if let Node::Decl(Decl {
                kind:
                    DeclKind::Let {
                        lhs,
                        rhs:
                            Some(Expr {
                                kind: ExprKind::Func(func),
                                ..
                            }),
                        ..
                    },
                ..
            }) = node
                && let PatternKind::Bind(name @ Name::Raw(_)) = &mut lhs.kind
            {
                *name = self.declare(name, SymbolKind::DeclaredLocal, lhs.id, lhs.span);
                // A lowered local `func` declaration joins the block
                // scope's overload set (ADR 0041).
                if func.origin == crate::node_kinds::func::FuncOrigin::Decl
                    && let Ok(symbol) = name.symbol()
                {
                    self.register_callable(symbol, &name.name_str(), &func.params, lhs.id);
                }
            }
        }
    }

    fn exit_block(&mut self, block: &mut Block) {
        self.exit_scope(block.id);
    }

    fn enter_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::For {
            pattern,
            hidden_source,
            hidden_iter,
            source_mode,
            iterable,
            ..
        } = &mut stmt.kind
        {
            // The whole loop is a scope: the hidden source/iterator bindings
            // and the loop binder live in it and die with it.
            self.push_scope(stmt.id);
            self.for_pattern_roots.push(pattern.id);
            *hidden_source =
                self.mint(hidden_source, SymbolKind::DeclaredLocal, stmt.id, stmt.span);
            *hidden_iter = self.mint(hidden_iter, SymbolKind::DeclaredLocal, stmt.id, stmt.span);
            // `for x in mut xs` restores its source at loop end — the
            // source is mutated exactly as an assignment target is.
            if matches!(source_mode, Some(crate::node_kinds::call_arg::ArgMode::Mut)) {
                self.track_assignment_mutation(iterable);
            }
        }

        on!(&mut stmt.kind, StmtKind::Handling { effect_name, .. }, {
            let Some(Name::Resolved(effect_sym, _)) = self.lookup_effect(effect_name) else {
                self.diagnostic(stmt.id, NameResolverError::Unresolved(effect_name.clone()));
                return;
            };

            *effect_name = Name::Resolved(effect_sym, effect_name.name_str());

            if let Some(scope) = self.current_scope()
                && let Some((_, id)) = scope.handlers.get(&effect_sym)
            {
                self.warning(
                    *id,
                    NameResolverError::ShadowedEffectHandler(effect_name.name_str()),
                );
            }

            let handler_sym =
                Symbol::Synthesized(self.symbols.next_synthesized(self.current_module_id));
            self.phase.symbols_to_node.insert(handler_sym, stmt.id);
            self.phase.symbol_names.insert(
                handler_sym,
                format!("handler('{}')", effect_name.name_str()),
            );

            let Some(scope) = self.current_scope_mut() else {
                self.diagnostic(
                    stmt.id,
                    NameResolverError::UndefinedName("no scope".to_string()),
                );

                return;
            };

            scope.handlers.insert(effect_sym, (handler_sym, stmt.id));
        });

        if let StmtKind::Assignment(box lhs, ..) = &mut stmt.kind {
            self.track_assignment_mutation(lhs);
        }
    }

    fn exit_stmt(&mut self, stmt: &mut Stmt) {
        if matches!(stmt.kind, StmtKind::For { .. }) {
            self.for_pattern_roots.pop();
            self.exit_scope(stmt.id);
        }
    }

    fn track_assignment_mutation(&mut self, expr: &mut Expr) {
        let Some((name, id, _span)) = Self::assignment_base_name(expr) else {
            return;
        };
        let Some(resolved) = self.lookup(name) else {
            self.diagnostic(id, NameResolverError::UndefinedName(name.name_str()));
            return;
        };

        self.phase
            .mutated_symbols
            .insert(resolved.symbol().unwrap_or_else(|_| unreachable!("")));

        *name = resolved;
    }

    fn assignment_base_name(expr: &mut Expr) -> Option<(&mut Name, NodeID, Span)> {
        match &mut expr.kind {
            ExprKind::Variable(name) => Some((name, expr.id, expr.span)),
            ExprKind::Member(Some(inner), ..) => Self::assignment_base_name(inner),
            _ => None,
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Locals scoping
    ///////////////////////////////////////////////////////////////////////////

    // An arm's binders are visible throughout the arm (pattern
    // alternatives, guard, body) — declared on entry, unlike a `let`'s.
    fn enter_match_arm(&mut self, arm: &mut MatchArm) {
        self.push_scope(arm.id);
        self.declare_pattern(&mut arm.pattern, SymbolKind::PatternBindLocal);
    }

    fn exit_match_arm(&mut self, arm: &mut MatchArm) {
        self.exit_scope(arm.id);
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        on!(&mut expr.kind, ExprKind::InlineIR(instr), {
            for bind in &mut instr.binds {
                self.enter_expr(bind);
            }

            match &mut instr.kind {
                InlineIRInstructionKind::Cmp { ty, .. }
                | InlineIRInstructionKind::Add { ty, .. }
                | InlineIRInstructionKind::Sub { ty, .. }
                | InlineIRInstructionKind::Mul { ty, .. }
                | InlineIRInstructionKind::Div { ty, .. }
                | InlineIRInstructionKind::And { ty, .. }
                | InlineIRInstructionKind::Or { ty, .. }
                | InlineIRInstructionKind::Xor { ty, .. }
                | InlineIRInstructionKind::Shl { ty, .. }
                | InlineIRInstructionKind::Shr { ty, .. }
                | InlineIRInstructionKind::Not { ty, .. }
                | InlineIRInstructionKind::Alloc { ty, .. }
                | InlineIRInstructionKind::Load { ty, .. }
                | InlineIRInstructionKind::Take { ty, .. }
                | InlineIRInstructionKind::Store { ty, .. }
                | InlineIRInstructionKind::Copy { ty, .. }
                | InlineIRInstructionKind::Swap { ty, .. }
                | InlineIRInstructionKind::Retain { ty, .. }
                | InlineIRInstructionKind::Gep { ty, .. }
                | InlineIRInstructionKind::InlineGet { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Io { .. }
                | InlineIRInstructionKind::Trunc { .. }
                | InlineIRInstructionKind::IsUnique { .. }
                | InlineIRInstructionKind::IntToFloat { .. }
                | InlineIRInstructionKind::ByteToInt { .. }
                | InlineIRInstructionKind::IntToByte { .. }
                | InlineIRInstructionKind::Free { .. } => (),
            }
        });

        // Overloaded callees select by written labels before the generic
        // variable resolution below reaches them (ADR 0041).
        on!(&mut expr.kind, ExprKind::Call { callee, args, .. }, {
            if let ExprKind::Variable(name) = &mut callee.kind
                && name.symbol().is_err()
                && let Some(set) = self.visible_overloads(&name.name_str())
            {
                self.select_overload(name, expr.id, &set, args);
                self.overload_selected.insert(callee.id);
            }
        });

        on!(&mut expr.kind, ExprKind::Variable(name), {
            // A call callee selected from an overload set stays selected.
            if self.overload_selected.contains(&expr.id) {
                return;
            }
            // A bare reference resolves only when the set has one callable.
            if let Some(set) = self.visible_overloads(&name.name_str()) {
                let candidates = set
                    .iter()
                    .filter_map(|symbol| {
                        Some(
                            crate::types::callables::CallableName {
                                base: name.name_str(),
                                labels: self.phase.callable_labels.get(symbol)?.clone(),
                            }
                            .to_string(),
                        )
                    })
                    .collect();
                self.diagnostic(
                    expr.id,
                    NameResolverError::AmbiguousCallable {
                        name: name.name_str(),
                        candidates,
                    },
                );
            }
            let Some(resolved_name) = self.lookup(name) else {
                self.diagnostic(expr.id, NameResolverError::UndefinedName(name.name_str()));
                return;
            };

            *name = resolved_name;

            if matches!(
                name,
                Name::Resolved(
                    Symbol::Struct(..)
                        | Symbol::Enum(..)
                        | Symbol::TypeAlias(..)
                        | Symbol::Protocol(..),
                    _
                )
            ) {
                expr.kind = ExprKind::Constructor(name.clone(), vec![]);
            }
        });

        // A parser-minted specialized reference (`Opt<Int>.`,
        // `Res.A<Bool>.`) arrives with a raw, possibly-dotted name;
        // resolve it through the nominal path (its generic args resolve
        // as ordinary driven children).
        on!(&mut expr.kind, ExprKind::Constructor(name, _), {
            if name.symbol().is_err() {
                let Some(resolved_name) = self.lookup_nominal_path(name) else {
                    self.diagnostic(expr.id, NameResolverError::UndefinedName(name.name_str()));
                    return;
                };
                *name = resolved_name;
            }
        });

        on!(&mut expr.kind, ExprKind::CallEffect { effect_name, .. }, {
            let Some(resolved_name) = self.lookup_effect(effect_name) else {
                self.diagnostic(
                    expr.id,
                    NameResolverError::UndefinedName(effect_name.name_str()),
                );
                return;
            };

            *effect_name = resolved_name;
        });
    }

    fn exit_expr(&mut self, expr: &mut Expr) {
        // A member access whose receiver is a type name and whose label
        // names one of its nested types is itself a type name: collapse
        // to a Constructor so `Res.A.success` types exactly like
        // `A.success`. Post-order, so qualified chains collapse
        // inner-first (`Res.A.B` becomes `Constructor(B)`). The
        // receiver's explicit head args ride along — they stay the
        // leading (captured) params of the nested type.
        let ExprKind::Member(Some(receiver), label, _) = &expr.kind else {
            return;
        };
        let ExprKind::Constructor(name, head_args) = &receiver.kind else {
            return;
        };
        let Ok(symbol) = name.symbol() else {
            return;
        };
        let Some(&child) = self
            .phase
            .child_types
            .get(&symbol)
            .and_then(|children| children.get(label))
        else {
            return;
        };
        if matches!(child, Symbol::Struct(_) | Symbol::Enum(_)) {
            let text = format!("{}.{}", name.name_str(), label);
            // The collapsed constructor gains a path segment; keep the
            // per-segment arg lists parallel (empty means no explicit
            // args anywhere).
            let mut segments = head_args.clone();
            if !segments.is_empty() {
                segments.resize(name.name_str().split('.').count(), vec![]);
                segments.push(vec![]);
            }
            expr.kind = ExprKind::Constructor(Name::Resolved(child, text), segments);
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Func scoping
    ///////////////////////////////////////////////////////////////////////////

    fn enter_func(&mut self, func: &mut Func) {
        // Resolve the func's name before entering its scope: a func decl
        // desugars to a func-valued let, so the name is the let binder —
        // declared at module scope (pass 1), hoisted at block entry, or a
        // method name (pass 1). Anonymous funcs get a synthesized symbol.
        let func_symbol = match func.name.symbol() {
            Ok(symbol) => symbol,
            Err(_) => {
                let resolved = self.lookup(&func.name).and_then(|name| name.symbol().ok());
                resolved.unwrap_or_else(|| {
                    let is_synth = func.name.name_str().starts_with("#fn_");
                    let fallback = if is_synth {
                        SymbolKind::Synthesized
                    } else {
                        SymbolKind::Global
                    };
                    self.declare(&func.name, fallback, func.id, func.name_span)
                        .symbol()
                        .unwrap_or_else(|_| unreachable!("declare always resolves"))
                })
            }
        };
        func.name = Name::Resolved(func_symbol, func.name.name_str());

        for capture in &mut func.captures {
            let Some(resolved_name) = self.lookup(&capture.name) else {
                self.diagnostic(func.id, NameResolverError::Unresolved(capture.name.clone()));
                continue;
            };
            capture.name = resolved_name;
        }

        self.push_scope(func.id);

        for generic in &mut func.generics {
            generic.name = self.declare(
                &generic.name,
                SymbolKind::TypeParameter,
                generic.id,
                generic.name_span,
            );
        }

        for param in &mut func.params {
            param.name = self.declare(
                &param.name,
                SymbolKind::ParamLocal,
                param.id,
                param.name_span,
            );
        }

        for name in func.effects.names.iter_mut() {
            let Some(resolved_name) = self.lookup_effect(name) else {
                self.diagnostic(func.id, NameResolverError::Unresolved(name.clone()));
                continue;
            };
            *name = resolved_name;
        }
    }

    fn exit_func(&mut self, func: &mut Func) {
        self.exit_scope(func.id);
    }

    fn enter_func_signature(&mut self, func: &mut FuncSignature) {
        self.enter_scope(func.id);
    }

    fn exit_func_signature(&mut self, func: &mut FuncSignature) {
        self.exit_scope(func.id);
    }

    ///////////////////////////////////////////////////////////////////////////
    // Nominal scoping
    ///////////////////////////////////////////////////////////////////////////
    fn enter_decl(&mut self, decl: &mut Decl) {
        on!(
            &decl.kind,
            DeclKind::Enum { name, .. }
                | DeclKind::Struct { name, .. }
                | DeclKind::Protocol { name, .. },
            {
                if name.symbol().is_err() {
                    self.diagnostic(decl.id, NameResolverError::Unresolved(name.clone()));
                    return;
                }

                self.enter_scope(decl.id);
            }
        );

        on!(&decl.kind, DeclKind::Extend { head, .. }, {
            if head.symbol().is_err() {
                return;
            }
            self.enter_scope(decl.id);
        });

        on!(&mut decl.kind, DeclKind::Init { params, .. }, {
            self.enter_scope(decl.id);

            for param in params {
                param.name = self.declare(
                    &param.name,
                    SymbolKind::ParamLocal,
                    param.id,
                    param.name_span,
                );
            }
        });

        on!(&decl.kind, DeclKind::Effect { .. }, {
            self.enter_scope(decl.id);
        });

        on!(&decl.kind, DeclKind::EnumVariant { .. }, {
            self.enter_scope(decl.id);
        });

        on!(&mut decl.kind, DeclKind::Let { lhs, rhs, .. }, {
            // A lowered `func` declaration IS its binder: bind the func's
            // own name to the binder's symbol before the body resolves, so
            // an overloaded base name never re-resolves to a sibling
            // declaration (ADR 0041).
            if let PatternKind::Bind(binder) = &lhs.kind
                && let Ok(symbol) = binder.symbol()
                && let Some(Expr {
                    kind: ExprKind::Func(func),
                    ..
                }) = rhs
                && func.origin == crate::node_kinds::func::FuncOrigin::Decl
                && func.name.symbol().is_err()
            {
                func.name = Name::Resolved(symbol, func.name.name_str());
            }

            // Local binders resolve to fresh symbols here, at their point
            // of declaration, but stay invisible until the decl exits
            // (rule 1 — the rhs sees the outer binding). Func-valued let
            // binders were already hoisted at block entry and arrive
            // resolved; re-staging them re-inserts the same symbol.
            // Module-scope lets were declared in pass 1.
            if !self.at_module_scope() {
                let mut staged = vec![];
                self.mint_pattern(lhs, SymbolKind::DeclaredLocal, &mut staged);
                self.pending_locals.push(staged);
            }
        });
    }

    fn exit_decl(&mut self, decl: &mut Decl) {
        on!(
            decl.kind,
            DeclKind::Enum { .. }
                | DeclKind::Struct { .. }
                | DeclKind::Protocol { .. }
                | DeclKind::Extend { .. }
                | DeclKind::Init { .. }
                | DeclKind::Effect { .. }
                | DeclKind::EnumVariant { .. },
            {
                self.exit_scope(decl.id);
            }
        );

        on!(&decl.kind, DeclKind::Let { .. }, {
            // The initializer is resolved; its binders become visible for
            // the rest of the enclosing block. Insertion may overwrite a
            // same-named earlier binding — sound, because every earlier
            // use already resolved (sequential shadowing).
            if !self.at_module_scope()
                && let Some(staged) = self.pending_locals.pop()
                && let Some(scope) = self.current_scope_mut()
            {
                for (name, symbol) in staged {
                    scope.types.insert(name, symbol);
                }
            }
        })
    }
}

fn module_path_keys(path: &str) -> Vec<String> {
    let mut keys = vec![path.to_string()];
    let path_buf = Path::new(path);
    if let Ok(canonical) = path_buf.canonicalize() {
        keys.push(canonical.to_string_lossy().to_string());
    }
    if path_buf.extension().and_then(|ext| ext.to_str()) == Some("tlk")
        && let Some(stemless) = path.strip_suffix(".tlk")
    {
        keys.push(stemless.to_string());
    }
    keys.sort();
    keys.dedup();
    keys
}

/// Returns true if the symbol represents a type (as opposed to a value)
fn is_type_symbol(symbol: &Symbol) -> bool {
    matches!(
        symbol,
        Symbol::Struct(_) | Symbol::Enum(_) | Symbol::Protocol(_) | Symbol::TypeAlias(_)
    )
}

/// Check if a file path refers to a core source file.
fn is_core_source_path(path: &str) -> bool {
    let file_name = std::path::Path::new(path)
        .file_name()
        .and_then(|n| n.to_str());
    let Some(name) = file_name else {
        return false;
    };
    crate::compiling::core::CORE_SOURCE_NAMES.contains(&name)
}
