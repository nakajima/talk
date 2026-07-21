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
        symbol::{Symbol, Symbols},
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
    on, some,
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
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ResolvedNames {
    pub scopes: FxHashMap<NodeID, Scope>,
    pub symbol_names: FxHashMap<Symbol, String>,
    pub symbols_to_node: FxHashMap<Symbol, NodeID>,
    pub child_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub mutated_symbols: IndexSet<Symbol>,
    /// Tracks which symbols are public (visible outside their file)
    pub public_symbols: FxHashSet<Symbol>,
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
                if self.public_symbols.contains(&symbol) && !matches!(symbol, Symbol::Builtin(..)) {
                    res.insert(name.clone(), symbol);
                }
            }
            for (name, &symbol) in &scope.values {
                if self.public_symbols.contains(&symbol) && !matches!(symbol, Symbol::Builtin(..)) {
                    res.insert(name.clone(), symbol);
                }
            }
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
            for (name, &symbol) in &core_module.exports {
                if is_type_symbol(&symbol) {
                    scope.types.insert(name.clone(), symbol);
                } else {
                    scope.values.insert(name.clone(), symbol);
                }
            }
        }

        if Path::new(path).file_name().and_then(|name| name.to_str()) == Some("package.tlk")
            && let Some(package_module) = self.modules.get_module_by_name("Package")
        {
            for (name, &symbol) in &package_module.exports {
                if is_type_symbol(&symbol) {
                    scope.types.insert(name.clone(), symbol);
                } else {
                    scope.values.insert(name.clone(), symbol);
                }
            }
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

                    let target_symbols: Vec<(String, Symbol, bool)> = match &import.path {
                        ImportPath::Package(pkg_name) => {
                            let Some(module) = self.modules.get_module_by_name(pkg_name) else {
                                self.diagnostic(
                                    decl_id,
                                    NameResolverError::ModuleNotFound(pkg_name.clone()),
                                );
                                continue;
                            };
                            imported_module = true;
                            module
                                .exports
                                .iter()
                                .map(|(name, &symbol)| {
                                    (name.clone(), symbol, is_type_symbol(&symbol))
                                })
                                .collect()
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
                                core.exports
                                    .iter()
                                    .map(|(name, &symbol)| {
                                        (name.clone(), symbol, is_type_symbol(&symbol))
                                    })
                                    .collect()
                            } else {
                                let Some(target_scope) = self.scopes.get(&target_scope_id) else {
                                    continue;
                                };
                                let mut symbols = Vec::new();
                                for (name, &symbol) in &target_scope.values {
                                    symbols.push((name.clone(), symbol, is_type_symbol(&symbol)));
                                }
                                for (name, &symbol) in &target_scope.types {
                                    symbols.push((name.clone(), symbol, is_type_symbol(&symbol)));
                                }
                                symbols
                            }
                        }
                    };

                    // Import the requested symbols
                    match &import.symbols {
                        ImportedSymbols::All => {
                            // Import all public non-builtin symbols
                            let Some(source_scope) = self.scopes.get_mut(&source_scope_id) else {
                                continue;
                            };
                            for (name, symbol, is_type) in target_symbols {
                                // Skip builtins and private symbols
                                // (core exports are public by definition)
                                if matches!(symbol, Symbol::Builtin(..)) {
                                    continue;
                                }
                                if !imported_module && !self.phase.public_symbols.contains(&symbol)
                                {
                                    continue;
                                }
                                if is_type {
                                    source_scope.types.insert(name, symbol);
                                } else {
                                    source_scope.values.insert(name, symbol);
                                }
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
                                    Some((_, symbol, is_type)) => {
                                        // Check if the symbol is public
                                        // (core exports are public by definition)
                                        if !imported_module
                                            && !self.phase.public_symbols.contains(symbol)
                                        {
                                            self.diagnostic(
                                                decl_id,
                                                NameResolverError::SymbolNotPublic(
                                                    name_to_find.clone(),
                                                ),
                                            );
                                            continue;
                                        }
                                        let Some(source_scope) =
                                            self.scopes.get_mut(&source_scope_id)
                                        else {
                                            continue;
                                        };
                                        if *is_type {
                                            source_scope.types.insert(local_name.clone(), *symbol);
                                        } else {
                                            source_scope.values.insert(local_name.clone(), *symbol);
                                        }
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

    fn lookup_qualified(&mut self, raw: &str, scope_id: NodeID) -> Option<Symbol> {
        let (module_path, symbol_name) = raw.rsplit_once("::")?;
        let target_symbols = if LocalModulePaths::is_local(module_path) {
            let source_file = scope_id.0;
            let source_path = self.file_path_by_id.get(&source_file)?.clone();
            let Some(resolved) = self.local_modules.resolve(&source_path, module_path) else {
                self.diagnostic(
                    scope_id,
                    NameResolverError::ModuleNotFound(module_path.to_string()),
                );
                return None;
            };
            let target_path = resolved.to_string_lossy().to_string();
            let Some(target_file_id) = module_path_keys(&target_path)
                .into_iter()
                .find_map(|key| self.path_to_file_id.get(&key).copied())
            else {
                self.diagnostic(
                    scope_id,
                    NameResolverError::ModuleNotFound(module_path.to_string()),
                );
                return None;
            };
            let target_scope_id = NodeID(target_file_id, 0);
            if let Some(core) = is_core_source_path(&target_path)
                .then(|| self.modules.get_module_by_name("Core"))
                .flatten()
            {
                core.exports
                    .iter()
                    .map(|(name, &symbol)| (name.clone(), symbol, true))
                    .collect_vec()
            } else {
                let target_scope = self.scopes.get(&target_scope_id)?;
                let mut symbols = Vec::new();
                for (name, &symbol) in &target_scope.values {
                    symbols.push((
                        name.clone(),
                        symbol,
                        self.phase.public_symbols.contains(&symbol),
                    ));
                }
                for (name, &symbol) in &target_scope.types {
                    symbols.push((
                        name.clone(),
                        symbol,
                        self.phase.public_symbols.contains(&symbol),
                    ));
                }
                symbols
            }
        } else {
            let Some(module) = self.modules.get_module_by_name(module_path) else {
                self.diagnostic(
                    scope_id,
                    NameResolverError::ModuleNotFound(module_path.to_string()),
                );
                return None;
            };
            module
                .exports
                .iter()
                .map(|(name, &symbol)| (name.clone(), symbol, true))
                .collect_vec()
        };

        let found = target_symbols
            .iter()
            .find(|(name, _, _)| name == symbol_name);
        if let Some((_, _, is_public)) = found
            && !*is_public
        {
            self.diagnostic(
                scope_id,
                NameResolverError::SymbolNotPublic(symbol_name.to_string()),
            );
            return None;
        }
        let found = found.map(|(_, symbol, _)| *symbol);
        if found.is_none() {
            self.diagnostic(
                scope_id,
                NameResolverError::SymbolNotFoundInModule(symbol_name.to_string()),
            );
        }
        found
    }

    pub(super) fn lookup(&mut self, name: &Name) -> Option<Name> {
        let symbol = self.lookup_in_scope(
            name,
            self.current_scope_id
                .unwrap_or_else(|| unreachable!("no scope to declare in. name: {name:?}")),
        )?;

        Some(Name::Resolved(symbol, name.name_str()))
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
        kind: Symbol,
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
                Symbol::DeclaredLocal(..) | Symbol::PatternBindLocal(..)
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
            Symbol::Struct(..)
                | Symbol::Enum(..)
                | Symbol::Protocol(..)
                | Symbol::Effect(..)
                | Symbol::TypeAlias(..)
        ) && let Some(&existing) = self
            .scopes
            .get(&scope_id)
            .and_then(|s| s.types.get(&name_str))
            && std::mem::discriminant(&existing) == std::mem::discriminant(&kind)
        {
            return Name::Resolved(existing, name_str);
        }

        // Check for predeclared Globals at module scope
        // This handles public Let bindings that were predeclared for import resolution
        // Only reuse if the existing Global is public (i.e., was predeclared)
        // Non-public Globals should allow shadowing (create new symbol)
        // Note: Don't record span here - it was already recorded during predeclaration
        if at_module_scope
            && matches!(kind, Symbol::Global(..))
            && let Some(&existing) = self
                .scopes
                .get(&scope_id)
                .and_then(|s| s.types.get(&name_str))
            && matches!(existing, Symbol::Global(..))
            && self.phase.public_symbols.contains(&existing)
        {
            return Name::Resolved(existing, name_str);
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

    /// Mint a fresh symbol for `name` (recording its defining node and
    /// name string) without making it visible in any scope. Local `let`
    /// binders go through this at their declaration point and only insert
    /// into scope once their initializer has resolved (rule 1 of
    /// docs/sequential-scoping-plan.md).
    pub(super) fn mint(&mut self, name: &Name, kind: Symbol, node_id: NodeID, span: Span) -> Name {
        let name_str = name.name_str();
        let module_id = self.current_module_id;
        let well_known_core_symbol = if self.at_module_scope() && module_id == ModuleId::Core {
            match kind {
                Symbol::Struct(..) => Symbol::well_known_core_struct(&name_str),
                Symbol::Protocol(..) => Symbol::well_known_core_protocol(&name_str),
                _ => None,
            }
        } else {
            None
        };
        let symbol = if let Some(symbol) = well_known_core_symbol {
            symbol
        } else {
            match kind {
                Symbol::Main => Symbol::Main,
                Symbol::Library => Symbol::Library,
                Symbol::Effect(..) => Symbol::Effect(self.symbols.next_effect(module_id)),
                Symbol::Struct(..) => Symbol::Struct(self.symbols.next_struct(module_id)),
                Symbol::Enum(..) => Symbol::Enum(self.symbols.next_enum(module_id)),
                Symbol::TypeAlias(..) => Symbol::TypeAlias(self.symbols.next_type_alias(module_id)),
                Symbol::TypeParameter(..) => {
                    Symbol::TypeParameter(self.symbols.next_type_parameter(module_id))
                }
                Symbol::Global(..) => Symbol::Global(self.symbols.next_global(module_id)),
                Symbol::DeclaredLocal(..) => Symbol::DeclaredLocal(self.symbols.next_local()),
                Symbol::PatternBindLocal(..) => {
                    Symbol::PatternBindLocal(self.symbols.next_pattern_bind())
                }
                Symbol::ParamLocal(..) => Symbol::ParamLocal(self.symbols.next_param()),
                Symbol::Builtin(..) => {
                    unreachable!("should not be generating symbols for builtins")
                }
                Symbol::Property(..) => Symbol::Property(self.symbols.next_property(module_id)),
                Symbol::Synthesized(..) => {
                    Symbol::Synthesized(self.symbols.next_synthesized(module_id))
                }
                Symbol::InstanceMethod(..) => {
                    Symbol::InstanceMethod(self.symbols.next_instance_method(module_id))
                }
                Symbol::Initializer(..) => {
                    Symbol::Initializer(self.symbols.next_initializer(module_id))
                }
                Symbol::MethodRequirement(..) => {
                    Symbol::MethodRequirement(self.symbols.next_method_requirement(module_id))
                }
                Symbol::StaticMethod(..) => {
                    Symbol::StaticMethod(self.symbols.next_static_method(module_id))
                }
                Symbol::Variant(..) => Symbol::Variant(self.symbols.next_variant(module_id)),
                Symbol::Protocol(..) => Symbol::Protocol(self.symbols.next_protocol(module_id)),
                Symbol::AssociatedType(..) => {
                    Symbol::AssociatedType(self.symbols.next_associated_type(module_id))
                }
            }
        };

        self.phase.symbols_to_node.insert(symbol, node_id);
        self.phase.symbol_names.insert(symbol, name_str.clone());

        let _ = span;

        Name::Resolved(symbol, name_str)
    }

    /// Mark a symbol as public (visible outside its file)
    pub(super) fn mark_public(&mut self, symbol: Symbol) {
        self.phase.public_symbols.insert(symbol);
    }

    /// Declare a pattern's binders into the current scope. At module
    /// scope, simple binds become Globals; everywhere else they take
    /// `bind_type`.
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    pub(super) fn declare_pattern(&mut self, pattern: &mut Pattern, bind_type: Symbol) {
        let Pattern { kind, span, .. } = pattern;
        let span = *span;

        match kind {
            PatternKind::Bind(name @ Name::Raw(_)) => {
                *name = if self.at_module_scope() {
                    self.declare(name, some!(Global), pattern.id, span)
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
                    self.declare_pattern(field, some!(PatternBindLocal));
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    match &mut field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            *name =
                                self.declare(name, some!(PatternBindLocal), pattern.id, field.span);
                        }
                        RecordFieldPatternKind::Equals {
                            name,
                            name_span,
                            value,
                        } => {
                            *name =
                                self.declare(name, some!(PatternBindLocal), pattern.id, *name_span);
                            self.declare_pattern(value, some!(PatternBindLocal));
                        }
                        RecordFieldPatternKind::Rest => (),
                    }
                }
            }
            #[allow(clippy::todo)]
            PatternKind::Struct { .. } => {
                todo!()
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
        bind_type: Symbol,
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
                    self.mint_pattern(field, some!(PatternBindLocal), out);
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    match &mut field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            if matches!(name, Name::Raw(_)) {
                                *name = self.mint(
                                    name,
                                    some!(PatternBindLocal),
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
                                    some!(PatternBindLocal),
                                    pattern.id,
                                    *name_span,
                                );
                            }
                            if let Ok(symbol) = name.symbol() {
                                out.push((name.name_str(), symbol));
                            }
                            self.mint_pattern(value, some!(PatternBindLocal), out);
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
            PatternKind::Struct { .. }
            | PatternKind::Wildcard
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
            self.declare_pattern(pattern, some!(PatternBindLocal));
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
                let Some(resolved) = self.lookup(enum_name) else {
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
                struct_name: _,
                fields: _,
                field_names: _,
                rest: _,
            } => (),
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
            arg.name = self.declare(&arg.name, some!(ParamLocal), arg.id, arg.name_span);
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
                                kind: ExprKind::Func(..),
                                ..
                            }),
                        ..
                    },
                ..
            }) = node
                && let PatternKind::Bind(name @ Name::Raw(_)) = &mut lhs.kind
            {
                *name = self.declare(name, some!(DeclaredLocal), lhs.id, lhs.span);
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
            *hidden_source = self.mint(hidden_source, some!(DeclaredLocal), stmt.id, stmt.span);
            *hidden_iter = self.mint(hidden_iter, some!(DeclaredLocal), stmt.id, stmt.span);
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
        self.declare_pattern(&mut arm.pattern, some!(PatternBindLocal));
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
                InlineIRInstructionKind::IoWrite { .. }
                | InlineIRInstructionKind::Trunc { .. }
                | InlineIRInstructionKind::IsUnique { .. }
                | InlineIRInstructionKind::IntToFloat { .. }
                | InlineIRInstructionKind::ByteToInt { .. }
                | InlineIRInstructionKind::Free { .. } => (),
            }
        });

        on!(&mut expr.kind, ExprKind::Variable(name), {
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
                expr.kind = ExprKind::Constructor(name.clone());
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

    fn exit_expr(&mut self, _expr: &mut Expr) {}

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
                        some!(Synthesized)
                    } else {
                        some!(Global)
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
                some!(TypeParameter),
                generic.id,
                generic.name_span,
            );
        }

        for param in &mut func.params {
            param.name = self.declare(&param.name, some!(ParamLocal), param.id, param.name_span);
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
                param.name =
                    self.declare(&param.name, some!(ParamLocal), param.id, param.name_span);
            }
        });

        on!(&decl.kind, DeclKind::Effect { .. }, {
            self.enter_scope(decl.id);
        });

        on!(&decl.kind, DeclKind::EnumVariant { .. }, {
            self.enter_scope(decl.id);
        });

        on!(&mut decl.kind, DeclKind::Let { lhs, .. }, {
            // Local binders resolve to fresh symbols here, at their point
            // of declaration, but stay invisible until the decl exits
            // (rule 1 — the rhs sees the outer binding). Func-valued let
            // binders were already hoisted at block entry and arrive
            // resolved; re-staging them re-inserts the same symbol.
            // Module-scope lets were declared in pass 1.
            if !self.at_module_scope() {
                let mut staged = vec![];
                self.mint_pattern(lhs, some!(DeclaredLocal), &mut staged);
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
