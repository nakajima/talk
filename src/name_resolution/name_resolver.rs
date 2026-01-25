use std::{error::Error, fmt::Display, path::Path, rc::Rc};

use derive_visitor::{DriveMut, VisitorMut};
use generational_arena::Index;
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::{AST, NameResolved, Parsed},
    compiling::{
        driver::Exports,
        module::{ModuleEnvironment, ModuleId},
    },
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    formatter,
    label::Label,
    name::Name,
    name_resolution::{
        builtins,
        decl_declarer::DeclDeclarer,
        scc_graph::SCCGraph,
        symbol::{Symbol, Symbols},
        transforms::{
            lower_funcs_to_lets::LowerFuncsToLets, lower_operators::LowerOperators,
            prepend_self_to_methods::PrependSelfToMethods,
        },
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
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
    types::infer_ty::Level,
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
    PackageImportsNotSupported,
    DuplicateExport(String),
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
            Self::PackageImportsNotSupported => {
                write!(f, "Package imports are not yet supported")
            }
            Self::DuplicateExport(name) => {
                write!(f, "Duplicate export: '{name}'")
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
    pub binder: Option<Symbol>,
    pub level: Level,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Capture {
    pub symbol: Symbol,
    pub parent_binder: Option<Symbol>,
    pub level: Level,
}

impl Scope {
    pub fn new(
        binder: Option<Symbol>,
        level: Level,
        node_id: NodeID,
        parent_id: Option<NodeID>,
        depth: u32,
    ) -> Self {
        Scope {
            node_id,
            parent_id,
            depth,
            level,
            values: Default::default(),
            types: Default::default(),
            handlers: Default::default(),
            binder,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ResolvedNames {
    pub captures: FxHashMap<Symbol, FxHashSet<Capture>>,
    pub captured: FxHashSet<Symbol>,
    pub scopes: FxHashMap<NodeID, Scope>,
    pub symbol_names: FxHashMap<Symbol, String>,
    pub symbols_to_node: FxHashMap<Symbol, NodeID>,
    pub effect_handlers: FxHashMap<NodeID, Symbol>,
    pub handler_symbols: FxHashSet<Symbol>,
    pub scc_graph: SCCGraph,
    pub unbound_nodes: Vec<NodeID>,
    pub child_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub mutated_symbols: IndexSet<Symbol>,
    /// Tracks which symbols are public (visible outside their file)
    pub public_symbols: FxHashSet<Symbol>,
}

impl ResolvedNames {
    pub fn exports(&self) -> Exports {
        let mut res = Exports::default();
        if let Some(scope) = self.scopes.get(&NodeID(FileID(0), 0)) {
            res.extend(scope.types.clone());
            res.extend(scope.values.clone());
        }

        res.into_iter()
            .filter(|e| !matches!(e.1, Symbol::Builtin(..)))
            .collect()
    }
}

pub type ScopeId = Index;

#[derive(Debug, VisitorMut)]
#[visitor(
    Func(enter, exit),
    FuncSignature,
    Stmt(enter, exit),
    MatchArm(enter, exit),
    Decl(enter, exit),
    Expr(enter, exit),
    TypeAnnotation(enter),
    Pattern(enter)
)]
pub struct NameResolver {
    pub symbols: Symbols,
    diagnostics: IndexSet<Diagnostic<NameResolverError>>,

    pub phase: ResolvedNames,

    pub(super) current_module_id: crate::compiling::module::ModuleId,
    pub(super) modules: Rc<ModuleEnvironment>,

    current_func_symbols: Vec<Symbol>,

    // Scope stuff
    pub(super) scopes: FxHashMap<NodeID, Scope>,
    pub(super) current_scope_id: Option<NodeID>,
    pub(super) current_symbol_scope: Vec<Option<Vec<(Symbol, NodeID)>>>,
    pub(super) current_level: Level,

    // For figuring out child types
    pub(super) nominal_stack: Vec<(Symbol, NodeID)>,
}

#[allow(clippy::expect_used)]
impl NameResolver {
    pub fn new(modules: Rc<ModuleEnvironment>, current_module_id: ModuleId) -> Self {
        let mut resolver = Self {
            symbols: Default::default(),
            diagnostics: Default::default(),
            phase: ResolvedNames::default(),
            current_func_symbols: Default::default(),
            current_module_id,
            scopes: Default::default(),
            current_scope_id: None,
            current_symbol_scope: Default::default(),
            current_level: Level::default(),
            nominal_stack: Default::default(),
            modules,
        };

        resolver.init_root_scope();
        resolver
    }

    fn init_root_scope(&mut self) {
        // This is kept for backwards compatibility but doesn't add builtins
        // Builtins are added per-file in resolve()
    }

    /// Create a root scope for a specific file and import builtins into it
    fn init_file_scope(&mut self, file_id: FileID) {
        let scope_id = NodeID(file_id, 0);
        // Always create fresh scope with builtins
        let mut scope = Scope::new(None, self.current_level, scope_id, None, 1);
        builtins::import_builtins(&mut scope);
        self.scopes.insert(scope_id, scope);
        self.current_scope_id = Some(scope_id);
    }

    pub fn resolve(
        &mut self,
        mut asts: Vec<AST<Parsed>>,
    ) -> (Vec<AST<NameResolved>>, ResolvedNames) {
        // Core module uses shared scope (its files depend on each other internally)
        // All other modules use per-file isolated scopes
        let use_shared_scope = self.current_module_id == ModuleId::Core;

        if use_shared_scope {
            // Single shared root scope for Core module
            let root_scope_id = NodeID(FileID(0), 0);
            let mut scope = Scope::new(None, self.current_level, root_scope_id, None, 1);
            builtins::import_builtins(&mut scope);
            self.scopes.insert(root_scope_id, scope);
            self.current_scope_id = Some(root_scope_id);
        } else {
            // Create per-file scopes with builtins for module isolation
            for ast in &asts {
                self.init_file_scope(ast.file_id);
            }
        }

        // First pass: run transforms and declare all types
        for ast in asts.iter_mut() {
            LowerFuncsToLets::run(ast);
            LowerOperators::run(ast);
            PrependSelfToMethods::run(ast);
        }

        if std::env::var("SHOW_TRANSFORM").is_ok() {
            for ast in asts.iter() {
                println!("{:?}", ast.path);
                println!("{}", formatter::format(ast, 80));
            }
        }

        // Helper to get the root scope ID for an AST
        let scope_for_ast = |ast: &AST<Parsed>, use_shared: bool| -> NodeID {
            if use_shared {
                NodeID(FileID(0), 0)
            } else {
                NodeID(ast.file_id, 0)
            }
        };

        // Predeclare module-scope nominals across all ASTs first, so `extend` resolution
        // doesn't depend on file order.
        for ast in asts.iter_mut() {
            let file_scope_id = scope_for_ast(ast, use_shared_scope);
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

        // Process imports (before full declaration phase so extends can see imported types)
        {
            // Build a map from file paths to FileIDs
            let path_to_file_id: FxHashMap<String, FileID> = asts
                .iter()
                .map(|ast| (ast.path.clone(), ast.file_id))
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
                            {
                                if let PatternKind::Bind(name) = &lhs.kind {
                                    return Some(name.name_str());
                                }
                            }
                            None
                        })
                        .collect();
                    (ast.file_id, names)
                })
                .collect();

            // Collect imports for each file (to avoid borrow conflicts)
            // (file_id, source_path, vec of (import, decl_node_id))
            let mut file_imports: Vec<(FileID, String, Vec<(Import, NodeID)>)> = Vec::new();
            for ast in &asts {
                let mut imports = Vec::new();
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
                    // Resolve the import path to a target file path
                    let target_path = match &import.path {
                        ImportPath::Relative(rel_path) => {
                            // Resolve relative to the source file's directory
                            let source_dir = Path::new(&source_path)
                                .parent()
                                .unwrap_or(Path::new("."));
                            // Strip leading "./" from relative path before joining
                            let clean_rel = rel_path.strip_prefix("./").unwrap_or(rel_path);
                            let resolved = source_dir.join(clean_rel);
                            resolved.to_string_lossy().to_string()
                        }
                        ImportPath::Package(_pkg_name) => {
                            // Package imports not yet implemented
                            self.diagnostic(decl_id, NameResolverError::PackageImportsNotSupported);
                            continue;
                        }
                    };

                    // Look up the target FileID
                    let Some(&target_file_id) = path_to_file_id.get(&target_path) else {
                        self.diagnostic(
                            decl_id,
                            NameResolverError::ModuleNotFound(target_path.clone()),
                        );
                        continue;
                    };

                    let target_scope_id = NodeID(target_file_id, 0);

                    // Get symbols from the target scope
                    let target_symbols: Vec<(String, Symbol, bool)> = {
                        let Some(target_scope) = self.scopes.get(&target_scope_id) else {
                            continue;
                        };
                        // Collect all value and type symbols
                        let mut symbols = Vec::new();
                        for (name, &symbol) in &target_scope.values {
                            symbols.push((name.clone(), symbol, false)); // false = value
                        }
                        for (name, &symbol) in &target_scope.types {
                            symbols.push((name.clone(), symbol, true)); // true = type
                        }
                        symbols
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
                                if matches!(symbol, Symbol::Builtin(..)) {
                                    continue;
                                }
                                if !self.phase.public_symbols.contains(&symbol) {
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
                                let found = target_symbols
                                    .iter()
                                    .find(|(n, _, _)| n == name_to_find);

                                match found {
                                    Some((_, symbol, is_type)) => {
                                        // Check if the symbol is public
                                        if !self.phase.public_symbols.contains(symbol) {
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
                                        let is_private = private_let_names
                                            .get(&target_file_id)
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
            let file_scope_id = scope_for_ast(ast, use_shared_scope);
            self.current_scope_id = Some(file_scope_id);
            let mut declarer = DeclDeclarer::new(self, &mut ast.node_ids);
            for root in &mut ast.roots {
                match root {
                    Node::Stmt(Stmt { id, .. }) => {
                        // If it's just a top level expr, it's not bound to anything so we stash
                        // it away so we can still type check it.
                        declarer.resolver.phase.unbound_nodes.push(*id);
                    }
                    Node::Decl(Decl {
                        id,
                        kind: DeclKind::Extend { .. },
                        ..
                    }) => {
                        declarer.resolver.phase.unbound_nodes.push(*id);
                    }
                    _ => {}
                }

                root.drive_mut(&mut declarer);
            }
        }

        // Second pass: resolve all names

        for ast in asts.iter_mut() {
            let file_scope_id = scope_for_ast(ast, use_shared_scope);
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
        let scope = self
            .scopes
            .get_mut(&scope_id)
            .unwrap_or_else(|| unreachable!("scope not found: {scope_id:?}, {:?}", name));

        if let Some(symbol) = scope.types.get(&name.name_str()) {
            return Some(*symbol);
        }

        if let Some(symbol) = scope.values.get(&name.name_str()) {
            return Some(*symbol);
        }

        if let Some(parent) = scope.parent_id
            && let Some(captured) = self.lookup_in_scope(name, parent)
            && parent != scope_id
        {
            let scope = self.scopes.get(&scope_id).expect("did not find scope");

            if scope.binder == Some(captured) {
                return Some(captured);
            }

            let Some(current_scope_binder) = scope.binder else {
                return Some(captured);
            };

            if !matches!(
                captured,
                Symbol::DeclaredLocal(..) | Symbol::ParamLocal(..) | Symbol::Global(..)
            ) {
                return Some(captured);
            }

            let parent_binder =
                self.nearest_enclosing_binder_from(Some(parent), current_scope_binder);

            let capture = Capture {
                symbol: captured,
                parent_binder,
                level: scope.level,
            };

            self.phase
                .captures
                .entry(current_scope_binder)
                .or_default()
                .insert(capture);
            self.phase.captured.insert(captured);

            return Some(captured);
        }

        let matching_imported_names = self.modules.lookup_name(&name.name_str());
        match matching_imported_names.len() {
            0 => {}
            1 => {
                return Some(matching_imported_names[0]);
            }
            _ => {
                self.diagnostic(
                    scope_id,
                    NameResolverError::AmbiguousName(name.clone(), matching_imported_names),
                );
            }
        }

        None
    }

    fn lookup_handler_in_scope(&mut self, effect: Symbol, scope_id: NodeID) -> Option<Symbol> {
        let handler = self
            .scopes
            .get(&scope_id)
            .and_then(|scope| scope.handlers.get(&effect).copied());

        if let Some((handler, _)) = handler {
            return Some(handler);
        }

        let parent = self.scopes.get(&scope_id).and_then(|scope| scope.parent_id);
        if let Some(parent) = parent
            && let Some(captured) = self.lookup_handler_in_scope(effect, parent)
            && parent != scope_id
        {
            let scope = self
                .scopes
                .get(&scope_id)
                .unwrap_or_else(|| unreachable!("scope not found: {scope_id:?}"));

            if scope.binder == Some(captured) {
                return Some(captured);
            }

            let Some(current_scope_binder) = scope.binder else {
                return Some(captured);
            };

            if !matches!(
                captured,
                Symbol::DeclaredLocal(..) | Symbol::ParamLocal(..) | Symbol::Global(..)
            ) {
                return Some(captured);
            }

            let parent_binder =
                self.nearest_enclosing_binder_from(Some(parent), current_scope_binder);

            let capture = Capture {
                symbol: captured,
                parent_binder,
                level: scope.level,
            };

            self.phase
                .captures
                .entry(current_scope_binder)
                .or_default()
                .insert(capture);
            self.phase.captured.insert(captured);

            return Some(captured);
        }

        None
    }

    pub(super) fn lookup(&mut self, name: &Name, node_id: Option<NodeID>) -> Option<Name> {
        let symbol = self.lookup_in_scope(
            name,
            self.current_scope_id
                .unwrap_or_else(|| unreachable!("no scope to declare in. name: {name:?}")),
        )?;

        if let Some(node_id) = node_id {
            self.track_dependency(symbol, node_id);
        }

        Some(Name::Resolved(symbol, name.name_str()))
    }

    pub(super) fn track_dependency(&mut self, to: Symbol, id: NodeID) {
        if let Some(symbols) = self
            .current_symbol_scope
            .iter()
            .rev()
            .find_map(|f| f.clone())
        {
            for (from_sym, from_id) in symbols {
                self.track_dependency_from_to(from_sym, from_id, to, id);
            }
        }
    }

    pub(super) fn track_dependency_from_to(
        &mut self,
        from_sym: Symbol,
        from_id: NodeID,
        to_sym: Symbol,
        to_id: NodeID,
    ) {
        if matches!(
            from_sym,
            Symbol::Builtin(..)
                | Symbol::InstanceMethod(..)
                | Symbol::StaticMethod(..)
                | Symbol::ParamLocal(..)
                | Symbol::MethodRequirement(..)
        ) || matches!(
            to_sym,
            Symbol::Builtin(..)
                | Symbol::InstanceMethod(..)
                | Symbol::StaticMethod(..)
                | Symbol::ParamLocal(..)
                | Symbol::MethodRequirement(..)
        ) {
            return;
        }

        // Skip external dependencies, but track Core module dependencies
        // when we're compiling the Core module itself
        if let Some(external_id) = to_sym.external_module_id()
            && (external_id != ModuleId::Core || self.current_module_id != ModuleId::Core) {
                return;
            }

        tracing::debug!("track_dependency from {from_sym:?} to {to_sym:?}");
        self.phase
            .scc_graph
            .add_edge((from_sym, from_id), (to_sym, to_id), to_id);
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
    fn enter_scope(&mut self, node_id: NodeID, symbols: Option<Vec<(Symbol, NodeID)>>) {
        self.current_scope_id = Some(node_id);
        self.current_symbol_scope.push(symbols.clone());

        // We track instance methods by type so we don't need to insert individual notes for them
        // automatically, however, we do insert nodes for them if they reference other things like globals
        let Some(symbols) = symbols else { return };

        for symbol in symbols {
            if !matches!(
                symbol.0,
                Symbol::InstanceMethod(..)
                    | Symbol::StaticMethod(..)
                    | Symbol::Synthesized(..)
                    | Symbol::Initializer(..)
                    | Symbol::Builtin(..)
                    | Symbol::Protocol(..)
            ) {
                self.phase
                    .scc_graph
                    .add_definition(symbol.0, symbol.1, self.current_level);
            }
        }
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
        self.current_symbol_scope.pop();
    }

    pub(super) fn declare(&mut self, name: &Name, kind: Symbol, node_id: NodeID) -> Name {
        let at_module_scope = self.at_module_scope();
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .unwrap_or_else(|| unreachable!("scope not found: {:?}", self.current_scope_id));

        // Check if this is a nominal type or effect that was already predeclared
        // If so, return the existing symbol to avoid duplicate creation
        if matches!(
            kind,
            Symbol::Struct(..) | Symbol::Enum(..) | Symbol::Protocol(..) | Symbol::Effect(..)
        ) {
            if let Some(&existing) = scope.types.get(&name.name_str()) {
                if std::mem::discriminant(&existing) == std::mem::discriminant(&kind) {
                    return Name::Resolved(existing, name.name_str());
                }
            }
        }

        // Check for predeclared Globals at module scope
        // This handles public Let bindings that were predeclared for import resolution
        // Only reuse if the existing Global is public (i.e., was predeclared)
        // Non-public Globals should allow shadowing (create new symbol)
        if at_module_scope && matches!(kind, Symbol::Global(..)) {
            if let Some(&existing) = scope.types.get(&name.name_str()) {
                if matches!(existing, Symbol::Global(..))
                    && self.phase.public_symbols.contains(&existing)
                {
                    return Name::Resolved(existing, name.name_str());
                }
            }
        }

        let module_id = self.current_module_id;
        let symbol = match kind {
            Symbol::Main => Symbol::Main,
            Symbol::Library => Symbol::Library,
            Symbol::Effect(..) => Symbol::Effect(self.symbols.next_effect(module_id)),
            Symbol::Struct(..) => Symbol::Struct(self.symbols.next_struct(module_id)),
            Symbol::Enum(..) => Symbol::Enum(self.symbols.next_enum(module_id)),
            Symbol::TypeAlias(..) => Symbol::TypeAlias(self.symbols.next_type_alias(module_id)),
            Symbol::TypeParameter(..) => Symbol::TypeParameter(self.symbols.next_type_parameter(module_id)),
            Symbol::Global(..) => Symbol::Global(self.symbols.next_global(module_id)),
            Symbol::DeclaredLocal(..) => Symbol::DeclaredLocal(self.symbols.next_local()),
            Symbol::PatternBindLocal(..) => {
                Symbol::PatternBindLocal(self.symbols.next_pattern_bind())
            }
            Symbol::ParamLocal(..) => Symbol::ParamLocal(self.symbols.next_param()),
            Symbol::Builtin(..) => unreachable!("should not be generating symbols for builtins"),
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
        };

        self.phase.symbols_to_node.insert(symbol, node_id);
        self.phase.symbol_names.insert(symbol, name.name_str());

        tracing::debug!(
            "declare type {name} {} -> {symbol:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );

        scope.types.insert(name.name_str(), symbol);

        Name::Resolved(symbol, name.name_str())
    }

    /// Mark a symbol as public (visible outside its file)
    pub(super) fn mark_public(&mut self, symbol: Symbol) {
        self.phase.public_symbols.insert(symbol);
    }


    fn nearest_enclosing_binder_from(
        &self,
        mut scope_id: Option<NodeID>,
        skip: Symbol,
    ) -> Option<Symbol> {
        while let Some(id) = scope_id {
            let scope = self
                .scopes
                .get(&id)
                .unwrap_or_else(|| unreachable!("scope not found: {id:?}"));

            if let Some(binder) = scope.binder
                && binder != skip
            {
                return Some(binder);
            }

            scope_id = scope.parent_id;
        }
        None
    }

    fn enter_pattern(&mut self, pattern: &mut Pattern) {
        match &mut pattern.kind {
            PatternKind::Bind(name @ Name::Raw(_)) => {
                *name = self.lookup(name, None).unwrap_or_else(|| {
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
                let Some(resolved) = self.lookup(enum_name, None) else {
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
                            *name = self.lookup(name, None).unwrap_or_else(|| {
                                tracing::error!("Lookup failed for {name:?}");
                                name.clone()
                            });
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            *name = self.lookup(name, None).unwrap_or_else(|| {
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
            if let Some(resolved_name) = self.lookup(name, Some(ty.id)) {
                *name = resolved_name
            } else {
                self.diagnostic(ty.id, NameResolverError::UndefinedName(name.name_str()));
            }
        }

        if let TypeAnnotationKind::SelfType(name) = &mut ty.kind {
            if let Some(resolved_name) = self.lookup(name, Some(ty.id)) {
                *name = resolved_name
            } else {
                self.diagnostic(ty.id, NameResolverError::UndefinedName(name.name_str()));
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block expr decls
    ///////////////////////////////////////////////////////////////////////////
    fn enter_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(block),
            ..
        }) = &mut stmt.kind
        {
            self.enter_scope(block.id, None);
        }

        on!(&mut stmt.kind, StmtKind::Handling { effect_name, .. }, {
            let Some(Name::Resolved(effect_sym, _)) = self.lookup(effect_name, Some(stmt.id))
            else {
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

            let Some(scope) = self.current_scope_mut() else {
                self.diagnostic(
                    stmt.id,
                    NameResolverError::UndefinedName("no scope".to_string()),
                );

                return;
            };

            scope.handlers.insert(effect_sym, (effect_sym, stmt.id));
        });

        if let StmtKind::Assignment(box lhs, ..) = &mut stmt.kind {
            self.track_assignment_mutation(lhs);
        }
    }

    fn exit_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(..),
            ..
        }) = &mut stmt.kind
        {
            self.exit_scope(stmt.id);
        }
    }

    fn track_assignment_mutation(&mut self, expr: &mut Expr) {
        let Some((name, id)) = Self::assignment_base_name(expr) else {
            return;
        };
        let Some(resolved) = self.lookup(name, Some(id)) else {
            self.diagnostic(id, NameResolverError::UndefinedName(name.name_str()));
            return;
        };

        self.phase
            .mutated_symbols
            .insert(resolved.symbol().unwrap_or_else(|_| unreachable!("")));

        *name = resolved;
    }

    fn assignment_base_name(expr: &mut Expr) -> Option<(&mut Name, NodeID)> {
        match &mut expr.kind {
            ExprKind::Variable(name) => Some((name, expr.id)),
            ExprKind::Member(Some(inner), ..) => Self::assignment_base_name(inner),
            _ => None,
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Locals scoping
    ///////////////////////////////////////////////////////////////////////////

    fn enter_match_arm(&mut self, arm: &mut MatchArm) {
        self.enter_scope(arm.id, None);
    }

    fn exit_match_arm(&mut self, arm: &mut MatchArm) {
        self.exit_scope(arm.id);
    }

    #[instrument(skip(self, expr))]
    fn enter_expr(&mut self, expr: &mut Expr) {
        on!(&mut expr.kind, ExprKind::InlineIR(instr), {
            for bind in &mut instr.binds {
                self.enter_expr(bind);
            }

            match &mut instr.kind {
                InlineIRInstructionKind::Constant { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Cmp { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Add { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Sub { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Mul { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Div { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Ref { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Call { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Record { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::GetField { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::SetField { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::_Print { .. } => (),
                InlineIRInstructionKind::Alloc { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Free { .. } => (),
                InlineIRInstructionKind::Load { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Store { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Move { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Copy { ty, .. } => self.enter_type_annotation(ty),
                InlineIRInstructionKind::Gep { ty, .. } => self.enter_type_annotation(ty),
            }
        });

        on!(&mut expr.kind, ExprKind::Variable(name), {
            let Some(resolved_name) = self.lookup(name, Some(expr.id)) else {
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
            let Some(resolved_name) = self.lookup(effect_name, Some(expr.id)) else {
                self.diagnostic(
                    expr.id,
                    NameResolverError::UndefinedName(effect_name.name_str()),
                );
                return;
            };

            *effect_name = resolved_name;

            if let Ok(effect_sym) = effect_name.symbol()
                && let Some(scope_id) = self.current_scope_id
                && let Some(handler_sym) = self.lookup_handler_in_scope(effect_sym, scope_id)
            {
                self.phase.effect_handlers.insert(expr.id, handler_sym);
                self.track_dependency(handler_sym, expr.id);
            }
        });
    }

    fn exit_expr(&mut self, _expr: &mut Expr) {}

    ///////////////////////////////////////////////////////////////////////////
    // Func scoping
    ///////////////////////////////////////////////////////////////////////////

    fn enter_func(&mut self, func: &mut Func) {
        let Ok(func_symbol) = func.name.symbol() else {
            unreachable!("did not resolve func");
        };
        self.enter_scope(func.id, Some(vec![(func_symbol, func.id)]));
        self.current_func_symbols.push(func_symbol);

        for name in &mut func.effects.names {
            let Some(resolved_name) = self.lookup(name, None) else {
                self.diagnostic(func.id, NameResolverError::Unresolved(name.clone()));
                continue;
            };
            *name = resolved_name;
        }
    }

    fn exit_func(&mut self, func: &mut Func) {
        self.current_func_symbols.pop();
        self.exit_scope(func.id);
    }

    fn enter_func_signature(&mut self, func: &mut FuncSignature) {
        self.enter_scope(func.id, None);
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
                | DeclKind::Protocol { name, .. }
                | DeclKind::Extend { name, .. },
            {
                let Ok(sym) = name.symbol() else {
                    self.diagnostic(decl.id, NameResolverError::Unresolved(name.clone()));
                    return;
                };

                self.enter_scope(decl.id, Some(vec![(sym, decl.id)]));
            }
        );

        on!(&mut decl.kind, DeclKind::Init { params, .. }, {
            self.enter_scope(decl.id, None);

            for param in params {
                param.name = self.declare(&param.name, some!(ParamLocal), param.id);
            }
        });

        on!(&decl.kind, DeclKind::Effect { .. }, {
            self.enter_scope(decl.id, None);
        });

        on!(&mut decl.kind, DeclKind::Method { func, .. }, {
            let sym = func
                .name
                .symbol()
                .unwrap_or_else(|_| unreachable!("did not resolve name"));

            self.enter_scope(func.id, Some(vec![(sym, func.id)]));
        });

        on!(&decl.kind, DeclKind::Let { lhs, .. }, {
            self.current_level = self.current_level.next();
            let mut last = None;

            for (id, binder) in lhs.collect_binders() {
                if let Some((last_id, last_binder)) = last
                    && id != last_id
                {
                    self.track_dependency_from_to(last_binder, last_id, binder, id);
                    self.track_dependency_from_to(binder, id, last_binder, last_id);
                }

                last = Some((id, binder));
                self.enter_scope(id, Some(vec![(binder, decl.id)]));
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
                | DeclKind::Method { .. }
                | DeclKind::Init { .. }
                | DeclKind::Effect { .. },
            {
                self.exit_scope(decl.id);
            }
        );

        on!(&decl.kind, DeclKind::Let { lhs, .. }, {
            for (id, _binder) in lhs.collect_binders() {
                self.exit_scope(id);
            }
        });

        on!(decl.kind, DeclKind::Let { .. }, {
            self.current_level = self.current_level.prev();
        })
    }
}
