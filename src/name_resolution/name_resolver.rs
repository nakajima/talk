use std::{error::Error, fmt::Display, rc::Rc};

use derive_visitor::{DriveMut, VisitorMut};
use generational_arena::Index;
use indexmap::IndexMap;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use crate::{
    ast::{AST, NameResolved, Parsed},
    compiling::module::{ModuleEnvironment, ModuleId},
    diagnostic::{AnyDiagnostic, Diagnostic},
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
        decl::{Decl, DeclKind},
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
        }
    }
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub node_id: NodeID,
    pub parent_id: Option<NodeID>,
    pub values: FxHashMap<String, Symbol>,
    pub types: FxHashMap<String, Symbol>,
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
            binder,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ResolvedNames {
    pub captures: FxHashMap<Symbol, FxHashSet<Capture>>,
    pub is_captured: FxHashSet<Symbol>,
    pub scopes: FxHashMap<NodeID, Scope>,
    pub symbol_names: FxHashMap<Symbol, String>,
    pub symbols_to_node: FxHashMap<Symbol, NodeID>,
    pub scc_graph: SCCGraph,
    pub unbound_nodes: Vec<NodeID>,
    pub child_types: IndexMap<Symbol, IndexMap<Label, Symbol>>,
    pub diagnostics: Vec<AnyDiagnostic>,
}

pub type ScopeId = Index;

#[derive(Debug, VisitorMut)]
#[visitor(
    Func(enter, exit),
    FuncSignature,
    Stmt(enter, exit),
    MatchArm(enter, exit),
    Decl(enter, exit),
    Expr(enter),
    TypeAnnotation(enter),
    Pattern(enter)
)]
pub struct NameResolver {
    pub symbols: Symbols,
    diagnostics: Vec<Diagnostic<NameResolverError>>,

    pub phase: ResolvedNames,

    pub(super) current_module_id: crate::compiling::module::ModuleId,
    pub(super) modules: Rc<ModuleEnvironment>,

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
        let root_scope = Scope::new(None, self.current_level, NodeID(FileID(0), 0), None, 1);
        self.scopes.insert(NodeID(FileID(0), 0), root_scope);
        self.current_scope_id = Some(NodeID(FileID(0), 0));
    }

    pub fn resolve(
        &mut self,
        mut asts: Vec<AST<Parsed>>,
    ) -> (Vec<AST<NameResolved>>, ResolvedNames) {
        let scope = self
            .scopes
            .get_mut(&NodeID(FileID(0), 0))
            .expect("root scope");

        builtins::import_builtins(scope);

        // First pass: run transforms and declare all types
        for ast in asts.iter_mut() {
            LowerFuncsToLets::run(ast);
            LowerOperators::run(ast);
            PrependSelfToMethods::run(ast);
        }

        {
            // One declarer per AST so the single &mut self borrow ends after each AST.
            for ast in asts.iter_mut() {
                let mut declarer = DeclDeclarer::new(self, &mut ast.node_ids);
                declarer.predeclare_nominals(
                    ast.roots
                        .iter()
                        .filter_map(|r| {
                            if let Node::Decl(decl) = r {
                                Some(decl)
                            } else {
                                None
                            }
                        })
                        .collect_vec()
                        .as_slice(),
                );
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
        }

        // Second pass: resolve all names

        for ast in asts.iter_mut() {
            // Borrow &mut self only while walking each root, then drop immediately.
            for root in &mut ast.roots {
                self.current_scope_id = Some(NodeID(FileID(0), 0));
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
            self.phase.is_captured.insert(captured);

            return Some(captured);
        }

        let matching_imported_names = self.modules.lookup_name(&name.name_str());
        match matching_imported_names.len() {
            0 => (),
            1 => return Some(matching_imported_names[0]),
            _ => {
                self.diagnostic(
                    scope_id,
                    NameResolverError::AmbiguousName(name.clone(), matching_imported_names),
                );
            }
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

        if to_sym.external_module_id().is_some() {
            return;
        }

        tracing::debug!("track_dependency from {from_sym:?} to {to_sym:?}");
        self.phase
            .scc_graph
            .add_edge((from_sym, from_id), (to_sym, to_id), to_id);
    }

    pub(super) fn diagnostic(&mut self, id: NodeID, err: NameResolverError) {
        self.diagnostics
            .push(Diagnostic::<NameResolverError> { kind: err, id });
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
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .unwrap_or_else(|| unreachable!("scope not found: {:?}", self.current_scope_id));

        let module_id = self.current_module_id;
        let symbol = match kind {
            Symbol::Main => Symbol::Main,
            Symbol::Library => Symbol::Library,
            Symbol::Struct(..) => Symbol::Struct(self.symbols.next_struct(module_id)),
            Symbol::Enum(..) => Symbol::Enum(self.symbols.next_enum(module_id)),
            Symbol::TypeAlias(..) => Symbol::TypeAlias(self.symbols.next_type_alias(module_id)),
            Symbol::TypeParameter(..) => Symbol::TypeParameter(self.symbols.next_type_parameter()),
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
            PatternKind::Bind(name) => {
                *name = self.lookup(name, None).unwrap_or_else(|| {
                    tracing::error!("Lookup failed for {name:?}");
                    name.clone()
                })
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
            _ => unimplemented!("{pattern:?}"),
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
    }

    ///////////////////////////////////////////////////////////////////////////
    // Func scoping
    ///////////////////////////////////////////////////////////////////////////

    fn enter_func(&mut self, func: &mut Func) {
        self.enter_scope(
            func.id,
            Some(vec![(
                func.name
                    .symbol()
                    .unwrap_or_else(|_| unreachable!("did not resolve func")),
                func.id,
            )]),
        );
    }

    fn exit_func(&mut self, func: &mut Func) {
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
                | DeclKind::Init { .. },
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
