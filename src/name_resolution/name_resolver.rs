use std::{error::Error, fmt::Display};

use derive_visitor::{DriveMut, VisitorMut};
use generational_arena::Index;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    ast::{AST, ASTPhase, Parsed},
    diagnostic::Diagnostic,
    name::Name,
    name_resolution::{
        builtins,
        decl_declarer::DeclDeclarer,
        symbol::{Symbol, Symbols},
        transforms::{
            lower_funcs_to_lets::LowerFuncsToLets, prepend_self_to_methods::PrependSelfToMethods,
        },
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        match_arm::MatchArm,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    on,
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameResolverError {
    UndefinedName(String),
    Unresolved(Name),
}

impl Error for NameResolverError {}
impl Display for NameResolverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefinedName(name) => write!(f, "Undefined name: {name}"),
            Self::Unresolved(name) => write!(f, "Unresolved symbol: {name:?}"),
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
}

impl Scope {
    pub fn new(node_id: NodeID, parent_id: Option<NodeID>, depth: u32) -> Self {
        Scope {
            node_id,
            parent_id,
            depth,
            values: Default::default(),
            types: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct NameResolved {
    pub captures: FxHashMap<NodeID, FxHashSet<Symbol>>,
    pub is_captured: FxHashSet<Symbol>,
    pub scopes: FxHashMap<NodeID, Scope>,
}

pub type ScopeId = Index;

#[derive(Default, Debug, VisitorMut)]
#[visitor(
    Func(enter, exit),
    Stmt(enter, exit),
    MatchArm(enter, exit),
    Decl(enter, exit),
    Expr(enter),
    TypeAnnotation(enter),
    Pattern(enter)
)]
pub struct NameResolver {
    path: String,
    pub(super) symbols: Symbols,
    diagnostics: Vec<Diagnostic<NameResolverError>>,
    pub(super) phase: NameResolved,

    // Scope stuff
    pub(super) scopes: FxHashMap<NodeID, Scope>,
    pub(super) current_scope_id: Option<NodeID>,
}

impl ASTPhase for NameResolved {}

impl NameResolver {
    pub fn resolve(mut ast: AST<Parsed>) -> AST<NameResolved> {
        LowerFuncsToLets::run(&mut ast);
        PrependSelfToMethods::run(&mut ast);

        let AST {
            path,
            roots,
            mut diagnostics,
            meta,
            ..
        } = ast;

        let mut resolver = NameResolver::default();

        // Declare stuff
        let mut declarer = DeclDeclarer::new(&mut resolver);
        declarer.start_scope(NodeID(0));
        let initial_scope = declarer
            .resolver
            .current_scope_mut()
            .expect("didn't get started scope");
        builtins::import_builtins(initial_scope);

        let roots: Vec<Node> = roots
            .into_iter()
            .map(|mut root| {
                root.drive_mut(&mut declarer);
                root
            })
            .collect();

        resolver.enter_scope(NodeID(0));
        // Resolve stuff
        let roots: Vec<Node> = roots
            .into_iter()
            .map(|mut root| {
                root.drive_mut(&mut resolver);
                root
            })
            .collect();

        for diagnostic in resolver.diagnostics {
            diagnostics.push(diagnostic.into());
        }

        AST {
            path,
            roots,
            diagnostics,
            meta,
            phase: resolver.phase,
            node_ids: ast.node_ids,
        }
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
        tracing::debug!("looking up {name:?} in scope {:?}", self.current_scope(),);

        let scope = self.scopes.get_mut(&scope_id).expect("scope not found");

        if let Some(symbol) = scope.types.get(&name.name_str()) {
            return Some(*symbol);
        }

        if let Some(symbol) = scope.values.get(&name.name_str()) {
            return Some(*symbol);
        }

        if let Some(parent) = scope.parent_id
            && let Some(captured) = self.lookup_in_scope(name, parent)
        {
            let scope = self.scopes.get(&scope_id).expect("did not find scope");

            self.phase
                .captures
                .entry(scope.node_id)
                .or_default()
                .insert(captured);
            self.phase.is_captured.insert(captured);

            return Some(captured);
        }

        None
    }

    pub(super) fn lookup(&mut self, name: &Name) -> Option<Name> {
        let symbol =
            self.lookup_in_scope(name, self.current_scope_id.expect("no scope to declare in"))?;

        Some(Name::Resolved(symbol, name.name_str()))
    }

    pub(super) fn diagnostic(&mut self, span: Span, err: NameResolverError) {
        self.diagnostics.push(Diagnostic::<NameResolverError> {
            kind: err,
            path: self.path.clone(),
            span,
        });
    }

    fn enter_scope(&mut self, node_id: NodeID) {
        self.current_scope_id = Some(node_id);
    }

    fn exit_scope(&mut self) {
        let current_scope_id = self.current_scope_id.expect("no scope to exit");
        let current_scope = self
            .scopes
            .get(&current_scope_id)
            .expect("did not find current scope");

        self.current_scope_id = current_scope.parent_id;
    }

    pub(super) fn declare_type(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_decl();
        let sym = Symbol::Type(id);
        tracing::debug!(
            "declare type {} -> {sym:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );
        scope.types.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }

    pub(super) fn declare_global(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_value();
        let sym = Symbol::Global(id);
        tracing::debug!(
            "declare global {} -> {sym:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );
        scope.values.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }

    pub(super) fn declare_variant(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_variant();
        let sym = Symbol::Variant(id);
        tracing::debug!(
            "declare variant {} -> {sym:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );
        scope.values.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }

    pub(super) fn declare_instance_method(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_instance_method();
        let sym = Symbol::InstanceMethod(id);
        tracing::debug!(
            "declare instance method {} -> {sym:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );
        scope.values.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }

    pub(super) fn declare_static_method(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_static_method();
        let sym = Symbol::StaticMethod(id);
        tracing::debug!(
            "declare static method {} -> {sym:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );
        scope.values.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }

    pub(super) fn declare_property(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_property();
        let sym = Symbol::Property(id);
        tracing::debug!(
            "declare global {} -> {sym:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );
        scope.values.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }

    pub(super) fn declare_local(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_local();
        let sym = Symbol::DeclaredLocal(id);
        tracing::debug!(
            "declare local {} -> {sym:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );
        scope.values.insert(name.name_str(), sym);
        Name::Resolved(sym, name.name_str())
    }

    pub(super) fn declare_param(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_param();
        let sym = Symbol::ParamLocal(id);
        tracing::debug!(
            "declare param {} -> {sym:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );
        scope.values.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }

    fn enter_pattern(&mut self, pattern: &mut Pattern) {
        if let PatternKind::Variant { enum_name, .. } = &mut pattern.kind
            && let Some(enum_name) = enum_name
        {
            let Some(resolved) = self.lookup(enum_name) else {
                self.diagnostic(
                    pattern.span,
                    NameResolverError::UndefinedName(enum_name.name_str()),
                );
                return;
            };

            *enum_name = resolved;
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
                self.diagnostic(ty.span, NameResolverError::UndefinedName(name.name_str()));
            }
        }

        if let TypeAnnotationKind::SelfType(name) = &mut ty.kind {
            if let Some(resolved_name) = self.lookup(name) {
                *name = resolved_name
            } else {
                self.diagnostic(ty.span, NameResolverError::UndefinedName(name.name_str()));
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
            self.enter_scope(block.id);
        }
    }

    fn exit_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(..),
            ..
        }) = &mut stmt.kind
        {
            self.exit_scope();
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Locals scoping
    ///////////////////////////////////////////////////////////////////////////

    fn enter_match_arm(&mut self, arm: &mut MatchArm) {
        self.enter_scope(arm.id);
    }

    fn exit_match_arm(&mut self, _arm: &mut MatchArm) {
        self.exit_scope();
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        on!(&mut expr.kind, ExprKind::Variable(name), {
            let Some(resolved_name) = self.lookup(name) else {
                self.diagnostic(expr.span, NameResolverError::UndefinedName(name.name_str()));
                return;
            };

            *name = resolved_name;

            if matches!(name, Name::Resolved(Symbol::Type(_), _)) {
                expr.kind = ExprKind::Constructor(name.clone());
            }
        });
    }

    ///////////////////////////////////////////////////////////////////////////
    // Func scoping
    ///////////////////////////////////////////////////////////////////////////

    fn enter_func(&mut self, func: &mut Func) {
        let Func {
            name: Name::Resolved(_, _),
            ..
        } = func
        else {
            panic!("did not resolve name")
        };

        self.enter_scope(func.id);
    }

    fn exit_func(&mut self, func: &mut Func) {
        let Func {
            name: Name::Resolved(_sym, _),
            ..
        } = func
        else {
            panic!("Did not resolve func")
        };

        self.exit_scope();
    }

    ///////////////////////////////////////////////////////////////////////////
    // Nominal scoping
    ///////////////////////////////////////////////////////////////////////////
    fn enter_decl(&mut self, decl: &mut Decl) {
        on!(
            decl.kind,
            DeclKind::Enum { .. }
                | DeclKind::Struct { .. }
                | DeclKind::Protocol { .. }
                | DeclKind::Extend { .. },
            {
                self.enter_scope(decl.id);
            }
        );

        on!(&mut decl.kind, DeclKind::Init { params, .. }, {
            self.enter_scope(decl.id);

            for param in params {
                param.name = self.declare_param(&param.name);
            }
        })
    }

    fn exit_decl(&mut self, decl: &mut Decl) {
        on!(
            decl.kind,
            DeclKind::Enum { .. }
                | DeclKind::Struct { .. }
                | DeclKind::Protocol { .. }
                | DeclKind::Extend { .. },
            {
                self.exit_scope();
            }
        );

        on!(&mut decl.kind, DeclKind::Init { .. }, {
            self.exit_scope();
        })
    }
}
