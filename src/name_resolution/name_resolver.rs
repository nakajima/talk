use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt::Display,
};

use generational_arena::{Arena, Index};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    ast::{AST, ASTPhase, Parsed},
    diagnostic::Diagnostic,
    name::Name,
    name_resolution::{
        decl_declarer::DeclDeclarer,
        symbol::{LocalId, Symbol, Symbols},
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
    },
    span::Span,
    traversal::fold_mut::FoldMut,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameResolverError {
    UndefinedName(String),
}
impl Error for NameResolverError {}
impl Display for NameResolverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefinedName(name) => write!(f, "Undefined name: {name}"),
        }
    }
}

#[derive(Default, Debug)]
pub struct Scope {
    pub node_id: NodeID,
    pub parent_id: Option<ScopeId>,

    pub values: FxHashMap<String, Symbol>,
    pub types: FxHashMap<String, Symbol>,
}

impl Scope {
    pub fn new(node_id: NodeID, parent_id: Option<ScopeId>) -> Self {
        Scope {
            node_id,
            parent_id,
            values: Default::default(),
            types: Default::default(),
        }
    }
}

#[derive(Default, Debug)]
pub struct CurrentFunc {
    capturable_locals: BTreeSet<LocalId>,
    captures: BTreeSet<LocalId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct NameResolved {
    pub captures: FxHashMap<NodeID, FxHashSet<Symbol>>,
    pub is_captured: FxHashSet<Symbol>,
}

pub type ScopeId = Index;

#[derive(Default, Debug)]
pub struct NameResolver {
    path: String,
    pub(super) symbols: Symbols,
    diagnostics: Vec<Diagnostic<NameResolverError>>,
    phase: NameResolved,
    current_funcs: Vec<CurrentFunc>,

    // Scope stuff
    pub(super) scopes: Arena<Scope>,
    pub(super) scopes_by_node_id: FxHashMap<NodeID, ScopeId>,
    pub(super) node_ids_by_scope: FxHashMap<ScopeId, NodeID>,
    pub(super) current_scope: Option<ScopeId>,
}

impl ASTPhase for NameResolved {}

impl NameResolver {
    pub fn resolve(ast: AST<Parsed>) -> AST<NameResolved> {
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

        let roots: Vec<Node> = roots
            .into_iter()
            .map(|mut root| {
                declarer.fold_node_mut(&mut root);
                root
            })
            .collect();

        // Resolve stuff
        let roots: Vec<Node> = roots
            .into_iter()
            .map(|mut root| {
                resolver.fold_node_mut(&mut root);
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
        }
    }

    fn lookup_in_scope(&mut self, name: &Name, scope_id: ScopeId) -> Option<Symbol> {
        tracing::debug!(
            "looking up {name:?} in scope {scope_id:?}. scopes: {:?}. scope map: {:?}",
            self.scopes,
            self.scopes_by_node_id
        );

        let scope = self.scopes.get_mut(scope_id).expect("scope not found");

        if let Some(symbol) = scope.types.get(&name.name_str()) {
            return Some(*symbol);
        }

        if let Some(symbol) = scope.values.get(&name.name_str()) {
            return Some(*symbol);
        }

        if let Some(parent) = scope.parent_id
            && let Some(captured) = self.lookup_in_scope(name, parent)
        {
            let scope = self.scopes.get(scope_id).expect("did not find scope");

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

    fn lookup(&mut self, name: &Name) -> Option<Symbol> {
        self.lookup_in_scope(name, self.current_scope.expect("no scope to declare in"))
    }

    fn diagnostic(&mut self, span: Span, err: NameResolverError) {
        self.diagnostics.push(Diagnostic::<NameResolverError> {
            kind: err,
            path: self.path.clone(),
            span,
        });
    }

    fn enter_scope(&mut self, node_id: NodeID) {
        let scope_id = self
            .scopes_by_node_id
            .get(&node_id)
            .expect("no scope found for node");

        self.current_scope = Some(*scope_id);
    }

    fn exit_scope(&mut self) {
        let current_scope_id = self.current_scope.expect("no scope to exit");
        let current_scope = self
            .scopes
            .get(current_scope_id)
            .expect("did not find current scope");

        self.current_scope = current_scope.parent_id;
    }

    pub fn declare_type(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(self.current_scope.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_decl();
        let sym = Symbol::Type(id);
        tracing::debug!("declare type {} -> {sym:?}", name.name_str());
        scope.types.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }

    pub fn declare_value(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(self.current_scope.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_decl();
        let sym = Symbol::Value(id);
        tracing::debug!("declare value {} -> {sym:?}", name.name_str());
        scope.values.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }

    pub fn declare_local(&mut self, name: &Name) -> Name {
        let scope = self
            .scopes
            .get_mut(self.current_scope.expect("no scope to declare in"))
            .expect("scope not found");

        let id = self.symbols.next_local();
        let sym = Symbol::Local(id);
        tracing::debug!("declare local {} -> {sym:?}", name.name_str());
        scope.values.insert(name.name_str(), sym);

        Name::Resolved(sym, name.name_str())
    }
}

impl FoldMut for NameResolver {
    ///////////////////////////////////////////////////////////////////////////
    // Block expr decls
    ///////////////////////////////////////////////////////////////////////////
    fn enter_stmt_mut(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(block),
            ..
        }) = &mut stmt.kind
        {
            self.enter_scope(block.id);
        }
    }

    fn exit_stmt_mut(&mut self, stmt: &mut Stmt) {
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

    fn enter_expr_variable_mut(&mut self, expr: &mut Expr) {
        let Expr {
            kind: ExprKind::Variable(name),
            ..
        } = expr
        else {
            unreachable!()
        };

        let Some(sym) = self.lookup(name) else {
            self.diagnostic(expr.span, NameResolverError::UndefinedName(name.name_str()));
            return;
        };

        *name = Name::Resolved(sym, name.name_str());
    }

    ///////////////////////////////////////////////////////////////////////////
    // Func scoping
    ///////////////////////////////////////////////////////////////////////////

    fn enter_decl_func_mut(&mut self, decl: &mut Decl) {
        let Decl {
            kind:
                DeclKind::Func {
                    name: Name::Resolved(_, _),
                    params,
                    ..
                },
            ..
        } = decl
        else {
            unreachable!()
        };

        self.enter_scope(decl.id);

        for param in params {
            param.name = self.declare_local(&param.name);
        }
    }

    fn exit_decl_func_mut(&mut self, decl: &mut Decl) {
        let Decl {
            kind:
                DeclKind::Func {
                    name: Name::Resolved(_sym, _),
                    ..
                },
            ..
        } = decl
        else {
            unreachable!()
        };

        self.exit_scope();
    }
}
