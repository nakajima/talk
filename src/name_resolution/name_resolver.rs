use std::{error::Error, fmt::Display, rc::Rc};

use derive_visitor::{DriveMut, VisitorMut};
use generational_arena::Index;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    ast::{AST, ASTPhase, Parsed},
    compiling::module::{ModuleEnvironment, ModuleId},
    diagnostic::Diagnostic,
    name::Name,
    name_resolution::{
        builtins,
        decl_declarer::DeclDeclarer,
        symbol::{Symbol, Symbols},
        transforms::{
            lower_funcs_to_lets::LowerFuncsToLets, lower_operators::LowerOperators,
            prepend_self_to_methods::PrependSelfToMethods,
        },
    },
    node_id::{FileID, NodeID},
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        match_arm::MatchArm,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    on, some,
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
    pub symbols_to_node: FxHashMap<Symbol, NodeID>,
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

    pub(super) phase: NameResolved,

    pub(super) current_module_id: crate::compiling::module::ModuleId,
    pub(super) modules: Rc<ModuleEnvironment>,

    // Scope stuff
    pub(super) scopes: FxHashMap<NodeID, Scope>,
    pub(super) current_scope_id: Option<NodeID>,
}

impl ASTPhase for NameResolved {}

impl NameResolver {
    pub fn new(modules: Rc<ModuleEnvironment>, current_module_id: ModuleId) -> Self {
        let mut resolver = Self {
            symbols: Default::default(),
            diagnostics: Default::default(),
            phase: NameResolved::default(),
            current_module_id,
            scopes: Default::default(),
            current_scope_id: None,
            modules,
        };

        resolver.init_root_scope();
        resolver
    }

    fn init_root_scope(&mut self) {
        let root_scope = Scope::new(NodeID(FileID(0), 0), None, 1);
        self.scopes.insert(NodeID(FileID(0), 0), root_scope);
        self.current_scope_id = Some(NodeID(FileID(0), 0));
    }

    pub fn resolve(&mut self, mut asts: Vec<AST<Parsed>>) -> Vec<AST<NameResolved>> {
        let scope = self
            .scopes
            .get_mut(&NodeID(FileID(0), 0))
            .expect("root scope");
        builtins::import_builtins(scope);

        // First pass: run transforms and declare all types
        for ast in &mut asts {
            LowerFuncsToLets::run(ast);
            LowerOperators::run(ast);
            PrependSelfToMethods::run(ast);
        }

        {
            // One declarer per AST so the single &mut self borrow ends after each AST.
            for ast in &mut asts {
                let mut declarer = DeclDeclarer::new(self, &mut ast.node_ids);
                for root in &mut ast.roots {
                    root.drive_mut(&mut declarer);
                }
                // declarer dropped here before the next AST
            }
        } // declarer definitely dropped before second pass

        // Second pass: resolve all names
        self.current_scope_id = Some(NodeID(FileID(0), 0));

        let mut out: Vec<AST<NameResolved>> = Vec::with_capacity(asts.len());

        for ast in asts.into_iter() {
            let AST {
                path,
                mut roots,
                mut diagnostics,
                meta,
                file_id,
                node_ids,
                synthsized_ids,
                ..
            } = ast;

            // Borrow &mut self only while walking each root, then drop immediately.
            for root in &mut roots {
                root.drive_mut(self);
            }

            // Move any diagnostics accumulated on self into this AST.
            for diagnostic in std::mem::take(&mut self.diagnostics) {
                diagnostics.push(diagnostic.into());
            }

            self.phase.scopes = self.scopes.clone();

            out.push(AST {
                path,
                roots,
                diagnostics,
                meta,
                phase: std::mem::take(&mut self.phase),
                node_ids,
                file_id,
                synthsized_ids,
            });
        }

        out
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
            .unwrap_or_else(|| panic!("scope not found: {scope_id:?}"));

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

        for (id, module) in self.modules.modules.iter() {
            if let Some(sym) = module.exports.get(&name.name_str()) {
                return Some(sym.import(*id));
            }
        }

        None
    }

    pub(super) fn lookup(&mut self, name: &Name) -> Option<Name> {
        let symbol =
            self.lookup_in_scope(name, self.current_scope_id.expect("no scope to declare in"))?;

        Some(Name::Resolved(symbol, name.name_str()))
    }

    pub(super) fn diagnostic(&mut self, span: Span, err: NameResolverError) {
        self.diagnostics
            .push(Diagnostic::<NameResolverError> { kind: err, span });
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

    pub(super) fn declare(&mut self, name: &Name, kind: Symbol, node_id: NodeID) -> Name {
        let scope = self
            .scopes
            .get_mut(&self.current_scope_id.expect("no scope to declare in"))
            .unwrap_or_else(|| panic!("scope not found: {:?}", self.current_scope_id));

        let module_id = self.current_module_id;
        let symbol = match kind {
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
            Symbol::Builtin(..) => Symbol::Builtin(self.symbols.next_builtin(module_id)),
            Symbol::Property(..) => Symbol::Property(self.symbols.next_property(module_id)),
            Symbol::Synthesized(..) => {
                Symbol::Synthesized(self.symbols.next_synthesized(module_id))
            }
            Symbol::InstanceMethod(..) => {
                Symbol::InstanceMethod(self.symbols.next_instance_method(module_id))
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

        tracing::debug!(
            "declare type {} -> {symbol:?} {:?}",
            name.name_str(),
            self.current_scope_id
        );

        scope.types.insert(name.name_str(), symbol);

        Name::Resolved(symbol, name.name_str())
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

            if matches!(
                name,
                Name::Resolved(
                    Symbol::Struct(_) | Symbol::Enum(_) | Symbol::TypeAlias(_),
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

    fn enter_func_signature(&mut self, func: &mut FuncSignature) {
        self.enter_scope(func.id);
    }

    fn exit_func_signature(&mut self, _func: &mut FuncSignature) {
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

        on!(&mut decl.kind, DeclKind::Extend { name, .. }, {
            let Some(type_name) = self.lookup(name) else {
                self.diagnostic(decl.span, NameResolverError::UndefinedName(name.name_str()));
                return;
            };

            *name = type_name;

            self.current_scope_mut()
                .unwrap()
                .types
                .insert("Self".into(), name.symbol().unwrap());
        });

        on!(&mut decl.kind, DeclKind::Init { params, .. }, {
            self.enter_scope(decl.id);

            for param in params {
                param.name = self.declare(&param.name, some!(ParamLocal), param.id);
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
