use rustc_hash::FxHashMap;

use crate::{
    hir::{
        Block, CallArg, Decl, DeclKind, Expr, ExprKind, MatchArm, Node, Parameter, Pattern,
        PatternKind, Stmt, StmtKind,
    },
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{func::CaptureSpec, type_annotation::TypeAnnotation},
    types::{
        TypeOutput,
        output::stored_field_symbol,
        ty::Ty,
    },
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct BlockId(pub(crate) usize);

impl BlockId {
    #[cfg(test)]
    pub(crate) fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct ScopeId(pub(crate) usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Scope {
    pub(crate) id: ScopeId,
    pub(crate) parent: Option<ScopeId>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct Local(pub(crate) usize);

impl Local {
    #[allow(dead_code)]
    #[cfg(test)]
    pub(crate) fn index(self) -> usize {
        self.0
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum LocalKind {
    Param,
    UserLocal,
    CompilerTemp,
    Return,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LocalDecl {
    pub(crate) local: Local,
    pub(crate) symbol: Symbol,
    pub(crate) ty: Option<Ty>,
    pub(crate) kind: LocalKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum KeyPathComponent {
    Field(Symbol),
}

/// A source-shaped storage path. This is the MIR equivalent of a place:
/// ownership and lowering should reason about this representation instead of
/// rediscovering roots and field paths from AST expressions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct KeyPath {
    pub(crate) root: Local,
    pub(crate) components: Vec<KeyPathComponent>,
}

impl KeyPath {
    pub(crate) fn root(root: Local) -> Self {
        Self {
            root,
            components: vec![],
        }
    }

    pub(crate) fn project(&self, component: KeyPathComponent) -> Self {
        let mut components = self.components.clone();
        components.push(component);
        Self {
            root: self.root,
            components,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Body {
    pub(crate) entry: BlockId,
    pub(crate) blocks: Vec<BasicBlock>,
    pub(crate) locals: Vec<LocalDecl>,
    /// Expression-position control constructs: the construct's expr id →
    /// the block whose terminator branches into its arm blocks. Lowering
    /// lowers the construct FROM these blocks (value through the
    /// continuation) when the consuming statement's expression reaches it.
    pub(crate) scaffolds: FxHashMap<NodeID, BlockId>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BasicBlock {
    pub(crate) statements: Vec<LocatedStatement>,
    pub(crate) terminator: Terminator,
}

#[derive(Clone, Debug)]
pub(crate) struct LocatedStatement {
    pub(crate) kind: Statement,
    /// Drop/move results projected onto this statement by `ownership::elaborate_body_drops`,
    /// so lowering reads drop/move handling off the statement it is walking rather than
    /// looking it up in a side `OwnershipOutput` table keyed by program point.
    pub(crate) ownership: StatementOwnership,
}

/// Drop/move results the borrow checker records for a single MIR statement.
/// Empty until the ownership pass elaborates drops over the body.
#[derive(Debug, Default, Clone)]
pub(crate) struct StatementOwnership {
    /// For a `DropCandidate`: how lowering must elaborate the drop at this point
    /// (static / dead / conditional / open), plus the resolved key path it applies to.
    pub(crate) drop: Option<DropElaborationResult>,
    /// Key paths moved at this statement, so lowering can clear their drop flags.
    pub(crate) moves: Vec<crate::flow::Place>,
}

#[derive(Debug, Clone)]
pub(crate) struct DropElaborationResult {
    pub(crate) key_path: crate::flow::Place,
    pub(crate) kind: DropElaboration,
}

#[allow(dead_code)]
// Statements own the cloned HIR nodes they reference (the MIR is built once and reused), so
// kinds carrying an `Expr`/`Pattern` are inherently larger than the marker kinds. Boxing every
// node field would only add indirection to a build-once IR.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug)]
pub(crate) enum Statement {
    ScopeEnter {
        scope: ScopeId,
    },
    ScopeExit {
        scope: ScopeId,
    },
    StorageLive {
        id: NodeID,
        symbol: Symbol,
    },
    StorageDead {
        id: NodeID,
        symbol: Symbol,
    },
    Read {
        expr: Expr,
    },
    ConsumeValue {
        expr: Expr,
    },
    AssignmentRootUse {
        id: NodeID,
        ty: Ty,
        symbol: Symbol,
    },
    Bind {
        lhs: Pattern,
        type_annotation: Option<TypeAnnotation>,
        rhs: Option<Expr>,
        bindings: Vec<Local>,
    },
    Assign {
        lhs: Expr,
        rhs: Expr,
        target: Option<KeyPath>,
    },
    DropCandidate {
        target: DropTarget,
        key_path: Option<KeyPath>,
        reason: DropReason,
        /// The HIR node whose flow results elaborate this candidate: the
        /// scope's source block for `ScopeExit`, the jumping/assigning
        /// statement for `EarlyExit`/`AssignmentReplace`. Placement is
        /// structural; the flow checker fills `ownership.drop` afterwards.
        source: NodeID,
    },
    Call {
        callee: Expr,
        args: Vec<CallArg>,
        trailing_block: Option<Block>,
    },
    Perform {
        /// The whole `CallEffect` expression: the flow checker consumes its
        /// arguments here (their evaluation statements are plain reads).
        expr: Expr,
    },
    ReturnValue {
        expr: Expr,
        destination: ValueDestination,
    },
    ContinueValue {
        expr: Expr,
    },
    Function {
        owner: Option<Symbol>,
        captures_parent: bool,
        captures: Vec<CaptureSpec>,
        params: Vec<Parameter>,
        body: Box<Block>,
        /// For a named nested `func` declaration: the whole node, so the
        /// flow checker can apply its capture effects at this statement.
        /// Other function-like statements (closure values, methods, inits)
        /// apply theirs at their embedded consumption sites, or not at all.
        decl_func: Option<Box<crate::hir::Func>>,
    },
    Handling {
        stmt: Stmt,
        effect_name: Name,
        body: Box<Block>,
    },
    DeclBody {
        body: crate::hir::Body,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ValueDestination {
    /// A nested tail delivery (branch arm, block value): the value flows on
    /// within the function.
    Continuation,
    /// The body's own tail expression: the function's return value.
    /// Lowering treats it exactly like `Continuation` (CPS delivers to the
    /// same continuation); the flow checker provenance-checks it as a
    /// return.
    TailReturn,
    /// A source `return`.
    Return,
}

#[allow(dead_code)]
// Owns a cloned HIR `Expr` for the same reason as `Statement` (build-once MIR).
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug)]
pub(crate) enum DropTarget {
    Symbol { id: NodeID, symbol: Symbol },
    Expr(Expr),
}

// Drop reasons and elaborations are the flow checker's vocabulary; MIR
// carries them through unchanged.
pub use crate::flow::drops::{DropElaboration, DropReason};

#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) enum Terminator {
    #[default]
    Unset,
    Return,
    ReturnVoid,
    Jump(BlockId),
    Break,
    Continue,
    Branch {
        condition: Expr,
        then_block: BlockId,
        else_block: BlockId,
        /// An expression-position `if`: the arm blocks are analysis
        /// scaffolding (the value — and evaluation — rides the expression
        /// embedded in the enclosing statement, like a `Switch`'s arms).
        /// Statement-position branches own their arm content.
        in_expression: bool,
    },
    Switch {
        scrutinee: Expr,
        match_arms: Option<Vec<MatchArm>>,
        arms: Vec<BlockId>,
        default: Option<BlockId>,
    },
    Loop {
        condition: Option<Expr>,
        body_block: BlockId,
        exit_block: BlockId,
    },
}

#[derive(Clone, Copy, Debug)]
struct LoopTargets {
    continue_target: BlockId,
    break_target: BlockId,
    /// `scope_stack.len()` at loop entry: a `break`/`continue` leaves only
    /// the scopes at or above this depth, so its early-exit drops are
    /// target-relative instead of covering every enclosing scope.
    scope_depth: usize,
}

struct Builder<'types> {
    types: &'types TypeOutput,
    grades: crate::flow::grades::GradeView<'types>,
    blocks: Vec<BasicBlock>,
    scopes: Vec<Scope>,
    locals: Vec<LocalDecl>,
    local_by_symbol: FxHashMap<Symbol, Local>,
    scope_stack: Vec<ScopeFrame>,
    loop_stack: Vec<LoopTargets>,
    /// Whether this body's root-scope tail is the function's return value
    /// (true for function/top-level bodies; false for standalone match-arm
    /// bodies, whose tail delivers to the match join).
    root_tail_is_return: bool,
    scaffolds: FxHashMap<NodeID, BlockId>,
}

#[derive(Debug)]
struct ScopeFrame {
    id: ScopeId,
    /// The HIR block this scope was built from (`NodeID::SYNTHESIZED` for
    /// the top-level file scope): the `source` its drop candidates carry.
    source: NodeID,
    locals: Vec<(NodeID, Symbol)>,
    /// Root-scope locals with no `let` of their own — owned by-value
    /// parameters, whose storage is the caller's move: drop candidates at
    /// scope exit, but no StorageLive/StorageDead.
    param_likes: Vec<(NodeID, Symbol)>,
}

pub(crate) fn build_function(
    types: &TypeOutput,
    owner: Option<Symbol>,
    params: &[Parameter],
    block: &Block,
) -> Body {
    let mut builder = Builder::new(types);
    let entry = builder.new_block();
    let param_likes = builder.owned_param_locals(owner, params);
    let exit = builder.lower_body_scope(entry, block.id, param_likes, |builder, entry| {
        builder.lower_nodes(&block.body, entry, true, true)
    });
    builder.terminate_if_open(exit, Terminator::Return);
    builder.finish(entry)
}

/// Build an init's body: no owned params (self is constructed and
/// delivered, never dropped here), and the tail is not a semantic return —
/// the caller receives self, so no return-provenance applies to it.
pub(crate) fn build_init_body(types: &TypeOutput, block: &Block) -> Body {
    let mut builder = Builder::new(types);
    builder.root_tail_is_return = false;
    let entry = builder.new_block();
    let exit = builder.lower_body_scope(entry, block.id, vec![], |builder, entry| {
        builder.lower_nodes(&block.body, entry, true, false)
    });
    builder.terminate_if_open(exit, Terminator::Return);
    builder.finish(entry)
}

/// Match-arm payload binders that need release at arm exit, with their
/// types — the rest are pure aliases of the scrutinee's payload (the flow
/// checker's alias rule). Shared between the builder's arm bodies and
/// lowering's arm drop-stack seeding.
pub(crate) fn arm_release_binders(
    types: &TypeOutput,
    pattern: &Pattern,
) -> Vec<(NodeID, Symbol, Ty)> {
    let grades = crate::flow::grades::GradeView::new(types);
    pattern
        .collect_binders()
        .into_iter()
        .filter_map(|(id, symbol)| {
            let ty = types
                .local_tys
                .get(&symbol)
                .or_else(|| types.node_types.get(&id))?;
            grades.needs_drop(ty).then(|| (id, symbol, ty.clone()))
        })
        .collect()
}

/// Build a match arm's body as a standalone body: the arm's pattern
/// binders that need release are root-frame locals (drop candidates at
/// scope exit, no storage statements — like owned by-value parameters,
/// their storage is the scrutinee's).
pub(crate) fn build_arm_body(types: &TypeOutput, pattern: &Pattern, block: &Block) -> Body {
    let mut builder = Builder::new(types);
    builder.root_tail_is_return = false;
    let entry = builder.new_block();
    let binders = builder.arm_binder_locals(pattern);
    let exit = builder.lower_body_scope(entry, block.id, binders, |builder, entry| {
        builder.lower_nodes(&block.body, entry, true, false)
    });
    builder.terminate_if_open(exit, Terminator::Return);
    builder.finish(entry)
}

/// Build a top-level body (a file's roots, or several files' concatenated
/// for the combined `main` body).
pub(crate) fn build_nodes(types: &TypeOutput, nodes: &[Node]) -> Body {
    let mut builder = Builder::new(types);
    let entry = builder.new_block();
    let exit = builder.lower_scope(entry, NodeID::SYNTHESIZED, |builder, entry| {
        builder.lower_nodes(nodes, entry, true, true)
    });
    builder.terminate_if_open(exit, Terminator::Return);
    builder.finish(entry)
}

/// The nodes the synthetic `main` executes: every file's top-level
/// statements and non-func `let` declarations, in source order — the same
/// filter `lower_main` applies, shared so the flow checker analyzes and
/// annotates exactly the body lowering runs.
pub fn main_body_nodes<'a>(
    files: impl Iterator<Item = &'a crate::hir::HirFile>,
) -> Vec<Node> {
    let mut nodes = vec![];
    for file in files {
        for root in &file.roots {
            match root {
                Node::Stmt(_) => nodes.push(root.clone()),
                Node::Decl(decl) => {
                    if let DeclKind::Let { rhs: Some(rhs), .. } = &decl.kind
                        && !matches!(rhs.kind, ExprKind::Func(_))
                    {
                        nodes.push(root.clone());
                    }
                }
                _ => {}
            }
        }
    }
    nodes
}

/// One module's checkable bodies (functions, methods, closures, inits),
/// keyed by body block, plus the combined top-level `main` body: built
/// structurally BEFORE the flow pass, annotated by it, consumed by
/// lowering. Lowering still builds on miss (an inlined constant's nested
/// value blocks) as an unchecked fallback.
#[derive(Clone, Debug, Default)]
pub struct ModuleBodies {
    map: FxHashMap<NodeID, std::sync::Arc<Body>>,
    top_level: Option<std::sync::Arc<Body>>,
}

impl ModuleBodies {
    pub(crate) fn get(&self, block: NodeID) -> Option<std::sync::Arc<Body>> {
        self.map.get(&block).cloned()
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.map.len()
    }

    /// Mutable access for the flow checker's annotation passes (the store
    /// is unshared until lowering clones it out).
    pub(crate) fn get_mut(&mut self, block: NodeID) -> Option<&mut Body> {
        std::sync::Arc::get_mut(self.map.get_mut(&block)?)
    }

    /// The combined top-level `main` body (see `main_body_nodes`).
    pub(crate) fn top_level(&self) -> Option<std::sync::Arc<Body>> {
        self.top_level.clone()
    }

    pub(crate) fn set_top_level(&mut self, body: Body) {
        self.top_level = Some(std::sync::Arc::new(body));
    }
}

/// Enumerate and build every function-like body in a module's HIR:
/// `hir::Func` bodies (functions, methods, closures) and init bodies.
pub fn build_module_bodies<'a>(
    types: &TypeOutput,
    files: impl Iterator<Item = &'a crate::hir::HirFile>,
) -> ModuleBodies {
    use derive_visitor::{Drive, Visitor};

    struct Collect<'t> {
        types: &'t TypeOutput,
        bodies: ModuleBodies,
    }

    impl Visitor for Collect<'_> {
        fn visit(&mut self, item: &dyn std::any::Any, event: derive_visitor::Event) {
            if !matches!(event, derive_visitor::Event::Enter) {
                return;
            }
            if let Some(func) = item.downcast_ref::<crate::hir::Func>() {
                let owner = func.name.symbol().ok();
                let body = build_function(self.types, owner, &func.params, &func.body);
                self.bodies
                    .map
                    .insert(func.body.id, std::sync::Arc::new(body));
            }
            if let Some(decl) = item.downcast_ref::<Decl>()
                && let DeclKind::Init { body, .. } = &decl.kind
            {
                let built = build_init_body(self.types, body);
                self.bodies.map.insert(body.id, std::sync::Arc::new(built));
            }
        }
    }

    let mut collect = Collect {
        types,
        bodies: ModuleBodies::default(),
    };
    for file in files {
        for root in &file.roots {
            root.drive(&mut collect);
        }
    }
    collect.bodies
}

impl<'types> Builder<'types> {
    fn new(types: &'types TypeOutput) -> Self {
        Self {
            types,
            grades: crate::flow::grades::GradeView::new(types),
            blocks: vec![],
            scopes: vec![],
            locals: vec![],
            local_by_symbol: FxHashMap::default(),
            scope_stack: vec![],
            loop_stack: vec![],
            root_tail_is_return: true,
            scaffolds: FxHashMap::default(),
        }
    }

    /// The owned by-value parameters of a body: consumed arguments' drops
    /// ride the callee, so each is a scope local of the body's root frame.
    /// The same filter the flow checker's `seed_params` applies: borrows
    /// aren't locals, and `'heap`-carrying parameters are exempt (params
    /// neither acquire nor release the region ledger).
    fn owned_param_locals(
        &mut self,
        owner: Option<Symbol>,
        params: &[Parameter],
    ) -> Vec<(NodeID, Symbol)> {
        let scheme_params = owner
            .and_then(|owner| self.types.schemes.get(&owner))
            .and_then(|scheme| match &scheme.ty {
                Ty::Func(params, ..) => Some(params.clone()),
                _ => None,
            })
            .unwrap_or_default();
        let mut locals = vec![];
        for (index, param) in params.iter().enumerate() {
            let Ok(symbol) = param.name.symbol() else {
                continue;
            };
            let Some(ty) = param
                .ty
                .clone()
                .or_else(|| self.types.node_types.get(&param.id).cloned())
                .or_else(|| scheme_params.get(index).cloned())
            else {
                continue;
            };
            if self.grades.contains_borrowed(&ty) {
                continue;
            }
            if self.grades.needs_drop(&ty) && !self.grades.contains_object(&ty) {
                locals.push((param.id, symbol));
            }
        }
        locals
    }

    /// Match-arm payload binders that need release at arm exit — the rest
    /// are pure aliases of the scrutinee's payload (the flow checker's
    /// alias rule) with no ledger events of their own.
    fn arm_binder_locals(&mut self, pattern: &Pattern) -> Vec<(NodeID, Symbol)> {
        arm_release_binders(self.types, pattern)
            .into_iter()
            .map(|(id, symbol, _)| (id, symbol))
            .collect()
    }

    fn finish(self, entry: BlockId) -> Body {
        Body {
            entry,
            blocks: self.blocks,
            locals: self.locals,
            scaffolds: self.scaffolds,
        }
    }

    fn declare_local(&mut self, symbol: Symbol, ty: Option<Ty>, kind: LocalKind) -> Local {
        if let Some(local) = self.local_by_symbol.get(&symbol).copied() {
            return local;
        }
        let local = Local(self.locals.len());
        self.locals.push(LocalDecl {
            local,
            symbol,
            ty,
            kind,
        });
        self.local_by_symbol.insert(symbol, local);
        local
    }

    fn declare_symbol_local(&mut self, symbol: Symbol, kind: LocalKind) -> Local {
        let ty = self
            .types
            .schemes
            .get(&symbol)
            .map(|scheme| scheme.ty.clone());
        self.declare_local(symbol, ty, kind)
    }

    fn local_for_symbol(&mut self, symbol: Symbol) -> Local {
        self.local_by_symbol
            .get(&symbol)
            .copied()
            .unwrap_or_else(|| self.declare_symbol_local(symbol, LocalKind::UserLocal))
    }

    fn key_path_for_expr(&mut self, expr: &Expr) -> Option<KeyPath> {
        match &expr.kind {
            ExprKind::Variable(name) => {
                let symbol = name.symbol().ok()?;
                Some(KeyPath::root(self.local_for_symbol(symbol)))
            }
            ExprKind::Member(Some(receiver), ..) => {
                let field = stored_field_symbol(self.types, expr.member_resolution.as_ref())?;
                Some(
                    self.key_path_for_expr(receiver)?
                        .project(KeyPathComponent::Field(field)),
                )
            }
            _ => None,
        }
    }

    fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len());
        self.blocks.push(BasicBlock::default());
        id
    }

    fn lower_nodes(
        &mut self,
        nodes: &[Node],
        mut current: BlockId,
        mark_tail_exprs: bool,
        tail_exits: bool,
    ) -> BlockId {
        let last = nodes.len().saturating_sub(1);
        for (index, node) in nodes.iter().enumerate() {
            if self.is_terminated(current) {
                current = self.new_block();
            }
            let is_tail = mark_tail_exprs && index == last;
            let tail_expr = is_tail.then(|| tail_expr(node)).flatten();
            let tail_control_value = is_tail && node_is_value_control(node);
            current = self.lower_node(
                node,
                current,
                tail_expr.is_none() && !tail_control_value,
                is_tail && tail_exits,
            );
            if let Some(expr) = tail_expr {
                // Only the root scope's tail is the function's return value;
                // nested tails (branch arms, value blocks) deliver within it.
                let destination = if self.scope_stack.len() == 1 && self.root_tail_is_return {
                    ValueDestination::TailReturn
                } else {
                    ValueDestination::Continuation
                };
                self.push_statement(
                    current,
                    Statement::ReturnValue {
                        expr: expr.clone(),
                        destination,
                    },
                );
                // A tail delivery that leaves the function (a branch arm on
                // the function's tail path): the enclosing frames'
                // scope-exit drops must ride this path (their own exit
                // blocks are unreachable from here). Drop flags keep them
                // per-path correct. Expression-position deliveries stay
                // inside the function: no enclosing drops.
                if tail_exits {
                    self.emit_enclosing_scope_drops(current);
                }
            }
        }
        current
    }

    fn lower_node(
        &mut self,
        node: &Node,
        current: BlockId,
        consume_expr_value: bool,
        tail_exits: bool,
    ) -> BlockId {
        match node {
            Node::Decl(decl) => self.lower_decl(decl, current),
            Node::Stmt(Stmt {
                kind: StmtKind::Expr(Expr {
                    kind: ExprKind::Block(_),
                    ..
                }),
                ..
            }) if !consume_expr_value => current,
            Node::Stmt(Stmt {
                kind: StmtKind::Expr(expr),
                ..
            }) if !consume_expr_value => self.lower_expr(expr, current),
            Node::Stmt(stmt) => self.lower_stmt(stmt, current, consume_expr_value, tail_exits),
            Node::Expr(expr) => {
                let current = self.lower_expr(expr, current);
                if consume_expr_value {
                    self.push_statement(
                        current,
                        Statement::ConsumeValue {
                            expr: expr.clone(),
                        },
                    );
                }
                current
            }
        }
    }

    fn lower_decl(&mut self, decl: &Decl, current: BlockId) -> BlockId {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => {
                let function_owner = match (rhs.as_ref().map(|rhs| &rhs.kind), &lhs.kind) {
                    (Some(ExprKind::Func(_)), PatternKind::Bind(name)) => name.symbol().ok(),
                    _ => None,
                };
                let current = match rhs {
                    Some(Expr {
                        kind: ExprKind::Func(func),
                        ..
                    }) => {
                        self.push_statement(
                            current,
                            Statement::Function {
                                owner: function_owner,
                                captures_parent: false,
                                captures: func.captures.clone(),
                                params: func.params.clone(),
                                body: Box::new(func.body.clone()),
                                decl_func: None,
                            },
                        );
                        current
                    }
                    Some(rhs) => self.lower_expr(rhs, current),
                    None => current,
                };
                let mut bindings = vec![];
                for (id, symbol) in lhs.collect_binders() {
                    let local = self.declare_symbol_local(symbol, LocalKind::UserLocal);
                    bindings.push(local);
                    self.push_statement(current, Statement::StorageLive { id, symbol });
                    if let Some(scope) = self.scope_stack.last_mut() {
                        scope.locals.push((id, symbol));
                    }
                }
                self.push_statement(
                    current,
                    Statement::Bind {
                        lhs: lhs.clone(),
                        type_annotation: type_annotation.clone(),
                        rhs: rhs.clone(),
                        bindings,
                    },
                );
                current
            }
            DeclKind::Func(func) => {
                let owner = func.name.symbol().ok();
                self.push_statement(
                    current,
                    Statement::Function {
                        owner,
                        captures_parent: true,
                        captures: func.captures.clone(),
                        params: func.params.clone(),
                        body: Box::new(func.body.clone()),
                        decl_func: Some(Box::new(func.clone())),
                    },
                );
                current
            }
            DeclKind::Method { func, .. } => {
                let owner = func.name.symbol().ok();
                self.push_statement(
                    current,
                    Statement::Function {
                        owner,
                        captures_parent: true,
                        captures: func.captures.clone(),
                        params: func.params.clone(),
                        body: Box::new(func.body.clone()),
                        decl_func: None,
                    },
                );
                current
            }
            DeclKind::Init { params, body, .. } => {
                let owner = match &decl.kind {
                    DeclKind::Init { name, .. } => name.symbol().ok(),
                    _ => None,
                };
                self.push_statement(
                    current,
                    Statement::Function {
                        owner,
                        captures_parent: true,
                        captures: vec![],
                        params: params.clone(),
                        body: Box::new(body.clone()),
                        decl_func: None,
                    },
                );
                current
            }
            DeclKind::Struct { body, .. }
            | DeclKind::Enum { body, .. }
            | DeclKind::Protocol { body, .. }
            | DeclKind::Extend { body, .. } => {
                self.push_statement(current, Statement::DeclBody { body: body.clone() });
                current
            }
            DeclKind::Import(_)
            | DeclKind::Effect { .. }
            | DeclKind::Property { .. }
            | DeclKind::Associated { .. }
            | DeclKind::EnumVariant { .. }
            | DeclKind::FuncSignature(_)
            | DeclKind::MethodRequirement { .. }
            | DeclKind::TypeAlias(..) => current,
        }
    }

    fn lower_stmt(
        &mut self,
        stmt: &Stmt,
        current: BlockId,
        consume_expr_value: bool,
        tail_exits: bool,
    ) -> BlockId {
        match &stmt.kind {
            StmtKind::Expr(Expr {
                kind: ExprKind::Block(block),
                ..
            }) => self.lower_scope(current, block.id, |builder, current| {
                builder.lower_nodes(&block.body, current, false, false)
            }),
            StmtKind::Expr(expr) => {
                let current = self.lower_expr(expr, current);
                self.push_statement(
                    current,
                    Statement::ConsumeValue {
                        expr: expr.clone(),
                    },
                );
                current
            }
            StmtKind::Return(Some(expr)) => {
                let current = self.lower_expr(expr, current);
                self.push_statement(
                    current,
                    Statement::ReturnValue {
                        expr: expr.clone(),
                        destination: ValueDestination::Return,
                    },
                );
                self.emit_early_exit_drops(current, stmt.id, 0);
                self.terminate_if_open(current, Terminator::Return);
                current
            }
            StmtKind::Return(None) => {
                self.emit_early_exit_drops(current, stmt.id, 0);
                self.terminate_if_open(current, Terminator::ReturnVoid);
                current
            }
            StmtKind::Continue(Some(expr)) => {
                let current = self.lower_expr(expr, current);
                self.push_statement(
                    current,
                    Statement::ContinueValue {
                        expr: expr.clone(),
                    },
                );
                self.emit_early_exit_drops(current, stmt.id, self.loop_scope_depth());
                let terminator = self
                    .loop_stack
                    .last()
                    .map(|targets| Terminator::Jump(targets.continue_target))
                    .unwrap_or(Terminator::Continue);
                self.terminate_if_open(current, terminator);
                current
            }
            StmtKind::Continue(None) => {
                self.emit_early_exit_drops(current, stmt.id, self.loop_scope_depth());
                let terminator = self
                    .loop_stack
                    .last()
                    .map(|targets| Terminator::Jump(targets.continue_target))
                    .unwrap_or(Terminator::Continue);
                self.terminate_if_open(current, terminator);
                current
            }
            StmtKind::Break => {
                self.emit_early_exit_drops(current, stmt.id, self.loop_scope_depth());
                let terminator = self
                    .loop_stack
                    .last()
                    .map(|targets| Terminator::Jump(targets.break_target))
                    .unwrap_or(Terminator::Break);
                self.terminate_if_open(current, terminator);
                current
            }
            StmtKind::Assignment(lhs, rhs) => {
                let current = self.lower_expr(rhs, current);
                self.lower_assignment_lhs(lhs, current);
                let target_key_path = self.key_path_for_expr(lhs);
                // The old value's drop; the flow checker classifies it at
                // the pre-assignment state.
                self.push_statement(
                    current,
                    Statement::DropCandidate {
                        target: DropTarget::Expr((**lhs).clone()),
                        key_path: target_key_path.clone(),
                        reason: DropReason::AssignmentReplace,
                        source: stmt.id,
                    },
                );
                self.push_statement(
                    current,
                    Statement::Assign {
                        lhs: (**lhs).clone(),
                        rhs: (**rhs).clone(),
                        target: target_key_path,
                    },
                );
                current
            }
            StmtKind::If(condition, then_block, else_block) => self.lower_if(
                condition,
                then_block,
                else_block.as_ref(),
                current,
                !consume_expr_value,
                tail_exits,
                None,
            ),
            StmtKind::Loop(condition, body) => self.lower_loop(condition.as_ref(), body, current),
            StmtKind::Handling {
                effect_name, body, ..
            } => {
                self.push_statement(
                    current,
                    Statement::Handling {
                        stmt: stmt.clone(),
                        effect_name: effect_name.clone(),
                        body: Box::new(body.clone()),
                    },
                );
                current
            }
        }
    }

    fn lower_expr(&mut self, expr: &Expr, current: BlockId) -> BlockId {
        match &expr.kind {
            ExprKind::Variable(_) => {
                self.push_statement(current, Statement::Read { expr: expr.clone() });
                current
            }
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
                self.lower_exprs(items, current)
            }
            ExprKind::As(inner, _) => self.lower_expr(inner, current),
            ExprKind::Block(block) => self.lower_scope(current, block.id, |builder, current| {
                builder.lower_nodes(&block.body, current, true, false)
            }),
            ExprKind::Call {
                callee,
                args,
                trailing_block,
                ..
            } => {
                let mut current = self.lower_expr(callee, current);
                for arg in args {
                    current = self.lower_expr(&arg.value, current);
                }
                self.push_statement(
                    current,
                    Statement::Call {
                        callee: (**callee).clone(),
                        args: args.clone(),
                        trailing_block: trailing_block.clone(),
                    },
                );
                current
            }
            ExprKind::CallEffect { args, .. } => {
                let mut current = current;
                for arg in args {
                    current = self.lower_expr(&arg.value, current);
                }
                self.push_statement(current, Statement::Perform { expr: expr.clone() });
                current
            }
            ExprKind::Member(Some(receiver), ..) => {
                if stored_field_symbol(self.types, expr.member_resolution.as_ref()).is_some() {
                    self.push_statement(current, Statement::Read { expr: expr.clone() });
                    current
                } else {
                    self.lower_expr(receiver, current)
                }
            }
            ExprKind::Func(func) => {
                self.push_statement(
                    current,
                    Statement::Function {
                        owner: None,
                        captures_parent: false,
                        captures: func.captures.clone(),
                        params: func.params.clone(),
                        body: Box::new(func.body.clone()),
                        decl_func: None,
                    },
                );
                current
            }
            ExprKind::If(condition, then_block, else_block) => {
                // An expression-position `if` builds real blocks — a
                // `break`/`continue`/move inside an arm must be a CFG edge,
                // not text flattened into the current block. Lowering
                // lowers the arms from these blocks when the consuming
                // statement's expression reaches this construct; the arm
                // tails deliver its value through the continuation.
                self.lower_if(
                    condition,
                    then_block,
                    Some(else_block),
                    current,
                    true,
                    false,
                    Some(expr.id),
                )
            }
            ExprKind::Match(scrutinee, arms) => self.lower_match(expr.id, scrutinee, arms, current),
            ExprKind::RecordLiteral { fields, spread } => {
                let mut current = current;
                if let Some(spread) = spread {
                    current = self.lower_expr(spread, current);
                }
                for field in fields {
                    current = self.lower_expr(&field.value, current);
                }
                current
            }
            ExprKind::InlineIR(_)
            | ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_)
            | ExprKind::Constructor(_)
            | ExprKind::RowVariable(_)
            | ExprKind::Member(None, ..) => current,
        }
    }

    fn lower_exprs(&mut self, exprs: &[Expr], mut current: BlockId) -> BlockId {
        for expr in exprs {
            current = self.lower_expr(expr, current);
        }
        current
    }

    fn lower_assignment_lhs(&mut self, expr: &Expr, current: BlockId) {
        match &expr.kind {
            ExprKind::Variable(_) => {}
            ExprKind::Member(Some(receiver), ..)
                if stored_field_symbol(self.types, expr.member_resolution.as_ref()).is_some() =>
            {
                self.lower_assignment_root(receiver, current);
            }
            _ => {
                self.lower_expr(expr, current);
            }
        }
    }

    fn lower_assignment_root(&mut self, expr: &Expr, current: BlockId) {
        match &expr.kind {
            ExprKind::Variable(name) => {
                if let Ok(symbol) = name.symbol() {
                    self.push_statement(
                        current,
                        Statement::AssignmentRootUse {
                            id: expr.id,
                            ty: expr.ty.clone(),
                            symbol,
                        },
                    );
                }
            }
            ExprKind::Member(Some(receiver), ..) => self.lower_assignment_root(receiver, current),
            _ => {
                self.lower_expr(expr, current);
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_if(
        &mut self,
        condition: &Expr,
        then_block: &Block,
        else_block: Option<&Block>,
        current: BlockId,
        mark_tail_exprs: bool,
        tail_exits: bool,
        scaffold: Option<NodeID>,
    ) -> BlockId {
        let current = self.lower_expr(condition, current);
        let then_id = self.new_block();
        let else_id = self.new_block();
        let join_id = self.new_block();
        if let Some(expr_id) = scaffold {
            self.scaffolds.insert(expr_id, current);
        }
        self.terminate_if_open(
            current,
            Terminator::Branch {
                condition: condition.clone(),
                then_block: then_id,
                else_block: else_id,
                in_expression: scaffold.is_some(),
            },
        );

        let then_exit = self.lower_scope(then_id, then_block.id, |builder, then_id| {
            builder.lower_nodes(&then_block.body, then_id, mark_tail_exprs, tail_exits)
        });
        self.terminate_if_open(then_exit, Terminator::Jump(join_id));

        let else_exit = if let Some(else_block) = else_block {
            self.lower_scope(else_id, else_block.id, |builder, else_id| {
                builder.lower_nodes(&else_block.body, else_id, mark_tail_exprs, tail_exits)
            })
        } else {
            else_id
        };
        self.terminate_if_open(else_exit, Terminator::Jump(join_id));

        join_id
    }

    fn lower_loop(&mut self, condition: Option<&Expr>, body: &Block, current: BlockId) -> BlockId {
        let header_id = self.new_block();
        let body_id = self.new_block();
        let exit_id = self.new_block();

        self.terminate_if_open(current, Terminator::Jump(header_id));
        if let Some(condition) = condition {
            let condition_exit = self.lower_expr(condition, header_id);
            self.terminate_if_open(
                condition_exit,
                Terminator::Loop {
                    condition: Some(condition.clone()),
                    body_block: body_id,
                    exit_block: exit_id,
                },
            );
        } else {
            self.terminate_if_open(
                header_id,
                Terminator::Loop {
                    condition: None,
                    body_block: body_id,
                    exit_block: exit_id,
                },
            );
        }

        self.loop_stack.push(LoopTargets {
            continue_target: header_id,
            break_target: exit_id,
            scope_depth: self.scope_stack.len(),
        });
        let body_exit = self.lower_scope(body_id, body.id, |builder, body_id| {
            builder.lower_nodes(&body.body, body_id, false, false)
        });
        self.loop_stack.pop();
        self.terminate_if_open(body_exit, Terminator::Jump(header_id));

        exit_id
    }

    fn lower_match(
        &mut self,
        expr_id: NodeID,
        scrutinee: &Expr,
        arms: &[MatchArm],
        current: BlockId,
    ) -> BlockId {
        let current = self.lower_expr(scrutinee, current);
        let join_id = self.new_block();
        let arm_blocks: Vec<_> = arms.iter().map(|_| self.new_block()).collect();
        self.scaffolds.insert(expr_id, current);
        self.terminate_if_open(
            current,
            Terminator::Switch {
                scrutinee: scrutinee.clone(),
                match_arms: Some(arms.to_vec()),
                arms: arm_blocks.clone(),
                default: None,
            },
        );

        for (arm, arm_id) in arms.iter().zip(arm_blocks) {
            let arm_exit = self.lower_scope(arm_id, arm.body.id, |builder, arm_id| {
                builder.lower_pattern_binders(&arm.pattern, arm_id);
                builder.lower_nodes(&arm.body.body, arm_id, true, false)
            });
            self.terminate_if_open(arm_exit, Terminator::Jump(join_id));
        }

        join_id
    }

    fn lower_pattern_binders(&mut self, pattern: &Pattern, current: BlockId) {
        for (id, symbol) in pattern.collect_binders() {
            self.declare_symbol_local(symbol, LocalKind::UserLocal);
            self.push_statement(current, Statement::StorageLive { id, symbol });
            if let Some(scope) = self.scope_stack.last_mut() {
                scope.locals.push((id, symbol));
            }
        }
    }

    fn push_statement(&mut self, block: BlockId, statement: Statement) {
        self.blocks[block.0].statements.push(LocatedStatement {
            kind: statement,
            ownership: StatementOwnership::default(),
        });
    }

    /// The scope depth a `break`/`continue` unwinds to: the innermost
    /// loop's entry depth (0 outside any loop, where the jump is an error
    /// anyway).
    fn loop_scope_depth(&self) -> usize {
        self.loop_stack
            .last()
            .map(|targets| targets.scope_depth)
            .unwrap_or(0)
    }

    /// Push a scope frame (parent = the enclosing frame, if any), lower
    /// `lower` inside it, emit its exit drops, pop.
    fn lower_scope(
        &mut self,
        current: BlockId,
        source: NodeID,
        lower: impl FnOnce(&mut Self, BlockId) -> BlockId,
    ) -> BlockId {
        self.lower_body_scope(current, source, vec![], lower)
    }

    /// `lower_scope` for a body's root frame, seeding its owned by-value
    /// parameters as param-like locals.
    fn lower_body_scope(
        &mut self,
        current: BlockId,
        source: NodeID,
        param_likes: Vec<(NodeID, Symbol)>,
        lower: impl FnOnce(&mut Self, BlockId) -> BlockId,
    ) -> BlockId {
        let parent = self.scope_stack.last().map(|scope| scope.id);
        let scope = self.new_scope(parent);
        self.scope_stack.push(ScopeFrame {
            id: scope,
            source,
            locals: vec![],
            param_likes,
        });
        self.push_statement(current, Statement::ScopeEnter { scope });
        let exit = lower(self, current);
        let exit = self.emit_scope_exit(exit);
        self.scope_stack.pop();
        exit
    }

    fn new_scope(&mut self, parent: Option<ScopeId>) -> ScopeId {
        let id = ScopeId(self.scopes.len());
        self.scopes.push(Scope { id, parent });
        id
    }

    /// Scope-exit drop candidates for every frame ENCLOSING the current
    /// innermost one, innermost-first — used at tail deliveries inside
    /// branch arms, whose normal exit blocks are unreachable.
    fn emit_enclosing_scope_drops(&mut self, current: BlockId) {
        if self.scope_stack.len() < 2 {
            return;
        }
        for index in (0..self.scope_stack.len() - 1).rev() {
            self.emit_frame_drop_candidates(current, index, false);
        }
    }

    /// One frame's scope-exit drop candidates: `let` locals in reverse
    /// declaration order (with storage teardown when `with_storage`), then
    /// param-like locals (candidates only — their storage is the caller's).
    fn emit_frame_drop_candidates(&mut self, current: BlockId, frame: usize, with_storage: bool) {
        let source = self.scope_stack[frame].source;
        let locals = self.scope_stack[frame].locals.clone();
        let param_likes = self.scope_stack[frame].param_likes.clone();
        for (id, symbol) in locals.iter().rev().copied() {
            let key_path = Some(KeyPath::root(self.local_for_symbol(symbol)));
            self.push_statement(
                current,
                Statement::DropCandidate {
                    target: DropTarget::Symbol { id, symbol },
                    key_path,
                    reason: DropReason::ScopeExit,
                    source,
                },
            );
            if with_storage {
                self.push_statement(current, Statement::StorageDead { id, symbol });
            }
        }
        for (id, symbol) in param_likes.iter().rev().copied() {
            let key_path = Some(KeyPath::root(self.local_for_symbol(symbol)));
            self.push_statement(
                current,
                Statement::DropCandidate {
                    target: DropTarget::Symbol { id, symbol },
                    key_path,
                    reason: DropReason::ScopeExit,
                    source,
                },
            );
        }
    }

    fn emit_scope_exit(&mut self, current: BlockId) -> BlockId {
        // A block already terminated by `break`/`continue`/`return` never
        // reaches its scope exit: the early-exit candidates on that statement
        // carry the drops. Emitting them here would execute them (statements
        // run before the terminator) and double-free moved locals.
        if self.is_terminated(current) {
            return current;
        }
        let Some(frame) = self.scope_stack.last() else {
            return current;
        };
        let scope = frame.id;
        self.emit_frame_drop_candidates(current, self.scope_stack.len() - 1, true);
        self.push_statement(current, Statement::ScopeExit { scope });
        current
    }

    /// Early-exit drop candidates for a `return`/`break`/`continue`: the
    /// locals (and param-like locals) of exactly the scopes between the
    /// jump and its target
    /// (`from_depth` — 0 for `return`, the loop's entry depth for
    /// `break`/`continue`), innermost scope first.
    fn emit_early_exit_drops(&mut self, current: BlockId, source: NodeID, from_depth: usize) {
        let locals: Vec<(NodeID, Symbol)> = self
            .scope_stack
            .iter()
            .skip(from_depth)
            .rev()
            .flat_map(|scope| {
                scope
                    .locals
                    .iter()
                    .rev()
                    .chain(scope.param_likes.iter().rev())
                    .copied()
            })
            .collect();
        for (id, symbol) in locals {
            let key_path = Some(KeyPath::root(self.local_for_symbol(symbol)));
            self.push_statement(
                current,
                Statement::DropCandidate {
                    target: DropTarget::Symbol { id, symbol },
                    key_path,
                    reason: DropReason::EarlyExit,
                    source,
                },
            );
        }
    }

    fn terminate_if_open(&mut self, block: BlockId, terminator: Terminator) {
        if matches!(self.blocks[block.0].terminator, Terminator::Unset) {
            self.blocks[block.0].terminator = terminator;
        }
    }

    fn is_terminated(&self, block: BlockId) -> bool {
        self.blocks[block.0].terminator != Terminator::Unset
    }
}

fn tail_expr(node: &Node) -> Option<&Expr> {
    match node {
        Node::Expr(expr) => Some(expr),
        Node::Stmt(stmt) => match &stmt.kind {
            StmtKind::Expr(expr) => Some(expr),
            _ => None,
        },
        _ => None,
    }
}

fn node_is_value_control(node: &Node) -> bool {
    matches!(
        node,
        Node::Stmt(Stmt {
            kind: StmtKind::If(_, _, Some(_)),
            ..
        })
    )
}

impl Body {
    #[cfg(test)]
    pub(crate) fn render(&self) -> String {
        let mut out = String::new();
        out.push_str("locals:\n");
        for local in &self.locals {
            out.push_str(&format!(
                "  {} {}{}\n",
                render_local(local.local),
                render_local_kind(local.kind),
                format!(" {}", local.symbol)
            ));
        }
        for (index, block) in self.blocks.iter().enumerate() {
            out.push_str(&format!("bb{index}:\n"));
            for statement in &block.statements {
                out.push_str("  ");
                out.push_str(&render_statement(&statement.kind));
                out.push('\n');
            }
            out.push_str("  ");
            out.push_str(&render_terminator(&block.terminator));
            out.push('\n');
        }
        out
    }
}

#[cfg(test)]
fn render_local(local: Local) -> String {
    format!("%{}", local.0)
}

#[cfg(test)]
fn render_local_kind(kind: LocalKind) -> &'static str {
    match kind {
        LocalKind::Param => "param",
        LocalKind::UserLocal => "local",
        LocalKind::CompilerTemp => "temp",
        LocalKind::Return => "return",
    }
}

#[cfg(test)]
fn render_key_path(key_path: &KeyPath) -> String {
    let mut rendered = render_local(key_path.root);
    for component in &key_path.components {
        match component {
            KeyPathComponent::Field(field) => rendered.push_str(&format!(".{field}")),
        }
    }
    rendered
}

#[cfg(test)]
fn render_statement(statement: &Statement) -> String {
    match statement {
        Statement::ScopeEnter { scope } => format!("scope_enter s{}", scope.0),
        Statement::ScopeExit { scope } => format!("scope_exit s{}", scope.0),
        Statement::StorageLive { symbol, .. } => format!("storage_live {symbol}"),
        Statement::StorageDead { symbol, .. } => format!("storage_dead {symbol}"),
        Statement::Read { .. } => "read".into(),
        Statement::ConsumeValue { .. } => "consume".into(),
        Statement::AssignmentRootUse { symbol, .. } => format!("assignment_root {symbol}"),
        Statement::Bind { .. } => "bind".into(),
        Statement::Assign { target, .. } => match target {
            Some(target) => format!("assign {}", render_key_path(target)),
            None => "assign <unresolved>".into(),
        },
        Statement::DropCandidate {
            key_path, reason, ..
        } => match key_path {
            Some(target) => {
                format!("drop_candidate {} {:?}", render_key_path(target), reason)
            }
            None => format!("drop_candidate <unresolved> {:?}", reason),
        },
        Statement::Call { .. } => "call".into(),
        Statement::Perform { .. } => "perform".into(),
        Statement::ReturnValue { .. } => "return_value".into(),
        Statement::ContinueValue { .. } => "continue_value".into(),
        Statement::Function { .. } => "function".into(),
        Statement::Handling { .. } => "handling".into(),
        Statement::DeclBody { .. } => "decl_body".into(),
    }
}

#[cfg(test)]
fn render_terminator(terminator: &Terminator) -> String {
    match terminator {
        Terminator::Unset => "unset".into(),
        Terminator::Return => "return".into(),
        Terminator::ReturnVoid => "return_void".into(),
        Terminator::Jump(target) => format!("goto bb{}", target.0),
        Terminator::Break => "break".into(),
        Terminator::Continue => "continue".into(),
        Terminator::Branch {
            then_block,
            else_block,
            ..
        } => format!("branch bb{} bb{}", then_block.0, else_block.0),
        Terminator::Switch { arms, default, .. } => {
            let arms = arms
                .iter()
                .map(|block| format!("bb{}", block.0))
                .collect::<Vec<_>>()
                .join(", ");
            match default {
                Some(default) => format!("switch [{arms}] default bb{}", default.0),
                None => format!("switch [{arms}]"),
            }
        }
        Terminator::Loop {
            body_block,
            exit_block,
            ..
        } => format!("loop bb{} bb{}", body_block.0, exit_block.0),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        compiling::driver::{Driver, DriverConfig, Source},
        types::TypeOutput,
    };

    fn with_first_func_mir<R>(source: &str, f: impl FnOnce(&Body) -> R) -> R {
        let source = format!("// no-core\n{source}");
        let resolved = Driver::new_bare(
            vec![Source::from(source.as_str())],
            DriverConfig::new("OwnershipMirTest"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve");
        assert!(
            !resolved.has_errors(),
            "unexpected diagnostics: {:?}",
            resolved.diagnostics()
        );
        for ast in resolved.phase.asts.values() {
            // The MIR builder is tested for structure, not types, so it needn't be
            // type-checked: give every expression a placeholder type and lower to HIR.
            let types = placeholder_types(&ast.roots);
            let hir = crate::hir::build::build_file(ast, &types);
            for node in &hir.roots {
                let Node::Decl(decl) = node else { continue };
                let DeclKind::Func(func) = &decl.kind else {
                    if let DeclKind::Let {
                        rhs: Some(expr), ..
                    } = &decl.kind
                        && let ExprKind::Func(func) = &expr.kind
                    {
                        let body = build_function(&types, None, &func.params, &func.body);
                        return f(&body);
                    }
                    continue;
                };
                let body = build_function(&types, None, &func.params, &func.body);
                return f(&body);
            }
        }
        panic!("expected a function declaration");
    }

    /// A `TypeOutput` giving every AST expression a placeholder type — enough for
    /// the (strict) HIR lowerer to run without type-checking, so MIR-builder tests
    /// can exercise structure on programs that need not be type-correct.
    fn placeholder_types(roots: &[crate::node::Node]) -> TypeOutput {
        use derive_visitor::{Drive, Visitor};
        #[derive(Default)]
        struct Collect {
            types: TypeOutput,
        }
        impl Visitor for Collect {
            fn visit(&mut self, item: &dyn std::any::Any, event: derive_visitor::Event) {
                if matches!(event, derive_visitor::Event::Enter)
                    && let Some(expr) = item.downcast_ref::<crate::node_kinds::expr::Expr>()
                {
                    self.types
                        .node_types
                        .insert(expr.id, crate::types::ty::Ty::Error);
                }
            }
        }
        let mut collect = Collect::default();
        for root in roots {
            root.drive(&mut collect);
        }
        collect.types
    }

    fn symbol_named(names: &FxHashMap<Symbol, String>, name: &str) -> Symbol {
        names
            .iter()
            .find_map(|(symbol, candidate)| (candidate == name).then_some(*symbol))
            .unwrap_or_else(|| panic!("missing symbol named {name}"))
    }

    fn resolved_names(source: &str) -> FxHashMap<Symbol, String> {
        let source = format!("// no-core\n{source}");
        let resolved = Driver::new_bare(
            vec![Source::from(source.as_str())],
            DriverConfig::new("OwnershipMirTest"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve");
        resolved.phase.resolved_names.symbol_names
    }

    #[test]
    fn builds_if_else_branch_and_join_blocks() {
        with_first_func_mir(
            "
            func f(flag) {
                if flag {
                    1
                } else {
                    2
                }
            }
            ",
            |body| {
                assert_eq!(body.entry.index(), 0);
                assert!(body.blocks.len() >= 4, "{body:#?}");
                assert!(
                    body.blocks
                        .iter()
                        .any(|block| matches!(block.terminator, Terminator::Branch { .. })),
                    "{body:#?}"
                );
                assert!(
                    body.blocks
                        .iter()
                        .any(|block| matches!(block.terminator, Terminator::Jump(_))),
                    "{body:#?}"
                );
            },
        );
    }

    #[test]
    fn expression_position_if_builds_scaffold_branch_blocks() {
        // A `break`/`continue`/move inside an expression-position arm must
        // be a CFG edge — the arms cannot flatten into the current block.
        with_first_func_mir(
            "
            func f(c) {
                let x = if (c) { 1 } else { 2 }
                x
            }
            ",
            |body| {
                assert!(
                    body.blocks.iter().any(|block| matches!(
                        block.terminator,
                        Terminator::Branch {
                            in_expression: true,
                            ..
                        }
                    )),
                    "{body:#?}"
                );
            },
        );
    }

    /// The early-exit drop candidates on each block, as (symbol, reason)
    /// pairs per block.
    fn early_exit_candidates(body: &Body) -> Vec<Vec<Symbol>> {
        body.blocks
            .iter()
            .map(|block| {
                block
                    .statements
                    .iter()
                    .filter_map(|statement| match &statement.kind {
                        Statement::DropCandidate {
                            reason: DropReason::EarlyExit,
                            target: DropTarget::Symbol { symbol, .. },
                            ..
                        } => Some(*symbol),
                        _ => None,
                    })
                    .collect()
            })
            .collect()
    }

    #[test]
    fn break_drop_candidates_cover_only_scopes_inside_the_loop() {
        // `outer` is declared before the loop and survives the break; only
        // `inner` (a loop-body local) drops on the break path. `return`
        // still unwinds every scope.
        let source = "
            func f(flag) {
                let outer = 1
                loop flag {
                    let inner = 2
                    if flag {
                        break
                    }
                    if inner {
                        return 3
                    }
                }
                outer
            }
        ";
        let names = resolved_names(source);
        let outer = symbol_named(&names, "outer");
        let inner = symbol_named(&names, "inner");
        with_first_func_mir(source, |body| {
            let per_block = early_exit_candidates(body);
            let break_path: Vec<&Vec<Symbol>> = per_block
                .iter()
                .filter(|symbols| symbols.contains(&inner) && !symbols.contains(&outer))
                .collect();
            assert!(
                !break_path.is_empty(),
                "break drops the loop-local only: {per_block:?}\n{body:#?}"
            );
            let return_path: Vec<&Vec<Symbol>> = per_block
                .iter()
                .filter(|symbols| symbols.contains(&inner) && symbols.contains(&outer))
                .collect();
            assert!(
                !return_path.is_empty(),
                "return drops every enclosing scope's locals: {per_block:?}\n{body:#?}"
            );
        });
    }

    #[test]
    fn builds_match_switch_and_arm_blocks() {
        with_first_func_mir(
            "
            enum E {
                case a
                case b
            }

            func f(e) {
                match e {
                    .a -> 1,
                    .b -> 2
                }
            }
            ",
            |body| {
                assert!(
                    body.blocks.iter().any(|block| matches!(
                        block.terminator,
                        Terminator::Switch { ref arms, .. } if arms.len() == 2
                    )),
                    "{body:#?}"
                );
            },
        );
    }

    #[test]
    fn builds_loop_back_edge() {
        with_first_func_mir(
            "
            func f(flag) {
                loop flag {
                    flag
                }
            }
            ",
            |body| {
                let has_back_edge = body.blocks.iter().enumerate().any(|(block_index, block)| {
                    matches!(
                        block.terminator,
                        Terminator::Jump(target) if target.index() <= block_index
                    )
                });
                assert!(has_back_edge, "{body:#?}");
            },
        );
    }

    #[test]
    fn records_user_locals_for_binders() {
        let source = "
            func f() {
                let first = 1
                let second = first
                second
            }
        ";
        let names = resolved_names(source);
        let first = symbol_named(&names, "first");
        let second = symbol_named(&names, "second");
        with_first_func_mir(source, |body| {
            let local_symbols: Vec<_> = body.locals.iter().map(|local| local.symbol).collect();
            assert!(local_symbols.contains(&first), "{body:#?}");
            assert!(local_symbols.contains(&second), "{body:#?}");
            assert!(
                body.locals
                    .iter()
                    .all(|local| matches!(local.kind, LocalKind::UserLocal)),
                "{body:#?}"
            );
        });
    }

    #[test]
    fn renders_drop_candidates_with_key_paths() {
        let source = "
            func f() {
                let first = 1
                first
            }
        ";
        let rendered = with_first_func_mir(source, |body| body.render());

        assert!(rendered.contains("locals:\n"), "{rendered}");
        assert!(rendered.contains("  %0 local "), "{rendered}");
        assert!(
            rendered.contains("drop_candidate %0 ScopeExit"),
            "{rendered}"
        );
    }


    fn destinations(body: &Body) -> Vec<ValueDestination> {
        body.blocks
            .iter()
            .flat_map(|block| &block.statements)
            .filter_map(|statement| match statement.kind {
                Statement::ReturnValue { destination, .. } => Some(destination),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn distinguishes_source_return_from_root_tail_value() {
        // `return 1` is a source return; the trailing `2` is the root tail —
        // the function's return value.
        let source = "
            func f(flag) {
                if flag {
                    return 1
                }
                2
            }
        ";
        with_first_func_mir(source, |body| {
            let destinations = destinations(body);
            assert!(
                destinations.contains(&ValueDestination::Return),
                "{body:#?}"
            );
            assert!(
                destinations.contains(&ValueDestination::TailReturn),
                "{body:#?}"
            );
        });
    }

    #[test]
    fn nested_tail_deliveries_are_continuations_not_returns() {
        // A tail-position if's arm tails deliver within the function — they
        // are not the return value itself (no provenance check applies).
        let source = "
            func f(flag) {
                if flag {
                    2
                } else {
                    3
                }
            }
        ";
        with_first_func_mir(source, |body| {
            let destinations = destinations(body);
            assert!(
                destinations.contains(&ValueDestination::Continuation),
                "{body:#?}"
            );
            assert!(
                !destinations.contains(&ValueDestination::TailReturn),
                "{body:#?}"
            );
        });
    }
}
