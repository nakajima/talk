use rustc_hash::FxHashMap;

use crate::{
    flow::{Place, place_for_expr},
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{func::CaptureSpec, type_annotation::TypeAnnotation},
    typed_ast::{
        Block, CallArg, Decl, DeclKind, Expr, ExprKind, MatchArm, Node, Parameter, Pattern,
        PatternKind, Stmt, StmtKind,
    },
    types::{TypeOutput, ty::Ty},
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

#[derive(Clone, Debug)]
pub(crate) struct Body {
    pub(crate) entry: BlockId,
    pub(crate) blocks: Vec<BasicBlock>,
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
    pub(crate) terminator_ownership: TerminatorOwnership,
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
    /// Runtime ownership transfers at this statement, recorded by flow.
    /// Lowering clears drop flags from this list; it must not re-derive moves
    /// from expression syntax.
    pub(crate) moves: Vec<Place>,
}

#[derive(Debug, Default, Clone)]
pub(crate) struct TerminatorOwnership {
    /// Runtime ownership transfers at this terminator, recorded by flow.
    pub(crate) moves: Vec<Place>,
}

#[derive(Debug, Clone)]
pub(crate) struct DropElaborationResult {
    /// The elaborated place, for symbol-rooted candidates; `None` for
    /// temp candidates (temps have no place — the statement's embedded
    /// `Temp` expression is the value).
    pub(crate) key_path: Option<Place>,
    pub(crate) kind: DropElaboration,
}

#[allow(dead_code)]
// Statements own the cloned typed nodes they reference (the MIR is built once and reused), so
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
    /// A place read, operand form: flow-only (lowering skips it — the
    /// evaluation rides the consuming statement's expression). One per
    /// node of a non-place chain (boundary checks only, `place: None`);
    /// a place-shaped read carries its place and stops the chain.
    Read {
        node: NodeID,
        ty: Ty,
        place: Option<Place>,
        /// Set by the CFG flow pass when this node's value is consumed by its
        /// consuming statement (the use is checked there, as an owned use);
        /// default-false is load-bearing for per-file error bodies.
        consumes: bool,
        pack: Option<crate::types::output::ExistentialPack>,
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
    },
    Assign {
        lhs: Expr,
        rhs: Expr,
        target: Option<Place>,
    },
    DropCandidate {
        target: DropTarget,
        key_path: Option<Place>,
        reason: DropReason,
        /// The typed node whose flow results elaborate this candidate: the
        /// scope's source block for `ScopeExit`, the jumping/assigning
        /// statement for `EarlyExit`/`AssignmentReplace`. Placement is
        /// structural; the flow checker fills `ownership.drop` afterwards.
        source: NodeID,
    },
    Call {
        /// The whole call expression: lowering evaluates it HERE, binding
        /// the result to `temp` for the consuming statement's `Temp` read.
        expr: Expr,
        callee: Expr,
        args: Vec<CallArg>,
        trailing_block: Option<Block>,
        temp: u32,
        result_ty: Ty,
    },
    Perform {
        /// The whole `CallEffect` expression: the flow checker consumes its
        /// arguments here (their evaluation statements are plain reads),
        /// and lowering evaluates it here, binding `temp` for the
        /// consuming statement's read.
        expr: Expr,
        temp: u32,
        result_ty: Ty,
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
        decl_func: Option<Box<crate::typed_ast::Func>>,
    },
    Handling {
        stmt: Stmt,
        effect_name: Name,
        body: Box<Block>,
    },
    DeclBody {
        body: crate::typed_ast::Body,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ValueDestination {
    /// A nested tail delivery into an enclosing construct's join temp.
    /// The flow checker records the delivered value's provenance there.
    Continuation(u32),
    /// A nested tail delivery to the current continuation without binding a temp.
    Fallthrough,
    /// A value-producing block's tail: bind the value to this temp, then
    /// continue through the block's scope-exit statements and enclosing use.
    TempThenContinue(u32),
    /// The body's own tail expression: the function's return value.
    /// Lowering delivers it to the current continuation; the flow checker
    /// provenance-checks it as a return.
    TailReturn,
    /// A source `return`.
    Return,
}

#[allow(dead_code)]
// Owns a cloned typed `Expr` for the same reason as `Statement` (build-once MIR).
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
    },
    Switch {
        scrutinee: Expr,
        match_arms: Option<Vec<MatchArm>>,
        arms: Vec<BlockId>,
        default: Option<BlockId>,
        /// The construct's join block, recorded by the builder (deriving
        /// it from arm terminators fails when an arm tail is itself
        /// control flow).
        join: BlockId,
        /// The construct's value as an operand: arm tails deliver to the
        /// join continuation, which binds this temp for the join block's
        /// statements (where the source expression's node now reads
        /// `ExprKind::Temp`).
        result: Option<(u32, Ty)>,
    },
    Loop {
        condition: Option<Expr>,
        header_block: BlockId,
        body_block: BlockId,
        exit_block: BlockId,
    },
    /// An effect-handling scope: the handler body's blocks are analysis
    /// scaffolding in the enclosing body (the body may run zero or more
    /// times — the two edges are the tree walk's clone+merge); evaluation
    /// rides the `Handling` statement's capability closure, which lowering
    /// builds from these same blocks.
    Handler {
        body_block: BlockId,
        join: BlockId,
    },
}

#[derive(Clone, Copy, Debug)]
struct HandlerTargets {
    /// The handling construct's join block: `continue v` (a resume) ends
    /// the handler-body path here — never at an enclosing loop's header.
    join: BlockId,
    /// `scope_stack.len()` at handler entry, for the resume path's
    /// target-relative early-exit drops.
    scope_depth: usize,
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

#[derive(derive_visitor::VisitorMut)]
#[visitor(Expr(enter))]
struct TempSubstituter<'a> {
    subs: &'a FxHashMap<NodeID, u32>,
}

impl TempSubstituter<'_> {
    fn enter_expr(&mut self, expr: &mut Expr) {
        if let Some(&temp) = self.subs.get(&expr.id) {
            expr.kind = ExprKind::Temp(temp);
        }
    }
}

struct Builder<'types> {
    types: &'types TypeOutput,
    grades: crate::flow::grades::GradeView<'types>,
    blocks: Vec<BasicBlock>,
    scopes: Vec<Scope>,
    scope_stack: Vec<ScopeFrame>,
    loop_stack: Vec<LoopTargets>,
    handler_stack: Vec<HandlerTargets>,
    /// Temporaries minted for flattened constructs, and the source nodes
    /// they replace in later statement/terminator embeddings.
    next_temp: u32,
    temp_subs: FxHashMap<NodeID, u32>,
    /// The join temps of the value-producing constructs currently being
    /// lowered, innermost last: an arm tail's `Continuation` delivery
    /// names the enclosing construct's temp.
    continuation_temps: Vec<u32>,
    /// Depth of value-construct arms with a pending JOIN (if/match arms):
    /// their tail deliveries are continuations into the join, never the
    /// function return. A tail-position BLOCK scope is join-free — its
    /// inner tail is still the function's return.
    join_depth: usize,
    /// Result temps for value-producing block expressions currently being
    /// flattened into the surrounding MIR body.
    block_value_temps: Vec<u32>,
    /// Whether this body's root-scope tail is the function's return value
    /// (true for function/top-level bodies; false for standalone match-arm
    /// bodies, whose tail delivers to the match join).
    root_tail_is_return: bool,
    scaffolds: FxHashMap<NodeID, BlockId>,
}

#[derive(Debug)]
struct ScopeFrame {
    id: ScopeId,
    /// The typed block this scope was built from (`NodeID::SYNTHESIZED` for
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
/// checker's alias rule).
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
    files: impl Iterator<Item = &'a crate::typed_ast::TypedFile>,
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
/// lowering.
#[derive(Clone, Debug, Default)]
pub(crate) struct ModuleBodies {
    map: FxHashMap<NodeID, std::sync::Arc<Body>>,
    top_level: Option<std::sync::Arc<Body>>,
}

/// Flow-checked MIR for one module. This is the compiler seam after type
/// checking: callers cannot build or mutate the structural body store directly.
#[derive(Clone, Debug, Default)]
pub(crate) struct CheckedMir {
    bodies: ModuleBodies,
}

impl CheckedMir {
    pub(crate) fn get(&self, block: NodeID) -> Option<std::sync::Arc<Body>> {
        self.bodies.get(block)
    }

    pub(crate) fn top_level(&self) -> Option<std::sync::Arc<Body>> {
        self.bodies.top_level()
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.bodies.len()
    }
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

/// Enumerate and build every function-like body in a module's typed tree:
/// function/method/closure bodies and init bodies.
pub(crate) fn build_checked(
    program: &mut crate::compiling::typed_program::TypedProgram,
    module_id: crate::compiling::module::ModuleId,
) -> (
    CheckedMir,
    crate::flow::FlowFacts,
    Vec<crate::diagnostic::AnyDiagnostic>,
) {
    let mut bodies = build_module_bodies(program.types(), program.files().values());
    let (flow, diagnostics) = if program.is_empty() {
        bodies.set_top_level(build_nodes(program.types(), &[]));
        (crate::flow::FlowFacts::default(), vec![])
    } else {
        let (files, types) = program.files_and_types_mut();
        crate::flow::check_flow(files, &mut bodies, types, module_id)
    };
    (CheckedMir { bodies }, flow, diagnostics)
}

fn build_module_bodies<'a>(
    types: &TypeOutput,
    files: impl Iterator<Item = &'a crate::typed_ast::TypedFile>,
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
            if let Some(func) = item.downcast_ref::<crate::typed_ast::Func>() {
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
            scope_stack: vec![],
            loop_stack: vec![],
            handler_stack: vec![],
            next_temp: 0,
            temp_subs: FxHashMap::default(),
            continuation_temps: vec![],
            join_depth: 0,
            block_value_temps: vec![],
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
            // GENERIC params classify like owned ones: the flow runs once
            // over the generic body and each specialization elides the
            // exit drop when its instantiation doesn't need one.
            let generic = matches!(ty, Ty::Param(_) | Ty::Proj(..));
            if (generic || self.grades.needs_drop(&ty)) && !self.grades.contains_object(&ty) {
                locals.push((param.id, symbol));
            }
        }
        locals
    }

    fn finish(self, entry: BlockId) -> Body {
        Body {
            entry,
            blocks: self.blocks,
            scaffolds: self.scaffolds,
        }
    }

    /// Build the expression that reads a flattened temporary. The enclosing
    /// statement records these structurally and emits `TemporaryEnd` drop
    /// candidates at its own completion point.
    fn temp_expr(&self, id: NodeID, span: crate::span::Span, temp: u32, ty: Ty) -> Expr {
        Expr {
            id,
            kind: ExprKind::Temp(temp),
            span,
            ownership: Default::default(),
            ty,
            member_resolution: None,
            instantiation: None,
            existential_pack: None,
        }
    }

    /// Materialize a droppable rvalue aggregate (array literal, tuple,
    /// variant/record construction) used as a call operand into its own
    /// temp. Parameters borrow by default (ADR 0018), so call operands are
    /// no longer implicitly consumed by the callee: the caller needs a
    /// `TemporaryEnd` candidate to free a merely-read operand. Consumed
    /// operands still classify `Dead`. `'heap`-carrying values are exempt:
    /// the region ledger owns their lifetime.
    fn temp_rvalue_aggregate(&mut self, expr: &Expr, current: BlockId, temp_drops: &mut Vec<Expr>) {
        if !matches!(
            expr.kind,
            ExprKind::LiteralArray(_)
                | ExprKind::Tuple(_)
                | ExprKind::Con { .. }
                | ExprKind::RecordLiteral { .. }
        ) {
            return;
        }
        let ty = expr.ty.clone();
        let generic = matches!(ty, Ty::Param(_) | Ty::Proj(..));
        if (!generic && !self.grades.needs_drop(&ty)) || self.grades.contains_object(&ty) {
            return;
        }
        let temp = self.next_temp;
        self.next_temp += 1;
        self.push_statement(
            current,
            Statement::ReturnValue {
                expr: expr.clone(),
                destination: ValueDestination::TempThenContinue(temp),
            },
        );
        self.temp_subs.insert(expr.id, temp);
        temp_drops.push(self.temp_expr(expr.id, expr.span, temp, ty));
    }

    /// Emit `TemporaryEnd` drop candidates for the current statement's temps
    /// (reverse creation order). Skipped when the block already terminated:
    /// exits consume their value, and unreachable candidates have no register
    /// to read.
    fn emit_temp_drops(&mut self, current: BlockId, temps: &mut Vec<Expr>) {
        let pending = std::mem::take(temps);
        if self.is_terminated(current) {
            return;
        }
        for temp_expr in pending.into_iter().rev() {
            let source = temp_expr.id;
            self.push_statement(
                current,
                Statement::DropCandidate {
                    target: DropTarget::Expr(temp_expr),
                    key_path: None,
                    reason: DropReason::TemporaryEnd,
                    source,
                },
            );
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
            let mut temp_drops = vec![];
            current = self.lower_node(
                node,
                current,
                tail_expr.is_none() && !tail_control_value,
                is_tail && tail_exits,
                &mut temp_drops,
            );
            // Temp drops precede the delivery/exit statements: the exit
            // machinery reads its scope-exit candidates adjacently, and a
            // consumed temp's candidate is Dead regardless of order
            // (consumption is static, the set completes before annotation).
            self.emit_temp_drops(current, &mut temp_drops);
            if let Some(expr) = tail_expr {
                // Only the root scope's tail is the function's return value;
                // nested tails (branch arms, value blocks) deliver within it.
                let destination = if let Some(temp) = self.continuation_temps.last().copied() {
                    ValueDestination::Continuation(temp)
                } else if let Some(temp) = self.block_value_temps.last().copied() {
                    ValueDestination::TempThenContinue(temp)
                } else if self.root_tail_is_return && self.join_depth == 0 {
                    ValueDestination::TailReturn
                } else {
                    ValueDestination::Fallthrough
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
        temp_drops: &mut Vec<Expr>,
    ) -> BlockId {
        match node {
            Node::Decl(decl) => self.lower_decl(decl, current, temp_drops),
            Node::Stmt(Stmt {
                kind:
                    StmtKind::Expr(Expr {
                        kind: ExprKind::Block(_),
                        ..
                    }),
                ..
            }) if !consume_expr_value => current,
            Node::Stmt(Stmt {
                kind: StmtKind::Expr(expr),
                ..
            }) if !consume_expr_value => self.lower_expr(expr, current, temp_drops),
            Node::Stmt(stmt) => {
                self.lower_stmt(stmt, current, consume_expr_value, tail_exits, temp_drops)
            }
            Node::Expr(expr) => {
                let current = self.lower_expr(expr, current, temp_drops);
                if consume_expr_value {
                    self.push_statement(current, Statement::ConsumeValue { expr: expr.clone() });
                }
                current
            }
        }
    }

    fn lower_decl(&mut self, decl: &Decl, current: BlockId, temp_drops: &mut Vec<Expr>) -> BlockId {
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
                    Some(rhs) => self.lower_expr(rhs, current, temp_drops),
                    None => current,
                };
                for (id, symbol) in lhs.collect_binders() {
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
        temp_drops: &mut Vec<Expr>,
    ) -> BlockId {
        match &stmt.kind {
            StmtKind::Expr(Expr {
                kind: ExprKind::Block(block),
                ..
            }) => self.lower_scope(current, block.id, |builder, current| {
                builder.lower_nodes(&block.body, current, consume_expr_value, tail_exits)
            }),
            StmtKind::Expr(expr) => {
                let current = self.lower_expr(expr, current, temp_drops);
                self.push_statement(current, Statement::ConsumeValue { expr: expr.clone() });
                current
            }
            StmtKind::Return(Some(expr)) => {
                let current = self.lower_expr(expr, current, temp_drops);
                self.emit_temp_drops(current, temp_drops);
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
                // `continue v` is a RESUME: the handler-body path ends at
                // the handling construct's join, never at a loop header.
                let current = self.lower_expr(expr, current, temp_drops);
                self.emit_temp_drops(current, temp_drops);
                self.push_statement(current, Statement::ContinueValue { expr: expr.clone() });
                if let Some(handler) = self.handler_stack.last().copied() {
                    self.emit_early_exit_drops(current, stmt.id, handler.scope_depth);
                    self.terminate_if_open(current, Terminator::Jump(handler.join));
                    return current;
                }
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
                let current = self.lower_expr(rhs, current, temp_drops);
                self.lower_assignment_lhs(lhs, current, temp_drops);
                let target_key_path = place_for_expr(lhs);
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
                temp_drops,
            ),
            StmtKind::Loop(condition, body) => {
                self.lower_loop(condition.as_ref(), body, current, temp_drops)
            }
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
                // The handler body gets real CFG blocks (scaffolding: the
                // capability closure's content lowers from them; the two
                // edges are the may-execute clone+merge for the checker).
                self.scaffolds.insert(stmt.id, current);
                let body_id = self.new_block();
                let join_id = self.new_block();
                self.terminate_if_open(
                    current,
                    Terminator::Handler {
                        body_block: body_id,
                        join: join_id,
                    },
                );
                self.handler_stack.push(HandlerTargets {
                    join: join_id,
                    scope_depth: self.scope_stack.len(),
                });
                // The handler body becomes a closure: enclosing loops are
                // not jump targets from inside it — a break/continue here
                // must surface as Terminator::Break/Continue (which
                // lowering diagnoses), not a jump into the enclosing CFG.
                let enclosing_loops = std::mem::take(&mut self.loop_stack);
                let body_exit = self.lower_scope(body_id, body.id, |builder, body_id| {
                    builder.lower_nodes(&body.body, body_id, true, false)
                });
                self.loop_stack = enclosing_loops;
                self.handler_stack.pop();
                self.terminate_if_open(body_exit, Terminator::Jump(join_id));
                join_id
            }
        }
    }

    fn lower_expr(&mut self, expr: &Expr, current: BlockId, temp_drops: &mut Vec<Expr>) -> BlockId {
        match &expr.kind {
            ExprKind::Variable(_) => {
                self.push_reads(expr, current);
                current
            }
            ExprKind::LiteralArray(items)
            | ExprKind::Tuple(items)
            | ExprKind::Con { args: items, .. } => self.lower_exprs(items, current, temp_drops),
            ExprKind::Block(block) => {
                let temp = self.next_temp;
                self.next_temp += 1;
                let result_ty = expr
                    .existential_pack
                    .as_ref()
                    .map(|pack| pack.payload.clone())
                    .or_else(|| self.types.node_types.get(&expr.id).cloned())
                    .unwrap_or(Ty::Error);
                temp_drops.push(self.temp_expr(expr.id, expr.span, temp, result_ty.clone()));
                self.temp_subs.insert(expr.id, temp);
                let delivers_value = block.body.last().is_some_and(node_delivers_tail_value);
                self.block_value_temps.push(temp);
                let exit = self.lower_scope(current, block.id, |builder, current| {
                    builder.lower_nodes(&block.body, current, true, false)
                });
                self.block_value_temps.pop();
                if !delivers_value && !self.is_terminated(exit) {
                    self.push_statement(
                        exit,
                        Statement::ReturnValue {
                            expr: Expr {
                                id: expr.id,
                                kind: ExprKind::Tuple(vec![]),
                                span: expr.span,
                                ownership: Default::default(),
                                ty: result_ty,
                                member_resolution: None,
                                instantiation: None,
                                existential_pack: None,
                            },
                            destination: ValueDestination::TempThenContinue(temp),
                        },
                    );
                }
                exit
            }
            ExprKind::Call {
                callee,
                args,
                trailing_block,
                ..
            } => {
                let mut current = self.lower_expr(callee, current, temp_drops);
                // An rvalue aggregate receiver (`[1, 2].show()`) is a call
                // operand like any argument.
                if let ExprKind::Member(Some(receiver), ..) = &callee.kind {
                    self.temp_rvalue_aggregate(receiver, current, temp_drops);
                }
                for arg in args {
                    current = self.lower_expr(&arg.value, current, temp_drops);
                    self.temp_rvalue_aggregate(&arg.value, current, temp_drops);
                }
                let temp = self.next_temp;
                self.next_temp += 1;
                // The temp holds the RAW result: a pack coercion on this
                // node applies at the Temp read, so the pre-pack payload
                // type is the value's type here.
                let result_ty = expr
                    .existential_pack
                    .as_ref()
                    .map(|pack| pack.payload.clone())
                    .or_else(|| self.types.node_types.get(&expr.id).cloned())
                    .unwrap_or(Ty::Error);
                temp_drops.push(self.temp_expr(expr.id, expr.span, temp, result_ty.clone()));
                self.push_statement(
                    current,
                    Statement::Call {
                        expr: expr.clone(),
                        callee: (**callee).clone(),
                        args: args.clone(),
                        trailing_block: trailing_block.clone(),
                        temp,
                        result_ty,
                    },
                );
                // Later embeddings of this call read its temp.
                self.temp_subs.insert(expr.id, temp);
                // A trailing block runs inside the callee, zero or more
                // times: scaffold blocks with may-execute edges, keyed by
                // the block's own id (the closure lowerer's handle).
                if let Some(block) = trailing_block {
                    self.scaffolds.insert(block.id, current);
                    let body_id = self.new_block();
                    let join_id = self.new_block();
                    self.terminate_if_open(
                        current,
                        Terminator::Handler {
                            body_block: body_id,
                            join: join_id,
                        },
                    );
                    // Like a handler body: the trailing block is a closure,
                    // so enclosing loops are not jump targets from inside.
                    let enclosing_loops = std::mem::take(&mut self.loop_stack);
                    let body_exit = self.lower_scope(body_id, block.id, |builder, body_id| {
                        builder.lower_nodes(&block.body, body_id, true, false)
                    });
                    self.loop_stack = enclosing_loops;
                    self.terminate_if_open(body_exit, Terminator::Jump(join_id));
                    return join_id;
                }
                current
            }
            ExprKind::CallEffect { args, .. } => {
                let mut current = current;
                for arg in args {
                    current = self.lower_expr(&arg.value, current, temp_drops);
                }
                let temp = self.next_temp;
                self.next_temp += 1;
                let result_ty = expr
                    .existential_pack
                    .as_ref()
                    .map(|pack| pack.payload.clone())
                    .or_else(|| self.types.node_types.get(&expr.id).cloned())
                    .unwrap_or(Ty::Error);
                temp_drops.push(self.temp_expr(expr.id, expr.span, temp, result_ty.clone()));
                self.push_statement(
                    current,
                    Statement::Perform {
                        expr: expr.clone(),
                        temp,
                        result_ty,
                    },
                );
                self.temp_subs.insert(expr.id, temp);
                current
            }
            ExprKind::Proj(..) => {
                self.push_reads(expr, current);
                current
            }
            ExprKind::Member(Some(receiver), ..) => self.lower_expr(receiver, current, temp_drops),
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
            ExprKind::Match(scrutinee, arms) => {
                self.lower_match(expr.id, scrutinee, arms, current, temp_drops)
            }
            ExprKind::RecordLiteral { fields, spread } => {
                let mut current = current;
                if let Some(spread) = spread {
                    current = self.lower_expr(spread, current, temp_drops);
                }
                for field in fields {
                    current = self.lower_expr(&field.value, current, temp_drops);
                }
                current
            }
            ExprKind::InlineIR(_)
            | ExprKind::Lit(_)
            | ExprKind::Constructor(_)
            | ExprKind::Temp(_)
            | ExprKind::Member(None, ..) => current,
        }
    }

    fn lower_exprs(
        &mut self,
        exprs: &[Expr],
        mut current: BlockId,
        temp_drops: &mut Vec<Expr>,
    ) -> BlockId {
        for expr in exprs {
            current = self.lower_expr(expr, current, temp_drops);
        }
        current
    }

    fn lower_assignment_lhs(&mut self, expr: &Expr, current: BlockId, temp_drops: &mut Vec<Expr>) {
        match &expr.kind {
            ExprKind::Variable(_) => {}
            ExprKind::Proj(receiver, ..) => {
                self.lower_assignment_root(receiver, current, temp_drops);
            }
            _ => {
                self.lower_expr(expr, current, temp_drops);
            }
        }
    }

    fn lower_assignment_root(&mut self, expr: &Expr, current: BlockId, temp_drops: &mut Vec<Expr>) {
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
            ExprKind::Member(Some(receiver), ..) | ExprKind::Proj(receiver, ..) => {
                self.lower_assignment_root(receiver, current, temp_drops)
            }
            _ => {
                self.lower_expr(expr, current, temp_drops);
            }
        }
    }

    fn lower_if(
        &mut self,
        condition: &Expr,
        then_block: &Block,
        else_block: Option<&Block>,
        current: BlockId,
        mark_tail_exprs: bool,
        tail_exits: bool,
        _temp_drops: &mut Vec<Expr>,
    ) -> BlockId {
        let mut condition_temp_drops = vec![];
        let current = self.lower_expr(condition, current, &mut condition_temp_drops);
        let then_id = self.new_block();
        let else_id = self.new_block();
        let join_id = self.new_block();
        let mut lowered_condition = condition.clone();
        self.substitute_temps_expr(&mut lowered_condition);
        self.emit_temp_drops(current, &mut condition_temp_drops);
        self.terminate_if_open(
            current,
            Terminator::Branch {
                condition: lowered_condition,
                then_block: then_id,
                else_block: else_id,
            },
        );

        self.join_depth += 1;
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
        self.join_depth -= 1;

        join_id
    }

    fn lower_loop(
        &mut self,
        condition: Option<&Expr>,
        body: &Block,
        current: BlockId,
        _temp_drops: &mut Vec<Expr>,
    ) -> BlockId {
        let header_id = self.new_block();
        let body_id = self.new_block();
        let exit_id = self.new_block();

        self.terminate_if_open(current, Terminator::Jump(header_id));
        if let Some(condition) = condition {
            let mut condition_temp_drops = vec![];
            let condition_exit = self.lower_expr(condition, header_id, &mut condition_temp_drops);
            let mut lowered_condition = condition.clone();
            self.substitute_temps_expr(&mut lowered_condition);
            self.emit_temp_drops(condition_exit, &mut condition_temp_drops);
            self.terminate_if_open(
                condition_exit,
                Terminator::Loop {
                    condition: Some(lowered_condition),
                    header_block: header_id,
                    body_block: body_id,
                    exit_block: exit_id,
                },
            );
        } else {
            self.terminate_if_open(
                header_id,
                Terminator::Loop {
                    condition: None,
                    header_block: header_id,
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
        temp_drops: &mut Vec<Expr>,
    ) -> BlockId {
        let current = self.lower_expr(scrutinee, current, temp_drops);
        let join_id = self.new_block();
        let arm_blocks: Vec<_> = arms.iter().map(|_| self.new_block()).collect();
        self.scaffolds.insert(expr_id, current);
        // The match's value flows arm-tail → join continuation → this
        // temp, which the consuming statement (in the join block) reads.
        let temp = self.next_temp;
        self.next_temp += 1;
        self.temp_subs.insert(expr_id, temp);
        let result_ty = self
            .types
            .existential_packs
            .get(&expr_id)
            .map(|pack| pack.payload.clone())
            .or_else(|| self.types.node_types.get(&expr_id).cloned())
            .unwrap_or(Ty::Error);
        temp_drops.push(self.temp_expr(expr_id, scrutinee.span, temp, result_ty.clone()));
        let mut scrutinee_sub = scrutinee.clone();
        self.substitute_temps_expr(&mut scrutinee_sub);
        self.terminate_if_open(
            current,
            Terminator::Switch {
                scrutinee: scrutinee_sub,
                match_arms: Some(arms.to_vec()),
                arms: arm_blocks.clone(),
                default: None,
                join: join_id,
                result: Some((temp, result_ty)),
            },
        );

        self.continuation_temps.push(temp);
        self.join_depth += 1;
        for (arm, arm_id) in arms.iter().zip(arm_blocks) {
            let arm_exit = self.lower_scope(arm_id, arm.body.id, |builder, arm_id| {
                builder.lower_pattern_binders(&arm.pattern, arm_id);
                builder.lower_nodes(&arm.body.body, arm_id, true, false)
            });
            self.terminate_if_open(arm_exit, Terminator::Jump(join_id));
        }
        self.join_depth -= 1;
        self.continuation_temps.pop();

        join_id
    }

    fn lower_pattern_binders(&mut self, pattern: &Pattern, current: BlockId) {
        for (id, symbol) in pattern.collect_binders() {
            self.push_statement(current, Statement::StorageLive { id, symbol });
            if let Some(scope) = self.scope_stack.last_mut() {
                scope.locals.push((id, symbol));
            }
        }
    }

    /// Emit `Read` statements for a place-shaped expression: one carrying
    /// the place when the whole chain is one; otherwise one boundary-only
    /// read per chain node down to the first place-shaped suffix or the
    /// opaque base (whose interior rides its own statements) — the shape
    /// of the old expression walk.
    fn push_reads(&mut self, expr: &Expr, current: BlockId) {
        let mut e = expr;
        loop {
            let place = crate::flow::place_for_expr(e);
            let is_place = place.is_some();
            self.push_statement(
                current,
                Statement::Read {
                    node: e.id,
                    ty: e.ty.clone(),
                    place,
                    consumes: false,
                    pack: e.existential_pack.clone(),
                },
            );
            if is_place {
                return;
            }
            match &e.kind {
                ExprKind::Proj(receiver, ..) | ExprKind::Member(Some(receiver), ..) => {
                    e = receiver;
                }
                _ => return,
            }
        }
    }

    fn push_statement(&mut self, block: BlockId, statement: Statement) {
        let mut statement = statement;
        self.substitute_temps(&mut statement);
        self.blocks[block.0].statements.push(LocatedStatement {
            kind: statement,
            ownership: StatementOwnership::default(),
        });
    }

    /// Rewrite embedded expressions so nodes standing for flattened
    /// constructs read their temps. Handler/trailing/function payload
    /// copies are left alone because they lower from their own checked
    /// MIR body or scaffold, not from the enclosing operand bridge.
    fn substitute_temps(&self, statement: &mut Statement) {
        if self.temp_subs.is_empty() {
            return;
        }
        let mut subs = TempSubstituter {
            subs: &self.temp_subs,
        };
        use derive_visitor::DriveMut;
        match statement {
            Statement::ConsumeValue { expr }
            | Statement::ReturnValue { expr, .. }
            | Statement::ContinueValue { expr }
            | Statement::Perform { expr, .. } => expr.drive_mut(&mut subs),
            Statement::Bind { rhs: Some(rhs), .. } => rhs.drive_mut(&mut subs),
            Statement::Assign { lhs, rhs, .. } => {
                lhs.drive_mut(&mut subs);
                rhs.drive_mut(&mut subs);
            }
            Statement::DropCandidate {
                target: DropTarget::Expr(expr),
                ..
            } => expr.drive_mut(&mut subs),
            Statement::Call {
                expr, callee, args, ..
            } => {
                expr.drive_mut(&mut subs);
                callee.drive_mut(&mut subs);
                for arg in args.iter_mut() {
                    arg.value.drive_mut(&mut subs);
                }
            }
            _ => {}
        }
    }

    fn substitute_temps_expr(&self, expr: &mut Expr) {
        if self.temp_subs.is_empty() {
            return;
        }
        use derive_visitor::DriveMut;
        expr.drive_mut(&mut TempSubstituter {
            subs: &self.temp_subs,
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
            let key_path = Some(Place::root(symbol));
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
            let key_path = Some(Place::root(symbol));
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
            let key_path = Some(Place::root(symbol));
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
    let expr = match node {
        Node::Expr(expr) => Some(expr),
        Node::Stmt(stmt) => match &stmt.kind {
            StmtKind::Expr(expr) => Some(expr),
            _ => None,
        },
        _ => None,
    }?;
    // A tail-position BLOCK is not an embeddable value expression: it
    // lowers as a real scope (its lets/moves/drops must be CFG facts —
    // an embedded copy would hide them from flow) and its own inner
    // tail delivers the value.
    if matches!(expr.kind, ExprKind::Block(_)) {
        return None;
    }
    Some(expr)
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

fn node_delivers_tail_value(node: &Node) -> bool {
    tail_expr(node).is_some()
        || node_is_value_control(node)
        || matches!(
            node,
            Node::Stmt(Stmt {
                kind: StmtKind::Expr(Expr {
                    kind: ExprKind::Block(_),
                    ..
                }),
                ..
            })
        )
}

impl Body {
    #[cfg(test)]
    pub(crate) fn render(&self) -> String {
        let mut out = String::new();
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
fn render_key_path(key_path: &Place) -> String {
    let mut rendered = format!("{}", key_path.root);
    for field in &key_path.fields {
        rendered.push_str(&format!(".{field}"));
    }
    rendered
}

#[cfg(test)]
pub(crate) fn render_statement(statement: &Statement) -> String {
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
        Statement::Call { temp, .. } => format!("call -> t{temp}"),
        Statement::Perform { .. } => "perform".into(),
        Statement::ReturnValue { .. } => "return_value".into(),
        Statement::ContinueValue { .. } => "continue_value".into(),
        Statement::Function { .. } => "function".into(),
        Statement::Handling { .. } => "handling".into(),
        Statement::DeclBody { .. } => "decl_body".into(),
    }
}

#[cfg(test)]
pub(crate) fn render_terminator(terminator: &Terminator) -> String {
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
        Terminator::Handler { body_block, join } => {
            format!("handler bb{} join bb{}", body_block.0, join.0)
        }
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
            header_block,
            body_block,
            exit_block,
            ..
        } => format!(
            "loop header bb{} body bb{} exit bb{}",
            header_block.0, body_block.0, exit_block.0
        ),
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
            // type-checked: give every expression a placeholder type and build the typed tree.
            let types = placeholder_types(&ast.roots);
            let typed_file = crate::compiling::typed_program::build::build_file(ast, &types);
            for node in &typed_file.roots {
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
    /// the strict typed-tree builder to run without type-checking, so MIR-builder tests
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
    fn expression_position_if_builds_scaffold_switch_blocks() {
        // A `break`/`continue`/move inside an expression-position arm must
        // be a CFG edge — the arms cannot flatten into the current block.
        // Expression-`if` desugars to a boolean `match`, so the scaffold
        // materializes as a `Switch` registered for the embedded expression.
        with_first_func_mir(
            "
            func f(c) {
                let x = if (c) { 1 } else { 2 }
                x
            }
            ",
            |body| {
                assert!(
                    body.blocks
                        .iter()
                        .any(|block| matches!(block.terminator, Terminator::Switch { .. })),
                    "{body:#?}"
                );
                assert!(!body.scaffolds.is_empty(), "{body:#?}");
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
    fn records_storage_lifetimes_for_binders() {
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
            let live: Vec<_> = body
                .blocks
                .iter()
                .flat_map(|block| &block.statements)
                .filter_map(|statement| match statement.kind {
                    Statement::StorageLive { symbol, .. } => Some(symbol),
                    _ => None,
                })
                .collect();
            assert!(live.contains(&first), "{body:#?}");
            assert!(live.contains(&second), "{body:#?}");
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

        // The candidate's key path is the binder's place (symbol-rooted,
        // like the flow checker's), not "<unresolved>".
        assert!(rendered.contains("ScopeExit"), "{rendered}");
        assert!(
            !rendered.contains("drop_candidate <unresolved>"),
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
    fn nested_tail_deliveries_are_fallthrough_not_returns() {
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
                destinations.contains(&ValueDestination::Fallthrough),
                "{body:#?}"
            );
            assert!(
                !destinations.contains(&ValueDestination::TailReturn),
                "{body:#?}"
            );
        });
    }
}
