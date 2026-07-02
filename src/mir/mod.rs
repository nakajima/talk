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
        ty::{Perm, Ty},
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

// The ownership checker uses StatementId as coordinates for facts:
//  - recording ownership facts at exact statement locations,
//  - building CFG edges between statement points,
//  - tying StorageLive, Move, Borrow, Assign, DropCandidate, etc. facts to a stable point in a MIR body.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct StatementId(pub(crate) usize);

impl StatementId {
    #[allow(dead_code)]
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

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum KeyPathComponent {
    Field(Symbol),
    TupleField(u32),
    VariantPayload { variant: Symbol, index: u32 },
    DerefBorrow,
    Index(Local),
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

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ValueUse {
    Copy(KeyPath),
    Move(KeyPath),
    Borrow { kind: Perm, target: KeyPath },
    Constant(NodeID),
    Function(Symbol),
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AggregateKind {
    Tuple,
    Record,
    Struct(Symbol),
    Variant {
        enum_symbol: Symbol,
        variant: Symbol,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Rvalue {
    Use(ValueUse),
    Borrow {
        kind: Perm,
        target: KeyPath,
    },
    Aggregate {
        kind: AggregateKind,
        fields: Vec<ValueUse>,
    },
    FieldRead {
        base: ValueUse,
        field: Symbol,
    },
    InlineIr {
        source: NodeID,
        operands: Vec<ValueUse>,
    },
    ExistentialPack {
        payload: ValueUse,
        protocol: Symbol,
        witnesses: Vec<ValueUse>,
    },
    Closure {
        source: NodeID,
        captures: Vec<KeyPath>,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct Body {
    pub(crate) owner: Option<Symbol>,
    pub(crate) entry: BlockId,
    pub(crate) blocks: Vec<BasicBlock>,
    pub(crate) scopes: Vec<Scope>,
    pub(crate) locals: Vec<LocalDecl>,
    #[allow(dead_code)]
    pub(crate) return_local: Option<Local>,
    use_counts: FxHashMap<Symbol, usize>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BasicBlock {
    pub(crate) statements: Vec<LocatedStatement>,
    pub(crate) terminator: Terminator,
}

#[derive(Clone, Debug)]
pub(crate) struct LocatedStatement {
    pub(crate) point: StatementId,
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
    pub(crate) moves: Vec<crate::ownership::KeyPath>,
}

#[derive(Debug, Clone)]
pub(crate) struct DropElaborationResult {
    pub(crate) key_path: crate::ownership::KeyPath,
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
        value: Option<ValueUse>,
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
        value: Option<Rvalue>,
    },
    Assign {
        lhs: Expr,
        rhs: Expr,
        target: Option<KeyPath>,
        value: Option<Rvalue>,
    },
    DropCandidate {
        target: DropTarget,
        key_path: Option<KeyPath>,
        reason: DropReason,
    },
    Call {
        callee: Expr,
        args: Vec<CallArg>,
        trailing_block: Option<Block>,
        trailing_body: Option<Box<Body>>,
    },
    Perform,
    ReturnValue {
        expr: Expr,
        value: Option<ValueUse>,
        destination: ValueDestination,
    },
    ContinueValue {
        expr: Expr,
        value: Option<ValueUse>,
    },
    Function {
        owner: Option<Symbol>,
        captures_parent: bool,
        captures: Vec<CaptureSpec>,
        params: Vec<Parameter>,
        body: Box<Block>,
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
    Continuation,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DropReason {
    ScopeExit,
    AssignmentReplace,
    EarlyExit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DropElaboration {
    /// initialized and not moved. Lowering may emit the drop/free unconditionally.
    Static,
    /// already moved/uninitialized. Lowering must not drop it.
    Dead,
    /// maybe initialized. Needs a runtime drop flag.
    Conditional,
    /// partially moved, usually an aggregate where some subpath moved. Needs more precise/dynamic drop handling.
    Open,
}

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
}

struct Builder<'types> {
    types: &'types TypeOutput,
    owner: Option<Symbol>,
    blocks: Vec<BasicBlock>,
    scopes: Vec<Scope>,
    locals: Vec<LocalDecl>,
    local_by_symbol: FxHashMap<Symbol, Local>,
    return_local: Option<Local>,
    scope_stack: Vec<ScopeFrame>,
    next_point: usize,
    use_counts: FxHashMap<Symbol, usize>,
    loop_stack: Vec<LoopTargets>,
}

#[derive(Debug)]
struct ScopeFrame {
    id: ScopeId,
    locals: Vec<(NodeID, Symbol)>,
}

pub(crate) fn build_block(types: &TypeOutput, block: &Block) -> Body {
    build_function(types, None, block)
}

pub(crate) fn build_function(types: &TypeOutput, owner: Option<Symbol>, block: &Block) -> Body {
    let mut builder = Builder::new(types, owner);
    let entry = builder.new_block();
    let exit = builder.lower_root_scope(entry, |builder, entry| {
        builder.lower_nodes(&block.body, entry, true)
    });
    builder.terminate_if_open(exit, Terminator::Return);
    builder.finish(entry)
}

pub(crate) fn build_decls(types: &TypeOutput, decls: &[Decl]) -> Body {
    let mut builder = Builder::new(types, None);
    let entry = builder.new_block();
    let exit = builder.lower_root_scope(entry, |builder, entry| builder.lower_decls(decls, entry));
    builder.terminate_if_open(exit, Terminator::Return);
    builder.finish(entry)
}

pub(crate) fn build_nodes(types: &TypeOutput, nodes: &[Node]) -> Body {
    let mut builder = Builder::new(types, None);
    let entry = builder.new_block();
    let exit = builder.lower_root_scope(entry, |builder, entry| {
        builder.lower_nodes(nodes, entry, true)
    });
    builder.terminate_if_open(exit, Terminator::Return);
    builder.finish(entry)
}

#[cfg(test)]
pub(crate) fn use_counts(body: &Body) -> FxHashMap<Symbol, usize> {
    body.use_counts.clone()
}

impl<'types> Builder<'types> {
    fn new(types: &'types TypeOutput, owner: Option<Symbol>) -> Self {
        Self {
            types,
            owner,
            blocks: vec![],
            scopes: vec![],
            locals: vec![],
            local_by_symbol: FxHashMap::default(),
            return_local: None,
            scope_stack: vec![],
            next_point: 0,
            use_counts: FxHashMap::default(),
            loop_stack: vec![],
        }
    }

    fn merge_use_counts(&mut self, body: &Body) {
        for (symbol, count) in &body.use_counts {
            *self.use_counts.entry(*symbol).or_insert(0) += count;
        }
    }
}

impl Builder<'_> {
    fn finish(self, entry: BlockId) -> Body {
        Body {
            owner: self.owner,
            entry,
            blocks: self.blocks,
            scopes: self.scopes,
            locals: self.locals,
            return_local: self.return_local,
            use_counts: self.use_counts,
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

    fn operand_for_expr(&mut self, expr: &Expr) -> Option<ValueUse> {
        match &expr.kind {
            ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_) => Some(ValueUse::Constant(expr.id)),
            ExprKind::Variable(_) | ExprKind::Member(Some(_), ..) => {
                self.key_path_for_expr(expr).map(ValueUse::Copy)
            }
            _ => None,
        }
    }

    fn rvalue_for_expr(&mut self, expr: &Expr) -> Option<Rvalue> {
        if let Some(operand) = self.operand_for_expr(expr) {
            return Some(Rvalue::Use(operand));
        }
        match &expr.kind {
            ExprKind::Tuple(items) => {
                let fields: Option<Vec<_>> = items
                    .iter()
                    .map(|item| self.operand_for_expr(item))
                    .collect();
                Some(Rvalue::Aggregate {
                    kind: AggregateKind::Tuple,
                    fields: fields?,
                })
            }
            ExprKind::RecordLiteral { fields, spread } if spread.is_none() => {
                let fields: Option<Vec<_>> = fields
                    .iter()
                    .map(|field| self.operand_for_expr(&field.value))
                    .collect();
                Some(Rvalue::Aggregate {
                    kind: AggregateKind::Record,
                    fields: fields?,
                })
            }
            ExprKind::Member(Some(receiver), ..) => {
                let field = stored_field_symbol(self.types, expr.member_resolution.as_ref())?;
                let base = self.operand_for_expr(receiver)?;
                Some(Rvalue::FieldRead { base, field })
            }
            ExprKind::InlineIR(_) => Some(Rvalue::InlineIr {
                source: expr.id,
                operands: vec![],
            }),
            ExprKind::Func(_) => Some(Rvalue::Closure {
                source: expr.id,
                captures: vec![],
            }),
            _ => None,
        }
    }

    fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len());
        self.blocks.push(BasicBlock::default());
        id
    }

    fn lower_decls(&mut self, decls: &[Decl], mut current: BlockId) -> BlockId {
        for decl in decls {
            if self.is_terminated(current) {
                current = self.new_block();
            }
            current = self.lower_decl(decl, current);
        }
        current
    }

    fn lower_nodes(
        &mut self,
        nodes: &[Node],
        mut current: BlockId,
        mark_tail_exprs: bool,
    ) -> BlockId {
        let last = nodes.len().saturating_sub(1);
        for (index, node) in nodes.iter().enumerate() {
            if self.is_terminated(current) {
                current = self.new_block();
            }
            let is_tail = mark_tail_exprs && index == last;
            let tail_expr = is_tail.then(|| tail_expr(node)).flatten();
            let tail_control_value = is_tail && node_is_value_control(node);
            current = self.lower_node(node, current, tail_expr.is_none() && !tail_control_value);
            if let Some(expr) = tail_expr {
                let value = self.operand_for_expr(expr);
                self.push_statement(
                    current,
                    Statement::ReturnValue {
                        expr: expr.clone(),
                        value,
                        destination: ValueDestination::Continuation,
                    },
                );
            }
        }
        current
    }

    fn lower_node(&mut self, node: &Node, current: BlockId, consume_expr_value: bool) -> BlockId {
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
            Node::Stmt(stmt) => self.lower_stmt(stmt, current, consume_expr_value),
            Node::Expr(expr) => {
                let current = self.lower_expr(expr, current);
                if consume_expr_value {
                    let value = self.operand_for_expr(expr);
                    self.push_statement(
                        current,
                        Statement::ConsumeValue {
                            expr: expr.clone(),
                            value,
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
                let value = rhs.as_ref().and_then(|rhs| self.rvalue_for_expr(rhs));
                self.push_statement(
                    current,
                    Statement::Bind {
                        lhs: lhs.clone(),
                        type_annotation: type_annotation.clone(),
                        rhs: rhs.clone(),
                        bindings,
                        value,
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

    fn lower_stmt(&mut self, stmt: &Stmt, current: BlockId, consume_expr_value: bool) -> BlockId {
        match &stmt.kind {
            StmtKind::Expr(Expr {
                kind: ExprKind::Block(block),
                ..
            }) => self.lower_child_scope(current, |builder, current| {
                builder.lower_nodes(&block.body, current, false)
            }),
            StmtKind::Expr(expr) => {
                let current = self.lower_expr(expr, current);
                let value = self.operand_for_expr(expr);
                self.push_statement(
                    current,
                    Statement::ConsumeValue {
                        expr: expr.clone(),
                        value,
                    },
                );
                current
            }
            StmtKind::Return(Some(expr)) => {
                let current = self.lower_expr(expr, current);
                let value = self.operand_for_expr(expr);
                self.push_statement(
                    current,
                    Statement::ReturnValue {
                        expr: expr.clone(),
                        value,
                        destination: ValueDestination::Return,
                    },
                );
                self.emit_early_exit_drops(current);
                self.terminate_if_open(current, Terminator::Return);
                current
            }
            StmtKind::Return(None) => {
                self.emit_early_exit_drops(current);
                self.terminate_if_open(current, Terminator::ReturnVoid);
                current
            }
            StmtKind::Continue(Some(expr)) => {
                let current = self.lower_expr(expr, current);
                let value = self.operand_for_expr(expr);
                self.push_statement(
                    current,
                    Statement::ContinueValue {
                        expr: expr.clone(),
                        value,
                    },
                );
                self.emit_early_exit_drops(current);
                let terminator = self
                    .loop_stack
                    .last()
                    .map(|targets| Terminator::Jump(targets.continue_target))
                    .unwrap_or(Terminator::Continue);
                self.terminate_if_open(current, terminator);
                current
            }
            StmtKind::Continue(None) => {
                self.emit_early_exit_drops(current);
                let terminator = self
                    .loop_stack
                    .last()
                    .map(|targets| Terminator::Jump(targets.continue_target))
                    .unwrap_or(Terminator::Continue);
                self.terminate_if_open(current, terminator);
                current
            }
            StmtKind::Break => {
                self.emit_early_exit_drops(current);
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
                let value = self.rvalue_for_expr(rhs);
                self.push_statement(
                    current,
                    Statement::DropCandidate {
                        target: DropTarget::Expr((**lhs).clone()),
                        key_path: target_key_path.clone(),
                        reason: DropReason::AssignmentReplace,
                    },
                );
                self.push_statement(
                    current,
                    Statement::Assign {
                        lhs: (**lhs).clone(),
                        rhs: (**rhs).clone(),
                        target: target_key_path,
                        value,
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
            ExprKind::Block(block) => self.lower_child_scope(current, |builder, current| {
                builder.lower_nodes(&block.body, current, true)
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
                let trailing_body = trailing_block.as_ref().map(|block| {
                    let body = build_block(self.types, block);
                    self.merge_use_counts(&body);
                    Box::new(body)
                });
                self.push_statement(
                    current,
                    Statement::Call {
                        callee: (**callee).clone(),
                        args: args.clone(),
                        trailing_block: trailing_block.clone(),
                        trailing_body,
                    },
                );
                current
            }
            ExprKind::CallEffect { args, .. } => {
                let mut current = current;
                for arg in args {
                    current = self.lower_expr(&arg.value, current);
                }
                self.push_statement(current, Statement::Perform);
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
                    },
                );
                current
            }
            ExprKind::If(condition, then_block, else_block) => {
                let current = self.lower_expr(condition, current);
                let current = self.lower_block_tail_exprs(then_block, current);
                self.lower_block_tail_exprs(else_block, current)
            }
            ExprKind::Match(scrutinee, arms) => self.lower_match(scrutinee, arms, current),
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

    fn lower_block_tail_exprs(&mut self, block: &Block, current: BlockId) -> BlockId {
        match block.body.last().and_then(tail_expr) {
            Some(expr) => self.lower_expr(expr, current),
            None => current,
        }
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

    fn lower_if(
        &mut self,
        condition: &Expr,
        then_block: &Block,
        else_block: Option<&Block>,
        current: BlockId,
        mark_tail_exprs: bool,
    ) -> BlockId {
        let current = self.lower_expr(condition, current);
        let then_id = self.new_block();
        let else_id = self.new_block();
        let join_id = self.new_block();
        self.terminate_if_open(
            current,
            Terminator::Branch {
                condition: condition.clone(),
                then_block: then_id,
                else_block: else_id,
            },
        );

        let then_exit = self.lower_child_scope(then_id, |builder, then_id| {
            builder.lower_nodes(&then_block.body, then_id, mark_tail_exprs)
        });
        self.terminate_if_open(then_exit, Terminator::Jump(join_id));

        let else_exit = if let Some(else_block) = else_block {
            self.lower_child_scope(else_id, |builder, else_id| {
                builder.lower_nodes(&else_block.body, else_id, mark_tail_exprs)
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
        });
        let body_exit = self.lower_child_scope(body_id, |builder, body_id| {
            builder.lower_nodes(&body.body, body_id, false)
        });
        self.loop_stack.pop();
        self.terminate_if_open(body_exit, Terminator::Jump(header_id));

        exit_id
    }

    fn lower_match(&mut self, scrutinee: &Expr, arms: &[MatchArm], current: BlockId) -> BlockId {
        let current = self.lower_expr(scrutinee, current);
        let join_id = self.new_block();
        let arm_blocks: Vec<_> = arms.iter().map(|_| self.new_block()).collect();
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
            let arm_exit = self.lower_child_scope(arm_id, |builder, arm_id| {
                builder.lower_pattern_binders(&arm.pattern, arm_id);
                builder.lower_nodes(&arm.body.body, arm_id, true)
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
        match &statement {
            Statement::Read { expr } => {
                if let Some(symbol) = syntactic_root_symbol(expr) {
                    *self.use_counts.entry(symbol).or_insert(0) += 1;
                }
            }
            Statement::AssignmentRootUse { symbol, .. } => {
                *self.use_counts.entry(*symbol).or_insert(0) += 1;
            }
            Statement::ScopeEnter { .. }
            | Statement::ScopeExit { .. }
            | Statement::StorageLive { .. }
            | Statement::StorageDead { .. }
            | Statement::DropCandidate { .. }
            | Statement::ConsumeValue { .. }
            | Statement::Bind { .. }
            | Statement::Assign { .. }
            | Statement::Call { .. }
            | Statement::Perform
            | Statement::ReturnValue { .. }
            | Statement::ContinueValue { .. }
            | Statement::Function { .. }
            | Statement::Handling { .. }
            | Statement::DeclBody { .. } => {}
        }
        let point = StatementId(self.next_point);
        self.next_point += 1;
        self.blocks[block.0].statements.push(LocatedStatement {
            point,
            kind: statement,
            ownership: StatementOwnership::default(),
        });
    }

    fn lower_root_scope(
        &mut self,
        current: BlockId,
        lower: impl FnOnce(&mut Self, BlockId) -> BlockId,
    ) -> BlockId {
        let scope = self.new_scope(None);
        self.scope_stack.push(ScopeFrame {
            id: scope,
            locals: vec![],
        });
        self.push_statement(current, Statement::ScopeEnter { scope });
        let exit = lower(self, current);
        let exit = self.emit_scope_exit(exit);
        self.scope_stack.pop();
        exit
    }

    fn lower_child_scope(
        &mut self,
        current: BlockId,
        lower: impl FnOnce(&mut Self, BlockId) -> BlockId,
    ) -> BlockId {
        let parent = self.scope_stack.last().map(|scope| scope.id);
        let scope = self.new_scope(parent);
        self.scope_stack.push(ScopeFrame {
            id: scope,
            locals: vec![],
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

    fn emit_scope_exit(&mut self, current: BlockId) -> BlockId {
        let Some(frame) = self.scope_stack.last() else {
            return current;
        };
        let scope = frame.id;
        let locals: Vec<(NodeID, Symbol)> = frame.locals.clone();
        for (id, symbol) in locals.iter().rev().copied() {
            let key_path = Some(KeyPath::root(self.local_for_symbol(symbol)));
            self.push_statement(
                current,
                Statement::DropCandidate {
                    target: DropTarget::Symbol { id, symbol },
                    key_path,
                    reason: DropReason::ScopeExit,
                },
            );
            self.push_statement(current, Statement::StorageDead { id, symbol });
        }
        self.push_statement(current, Statement::ScopeExit { scope });
        current
    }

    fn emit_early_exit_drops(&mut self, current: BlockId) {
        let locals: Vec<(NodeID, Symbol)> = self
            .scope_stack
            .iter()
            .rev()
            .flat_map(|scope| scope.locals.iter().rev().copied())
            .collect();
        for (id, symbol) in locals {
            let key_path = Some(KeyPath::root(self.local_for_symbol(symbol)));
            self.push_statement(
                current,
                Statement::DropCandidate {
                    target: DropTarget::Symbol { id, symbol },
                    key_path,
                    reason: DropReason::EarlyExit,
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

fn syntactic_root_symbol(expr: &Expr) -> Option<Symbol> {
    match &expr.kind {
        ExprKind::Variable(name) => name.symbol().ok(),
        ExprKind::Member(Some(receiver), ..) => syntactic_root_symbol(receiver),
        _ => None,
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
            KeyPathComponent::TupleField(index) => rendered.push_str(&format!(".{index}")),
            KeyPathComponent::VariantPayload { variant, index } => {
                rendered.push_str(&format!(".{variant}[{index}]"));
            }
            KeyPathComponent::DerefBorrow => rendered.push_str(".*"),
            KeyPathComponent::Index(index) => {
                rendered.push_str(&format!("[{}]", render_local(*index)))
            }
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
        Statement::Perform => "perform".into(),
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
                        let body = build_block(&types, &func.body);
                        return f(&body);
                    }
                    continue;
                };
                let body = build_block(&types, &func.body);
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
    fn caches_source_order_use_counts() {
        let source = "
            func f(x, y) {
                let z = x
                (z, y)
            }
        ";
        let names = resolved_names(source);
        let x = symbol_named(&names, "x");
        let y = symbol_named(&names, "y");
        let z = symbol_named(&names, "z");
        let counts = with_first_func_mir(source, use_counts);

        assert_eq!(counts.get(&x), Some(&1));
        assert_eq!(counts.get(&y), Some(&1));
        assert_eq!(counts.get(&z), Some(&1));
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

    #[test]
    fn records_rvalues_for_simple_binds_and_returns() {
        let source = "
            func f() {
                let first = 1
                first
            }
        ";
        with_first_func_mir(source, |body| {
            let bind_has_constant = body.blocks.iter().any(|block| {
                block.statements.iter().any(|statement| {
                    matches!(
                        &statement.kind,
                        Statement::Bind {
                            value: Some(Rvalue::Use(ValueUse::Constant(_))),
                            ..
                        }
                    )
                })
            });
            let return_has_copy = body.blocks.iter().any(|block| {
                block.statements.iter().any(|statement| {
                    matches!(
                        &statement.kind,
                        Statement::ReturnValue {
                            value: Some(ValueUse::Copy(_)),
                            ..
                        }
                    )
                })
            });

            assert!(bind_has_constant, "{body:#?}");
            assert!(return_has_copy, "{body:#?}");
        });
    }

    #[test]
    fn distinguishes_source_return_from_block_tail_value() {
        let source = "
            func f(flag) {
                if flag {
                    return 1
                }
                2
            }
        ";
        with_first_func_mir(source, |body| {
            let mut has_source_return = false;
            let mut has_block_tail = false;
            for block in &body.blocks {
                for statement in &block.statements {
                    if let Statement::ReturnValue { destination, .. } = statement.kind {
                        match destination {
                            ValueDestination::Return => has_source_return = true,
                            ValueDestination::Continuation => has_block_tail = true,
                        }
                    }
                }
            }

            assert!(has_source_return, "{body:#?}");
            assert!(has_block_tail, "{body:#?}");
        });
    }
}
