//! Borrower liveness: when does a borrow end? The legacy checker ran a
//! backward live-variable dataflow over MIR and pruned loans whose borrower
//! root died. The flow checker's structured equivalent: a pre-order pre-pass
//! assigns every node a position and records each symbol's LAST USE
//! position; the checking walk prunes loans whose borrower has no use at or
//! beyond the current node.
//!
//! Loop-carried borrows: a use inside a loop of a symbol declared OUTSIDE
//! that loop is a use on every iteration, so it extends to the loop's end
//! position. Symbols declared inside the loop die within their own
//! iteration. (Uses in a sibling branch over-approximate liveness by
//! pre-order position — conservative, and unobserved by the ported corpus.)

use rustc_hash::{FxHashMap, FxHashSet};

use crate::hir::{self, ExprKind};
use crate::name_resolution::symbol::Symbol;
use crate::node_id::NodeID;

#[derive(Default)]
pub(crate) struct Liveness {
    position: FxHashMap<NodeID, usize>,
    last_use: FxHashMap<Symbol, usize>,
}

impl Liveness {
    pub(crate) fn analyze(nodes: &[hir::Node]) -> Liveness {
        let mut pass = Prepass {
            liveness: Liveness::default(),
            declared: FxHashMap::default(),
            loop_stack: vec![],
            next: 0,
        };
        pass.walk_nodes(nodes);
        pass.liveness
    }

    /// True when `symbol` has no use at or after `node` (so any loan it
    /// holds can be pruned once the walk passes `node`).
    pub(crate) fn dead_after(&self, node: NodeID, symbol: Symbol) -> bool {
        let Some(position) = self.position.get(&node) else {
            return false;
        };
        match self.last_use.get(&symbol) {
            Some(last) => last <= position,
            None => true,
        }
    }
}

struct Prepass {
    liveness: Liveness,
    /// Declaration position + loop depth per symbol.
    declared: FxHashMap<Symbol, usize>,
    /// Open loops as (loop depth marker); uses of symbols declared outside
    /// the innermost enclosing loop extend to that loop's end.
    loop_stack: Vec<LoopFrame>,
    next: usize,
}

struct LoopFrame {
    /// Symbols used inside this loop that were declared before it started.
    carried: FxHashSet<Symbol>,
    start: usize,
}

impl Prepass {
    fn bump(&mut self, node: NodeID) -> usize {
        self.next += 1;
        self.liveness.position.insert(node, self.next);
        self.next
    }

    fn record_use(&mut self, symbol: Symbol, position: usize) {
        // A use inside a loop of a symbol declared before the loop recurs
        // every iteration; the loop frame extends it to the loop end.
        for frame in self.loop_stack.iter_mut().rev() {
            if self
                .declared
                .get(&symbol)
                .is_some_and(|declared| *declared < frame.start)
            {
                frame.carried.insert(symbol);
            }
        }
        let entry = self.liveness.last_use.entry(symbol).or_insert(position);
        if *entry < position {
            *entry = position;
        }
    }

    fn walk_nodes(&mut self, nodes: &[hir::Node]) {
        for node in nodes {
            match node {
                hir::Node::Decl(decl) => self.walk_decl(decl),
                hir::Node::Stmt(stmt) => self.walk_stmt(stmt),
                hir::Node::Expr(expr) => self.walk_expr(expr),
            }
        }
    }

    fn walk_decl(&mut self, decl: &hir::Decl) {
        match &decl.kind {
            hir::DeclKind::Let { lhs, rhs, .. } => {
                if let Some(rhs) = rhs {
                    self.walk_expr(rhs);
                }
                for (id, binder) in lhs.collect_binders() {
                    let position = self.bump(id);
                    self.declared.insert(binder, position);
                }
            }
            hir::DeclKind::Func(func) => self.walk_closure(func),
            _ => {}
        }
        // The checker prunes loans after each declaration node.
        self.bump(decl.id);
    }

    fn walk_stmt(&mut self, stmt: &hir::Stmt) {
        match &stmt.kind {
            hir::StmtKind::Expr(expr) => {
                self.walk_expr(expr);
                self.bump(stmt.id);
            }
            hir::StmtKind::If(cond, then_block, else_block) => {
                self.walk_expr(cond);
                self.walk_nodes(&then_block.body);
                if let Some(else_block) = else_block {
                    self.walk_nodes(&else_block.body);
                }
                self.bump(stmt.id);
            }
            hir::StmtKind::Return(value) | hir::StmtKind::Continue(value) => {
                if let Some(value) = value {
                    self.walk_expr(value);
                }
                self.bump(stmt.id);
            }
            hir::StmtKind::Break => {
                self.bump(stmt.id);
            }
            hir::StmtKind::Assignment(lhs, rhs) => {
                self.walk_expr(rhs);
                // An assignment through fields reads its root; a whole-root
                // assignment is a definition, not a use.
                if let Some((root, has_fields)) = assignment_root(lhs) {
                    if has_fields {
                        let position = self.next + 1;
                        self.record_use(root, position);
                    }
                    self.walk_member_receivers(lhs);
                }
                self.bump(stmt.id);
            }
            hir::StmtKind::Loop(cond, body) => {
                self.loop_stack.push(LoopFrame {
                    carried: FxHashSet::default(),
                    start: self.next,
                });
                if let Some(cond) = cond {
                    self.walk_expr(cond);
                }
                self.walk_nodes(&body.body);
                let end = self.bump(stmt.id);
                let Some(frame) = self.loop_stack.pop() else {
                    unreachable!("loop frame pushed above")
                };
                for symbol in frame.carried {
                    self.record_use(symbol, end);
                }
            }
            hir::StmtKind::Handling { body, .. } => {
                self.walk_nodes(&body.body);
                self.bump(stmt.id);
            }
        }
    }

    fn walk_expr(&mut self, expr: &hir::Expr) {
        match &expr.kind {
            ExprKind::Variable(name) => {
                if let Ok(symbol) = name.symbol() {
                    let position = self.bump(expr.id);
                    self.record_use(symbol, position);
                }
            }
            ExprKind::Member(receiver, _) => {
                if let Some(receiver) = receiver {
                    self.walk_expr(receiver);
                }
                self.bump(expr.id);
            }
            ExprKind::Call {
                callee,
                args,
                trailing_block,
                ..
            } => {
                self.walk_expr(callee);
                for arg in args {
                    self.walk_expr(&arg.value);
                }
                if let Some(block) = trailing_block {
                    self.walk_nodes(&block.body);
                }
                self.bump(expr.id);
            }
            ExprKind::CallEffect { args, .. } => {
                for arg in args {
                    self.walk_expr(&arg.value);
                }
                self.bump(expr.id);
            }
            ExprKind::Tuple(items) | ExprKind::LiteralArray(items) => {
                for item in items {
                    self.walk_expr(item);
                }
                self.bump(expr.id);
            }
            ExprKind::RecordLiteral { fields, spread } => {
                for field in fields {
                    self.walk_expr(&field.value);
                }
                if let Some(spread) = spread {
                    self.walk_expr(spread);
                }
                self.bump(expr.id);
            }
            ExprKind::As(inner, _) => {
                self.walk_expr(inner);
                self.bump(expr.id);
            }
            ExprKind::Block(block) => {
                self.walk_nodes(&block.body);
                self.bump(expr.id);
            }
            ExprKind::If(cond, then_block, else_block) => {
                self.walk_expr(cond);
                self.walk_nodes(&then_block.body);
                self.walk_nodes(&else_block.body);
                self.bump(expr.id);
            }
            ExprKind::Match(scrutinee, arms) => {
                self.walk_expr(scrutinee);
                for arm in arms {
                    for (id, binder) in arm.pattern.collect_binders() {
                        let position = self.bump(id);
                        self.declared.insert(binder, position);
                    }
                    self.walk_nodes(&arm.body.body);
                }
                self.bump(expr.id);
            }
            ExprKind::Func(func) => {
                self.walk_closure(func);
                self.bump(expr.id);
            }
            ExprKind::InlineIR(ir) => {
                for bind in &ir.binds {
                    self.walk_expr(bind);
                }
                self.bump(expr.id);
            }
            ExprKind::Constructor(_)
            | ExprKind::RowVariable(_)
            | ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_) => {
                self.bump(expr.id);
            }
        }
    }

    /// A closure's free-variable reads (captures) are uses at the closure's
    /// position in the parent: the closure value carries them.
    fn walk_closure(&mut self, func: &hir::Func) {
        let position = self.bump(func.id);
        let mut bound: FxHashSet<Symbol> = FxHashSet::default();
        for param in &func.params {
            if let Ok(symbol) = param.name.symbol() {
                bound.insert(symbol);
            }
        }
        let mut uses = FxHashSet::default();
        collect_free_reads(&func.body, &mut bound, &mut uses);
        for capture in &func.captures {
            if let Ok(symbol) = capture.name.symbol() {
                uses.insert(symbol);
            }
        }
        for symbol in uses {
            self.record_use(symbol, position);
        }
    }

    fn walk_member_receivers(&mut self, expr: &hir::Expr) {
        if let ExprKind::Member(Some(receiver), _) = &expr.kind {
            self.walk_member_receivers(receiver);
        }
    }
}

fn assignment_root(lhs: &hir::Expr) -> Option<(Symbol, bool)> {
    match &lhs.kind {
        ExprKind::Variable(name) => name.symbol().ok().map(|symbol| (symbol, false)),
        ExprKind::Member(Some(receiver), _) => {
            let (root, _) = assignment_root(receiver)?;
            Some((root, true))
        }
        _ => None,
    }
}

/// Free-variable reads within a closure body (symbols not bound inside it).
pub(crate) fn collect_free_reads(
    block: &hir::Block,
    bound: &mut FxHashSet<Symbol>,
    out: &mut FxHashSet<Symbol>,
) {
    use derive_visitor::{Drive, Visitor};

    #[derive(Visitor)]
    #[visitor(hir::Expr(enter), hir::Pattern(enter))]
    struct FreeReads<'a> {
        bound: &'a mut FxHashSet<Symbol>,
        out: &'a mut FxHashSet<Symbol>,
    }

    impl FreeReads<'_> {
        fn enter_expr(&mut self, expr: &hir::Expr) {
            match &expr.kind {
                ExprKind::Variable(name) => {
                    if let Ok(symbol) = name.symbol()
                        && !self.bound.contains(&symbol)
                        && is_local_or_param(symbol)
                    {
                        self.out.insert(symbol);
                    }
                }
                ExprKind::Func(func) => {
                    // Nested closure params/binders bind inward; their free
                    // reads are still free here, so keep walking but bind
                    // their params first.
                    for param in &func.params {
                        if let Ok(symbol) = param.name.symbol() {
                            self.bound.insert(symbol);
                        }
                    }
                }
                _ => {}
            }
        }

        fn enter_pattern(&mut self, pattern: &hir::Pattern) {
            for (_, binder) in pattern.collect_binders() {
                self.bound.insert(binder);
            }
        }
    }

    let mut visitor = FreeReads { bound, out };
    for node in &block.body {
        node.drive(&mut visitor);
    }
}

pub(crate) fn is_local_or_param(symbol: Symbol) -> bool {
    matches!(
        symbol,
        Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_) | Symbol::ParamLocal(_)
    )
}
