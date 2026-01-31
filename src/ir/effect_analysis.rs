//! Analysis pass for effectful functions to prepare for state machine compilation.
//!
//! This module analyzes functions that use effects to identify yield points
//! (effect calls) and determine which variables are live at each point.

use indexmap::IndexSet;
use rustc_hash::FxHashSet;

use crate::{
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        infer_ty::Ty,
        typed_ast::{
            TypedBlock, TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedFunc,
            TypedNode, TypedPattern, TypedPatternKind, TypedStmt, TypedStmtKind,
        },
    },
};

/// A yield point is an effect call site where execution can suspend.
#[derive(Debug, Clone)]
pub struct YieldPoint {
    /// The AST node ID of the effect call expression
    pub expr_id: NodeID,
    /// The effect being called
    pub effect: Symbol,
    /// Variables that are live (needed after this yield point)
    pub live_vars: Vec<(Symbol, Ty)>,
    /// The state index after this yield point resumes
    pub resume_state: usize,
}

/// Information about a state in the state machine
#[derive(Debug, Clone)]
pub struct StateInfo {
    /// The state index (0 = initial state)
    pub index: usize,
    /// Variables that need to be stored in this state
    pub live_vars: Vec<(Symbol, Ty)>,
    /// The yield point that transitions to this state (None for initial state)
    pub from_yield: Option<usize>,
}

/// Analysis results for an effectful function
#[derive(Debug, Clone)]
pub struct EffectAnalysis {
    /// All yield points (effect call sites) in the function
    pub yield_points: Vec<YieldPoint>,
    /// All states in the state machine
    pub states: Vec<StateInfo>,
    /// The function's effect row
    pub effects: Vec<Symbol>,
}

impl EffectAnalysis {
    /// Create a new empty analysis
    pub fn new() -> Self {
        Self {
            yield_points: Vec::new(),
            states: vec![StateInfo {
                index: 0,
                live_vars: Vec::new(),
                from_yield: None,
            }],
            effects: Vec::new(),
        }
    }

    /// Analyze a function to find yield points and compute live variables.
    /// Returns None if the function has no effects (not effectful).
    pub fn analyze(func: &TypedFunc, get_ty: impl Fn(&Symbol) -> Option<Ty>) -> Option<Self> {
        // Check if function has effects
        if func.effects.is_empty() {
            return None;
        }

        let mut analysis = Self::new();

        // Collect effect symbols
        for effect in &func.effects {
            analysis.effects.push(effect.name);
        }

        // Find all effect call sites and collect all bindings
        let mut yield_points = Vec::new();
        let mut all_bindings: IndexSet<Symbol> = IndexSet::new();

        // Collect parameter bindings
        for param in &func.params {
            all_bindings.insert(param.name);
        }

        // Walk the AST to find effect calls and collect bindings
        Self::find_yields_and_bindings(&func.body, &mut yield_points, &mut all_bindings);

        if yield_points.is_empty() {
            return None;
        }

        // For each yield point, compute live variables (variables defined before
        // and used after this point)
        for (expr_id, effect) in yield_points.iter() {
            // Collect variables defined before this yield point
            let mut defined_before: FxHashSet<Symbol> = FxHashSet::default();
            for param in &func.params {
                defined_before.insert(param.name);
            }
            Self::collect_definitions_before(&func.body, *expr_id, &mut defined_before);

            // Collect variables used after this yield point
            let mut used_after: FxHashSet<Symbol> = FxHashSet::default();
            Self::collect_uses_after(&func.body, *expr_id, &mut used_after);

            // Live variables = defined_before ∩ used_after
            let live_vars: Vec<(Symbol, Ty)> = defined_before
                .intersection(&used_after)
                .filter_map(|sym| {
                    let ty = get_ty(sym)?;
                    Some((*sym, ty))
                })
                .collect();

            analysis.add_yield_point(*expr_id, *effect, live_vars);
        }

        Some(analysis)
    }

    /// Walk the AST to find effect call expressions and collect all bindings
    fn find_yields_and_bindings(
        block: &TypedBlock,
        yield_points: &mut Vec<(NodeID, Symbol)>,
        bindings: &mut IndexSet<Symbol>,
    ) {
        for node in &block.body {
            Self::find_yields_in_node(node, yield_points, bindings);
        }
    }

    fn find_yields_in_node(
        node: &TypedNode,
        yield_points: &mut Vec<(NodeID, Symbol)>,
        bindings: &mut IndexSet<Symbol>,
    ) {
        match node {
            TypedNode::Expr(expr) => Self::find_yields_in_expr(expr, yield_points, bindings),
            TypedNode::Stmt(stmt) => Self::find_yields_in_stmt(stmt, yield_points, bindings),
            TypedNode::Decl(decl) => Self::find_yields_in_decl(decl, yield_points, bindings),
        }
    }

    fn find_yields_in_decl(
        decl: &TypedDecl,
        yield_points: &mut Vec<(NodeID, Symbol)>,
        bindings: &mut IndexSet<Symbol>,
    ) {
        if let TypedDeclKind::Let {
            pattern,
            initializer,
            ..
        } = &decl.kind
        {
            // Collect bindings from pattern
            Self::collect_pattern_bindings(pattern, bindings);

            // Check initializer for yields
            if let Some(init) = initializer {
                Self::find_yields_in_expr(init, yield_points, bindings);
            }
        }
    }

    fn find_yields_in_stmt(
        stmt: &TypedStmt,
        yield_points: &mut Vec<(NodeID, Symbol)>,
        bindings: &mut IndexSet<Symbol>,
    ) {
        match &stmt.kind {
            TypedStmtKind::Expr(expr) => {
                Self::find_yields_in_expr(expr, yield_points, bindings);
            }
            TypedStmtKind::Assignment(lhs, rhs) => {
                Self::find_yields_in_expr(lhs, yield_points, bindings);
                Self::find_yields_in_expr(rhs, yield_points, bindings);
            }
            TypedStmtKind::Return(Some(expr)) => {
                Self::find_yields_in_expr(expr, yield_points, bindings);
            }
            TypedStmtKind::Return(None) => {}
            TypedStmtKind::Continue(Some(expr)) => {
                Self::find_yields_in_expr(expr, yield_points, bindings);
            }
            TypedStmtKind::Continue(None) => {}
            TypedStmtKind::Loop(cond, body) => {
                Self::find_yields_in_expr(cond, yield_points, bindings);
                Self::find_yields_and_bindings(body, yield_points, bindings);
            }
            TypedStmtKind::Break => {}
            TypedStmtKind::Handler { func, .. } => {
                // Don't descend into handlers - they're separate functions
                let _ = func;
            }
        }
    }

    fn find_yields_in_expr(
        expr: &TypedExpr,
        yield_points: &mut Vec<(NodeID, Symbol)>,
        bindings: &mut IndexSet<Symbol>,
    ) {
        match &expr.kind {
            TypedExprKind::CallEffect { effect, args, .. } => {
                // This is a yield point!
                yield_points.push((expr.id, *effect));
                // Check args for nested yields
                for arg in args {
                    Self::find_yields_in_expr(arg, yield_points, bindings);
                }
            }
            TypedExprKind::Call { callee, args, .. } => {
                Self::find_yields_in_expr(callee, yield_points, bindings);
                for arg in args {
                    Self::find_yields_in_expr(arg, yield_points, bindings);
                }
            }
            TypedExprKind::Block(block) => {
                Self::find_yields_and_bindings(block, yield_points, bindings);
            }
            TypedExprKind::If(cond, conseq, alt) => {
                Self::find_yields_in_expr(cond, yield_points, bindings);
                Self::find_yields_and_bindings(conseq, yield_points, bindings);
                Self::find_yields_and_bindings(alt, yield_points, bindings);
            }
            TypedExprKind::Match(scrutinee, arms) => {
                Self::find_yields_in_expr(scrutinee, yield_points, bindings);
                for arm in arms {
                    Self::collect_pattern_bindings(&arm.pattern, bindings);
                    Self::find_yields_and_bindings(&arm.body, yield_points, bindings);
                }
            }
            TypedExprKind::Func(_) => {
                // Don't descend into nested functions
            }
            TypedExprKind::Member { receiver, .. } => {
                Self::find_yields_in_expr(receiver, yield_points, bindings);
            }
            TypedExprKind::Tuple(exprs) | TypedExprKind::LiteralArray(exprs) => {
                for e in exprs {
                    Self::find_yields_in_expr(e, yield_points, bindings);
                }
            }
            TypedExprKind::RecordLiteral { fields } => {
                for field in fields {
                    Self::find_yields_in_expr(&field.value, yield_points, bindings);
                }
            }
            // Leaf expressions - no nested yields
            TypedExprKind::Hole
            | TypedExprKind::InlineIR(_)
            | TypedExprKind::LiteralInt(_)
            | TypedExprKind::LiteralFloat(_)
            | TypedExprKind::LiteralTrue
            | TypedExprKind::LiteralFalse
            | TypedExprKind::LiteralString(_)
            | TypedExprKind::Variable(_)
            | TypedExprKind::Constructor(_, _)
            | TypedExprKind::Choice { .. } => {}
        }
    }

    fn collect_pattern_bindings(pattern: &TypedPattern, bindings: &mut IndexSet<Symbol>) {
        match &pattern.kind {
            TypedPatternKind::Bind(sym) => {
                bindings.insert(*sym);
            }
            TypedPatternKind::Tuple(pats) => {
                for p in pats {
                    Self::collect_pattern_bindings(p, bindings);
                }
            }
            TypedPatternKind::Variant { fields, .. } => {
                for field in fields {
                    Self::collect_pattern_bindings(field, bindings);
                }
            }
            TypedPatternKind::Record { fields } => {
                for field in fields {
                    Self::collect_record_field_pattern_bindings(field, bindings);
                }
            }
            TypedPatternKind::Struct { fields, .. } => {
                for field in fields {
                    Self::collect_pattern_bindings(field, bindings);
                }
            }
            TypedPatternKind::Or(pats) => {
                for p in pats {
                    Self::collect_pattern_bindings(p, bindings);
                }
            }
            TypedPatternKind::Wildcard
            | TypedPatternKind::LiteralInt(_)
            | TypedPatternKind::LiteralFloat(_)
            | TypedPatternKind::LiteralTrue
            | TypedPatternKind::LiteralFalse => {}
        }
    }

    fn collect_record_field_pattern_bindings(
        field: &crate::types::typed_ast::TypedRecordFieldPattern,
        bindings: &mut IndexSet<Symbol>,
    ) {
        use crate::types::typed_ast::TypedRecordFieldPatternKind;
        match &field.kind {
            TypedRecordFieldPatternKind::Bind(sym) => {
                bindings.insert(*sym);
            }
            TypedRecordFieldPatternKind::Equals { value, .. } => {
                Self::collect_pattern_bindings(value, bindings);
            }
            TypedRecordFieldPatternKind::Rest => {}
        }
    }

    /// Collect all variables defined before a specific expression
    fn collect_definitions_before(
        block: &TypedBlock,
        target_id: NodeID,
        defined: &mut FxHashSet<Symbol>,
    ) -> bool {
        for node in &block.body {
            if Self::node_contains_id(node, target_id) {
                // Found the target - collect definitions in prefix of this node
                Self::collect_definitions_in_node_prefix(node, target_id, defined);
                return true;
            }
            // Node is before target - collect all its definitions
            Self::collect_all_definitions_in_node(node, defined);
        }
        false
    }

    fn node_contains_id(node: &TypedNode, target_id: NodeID) -> bool {
        match node {
            TypedNode::Expr(expr) => Self::expr_contains_id(expr, target_id),
            TypedNode::Stmt(stmt) => Self::stmt_contains_id(stmt, target_id),
            TypedNode::Decl(decl) => Self::decl_contains_id(decl, target_id),
        }
    }

    fn expr_contains_id(expr: &TypedExpr, target_id: NodeID) -> bool {
        if expr.id == target_id {
            return true;
        }
        match &expr.kind {
            TypedExprKind::CallEffect { args, .. } => args.iter().any(|a| Self::expr_contains_id(a, target_id)),
            TypedExprKind::Call { callee, args, .. } => {
                Self::expr_contains_id(callee, target_id)
                    || args.iter().any(|a| Self::expr_contains_id(a, target_id))
            }
            TypedExprKind::Block(block) => block.body.iter().any(|n| Self::node_contains_id(n, target_id)),
            TypedExprKind::If(cond, conseq, alt) => {
                Self::expr_contains_id(cond, target_id)
                    || conseq.body.iter().any(|n| Self::node_contains_id(n, target_id))
                    || alt.body.iter().any(|n| Self::node_contains_id(n, target_id))
            }
            TypedExprKind::Match(scrutinee, arms) => {
                Self::expr_contains_id(scrutinee, target_id)
                    || arms.iter().any(|arm| arm.body.body.iter().any(|n| Self::node_contains_id(n, target_id)))
            }
            TypedExprKind::Member { receiver, .. } => Self::expr_contains_id(receiver, target_id),
            TypedExprKind::Tuple(exprs) | TypedExprKind::LiteralArray(exprs) => {
                exprs.iter().any(|e| Self::expr_contains_id(e, target_id))
            }
            TypedExprKind::RecordLiteral { fields } => {
                fields.iter().any(|f| Self::expr_contains_id(&f.value, target_id))
            }
            _ => false,
        }
    }

    fn stmt_contains_id(stmt: &TypedStmt, target_id: NodeID) -> bool {
        match &stmt.kind {
            TypedStmtKind::Expr(expr) => Self::expr_contains_id(expr, target_id),
            TypedStmtKind::Assignment(lhs, rhs) => {
                Self::expr_contains_id(lhs, target_id) || Self::expr_contains_id(rhs, target_id)
            }
            TypedStmtKind::Return(Some(expr)) => Self::expr_contains_id(expr, target_id),
            TypedStmtKind::Continue(Some(expr)) => Self::expr_contains_id(expr, target_id),
            TypedStmtKind::Loop(cond, body) => {
                Self::expr_contains_id(cond, target_id)
                    || body.body.iter().any(|n| Self::node_contains_id(n, target_id))
            }
            _ => false,
        }
    }

    fn decl_contains_id(decl: &TypedDecl, target_id: NodeID) -> bool {
        if let TypedDeclKind::Let { initializer: Some(init), .. } = &decl.kind {
            Self::expr_contains_id(init, target_id)
        } else {
            false
        }
    }

    fn collect_definitions_in_node_prefix(
        node: &TypedNode,
        target_id: NodeID,
        defined: &mut FxHashSet<Symbol>,
    ) {
        match node {
            TypedNode::Decl(_decl) => {
                // If target is in initializer, we don't include the pattern bindings yet
                // (they're not defined until after the initializer completes)
            }
            TypedNode::Stmt(stmt) => {
                Self::collect_definitions_in_stmt_prefix(stmt, target_id, defined);
            }
            TypedNode::Expr(expr) => {
                Self::collect_definitions_in_expr_prefix(expr, target_id, defined);
            }
        }
    }

    fn collect_definitions_in_stmt_prefix(
        stmt: &TypedStmt,
        target_id: NodeID,
        defined: &mut FxHashSet<Symbol>,
    ) {
        match &stmt.kind {
            TypedStmtKind::Loop(_, body) => {
                // Definitions in loop body before target
                Self::collect_definitions_before(body, target_id, defined);
            }
            _ => {}
        }
    }

    fn collect_definitions_in_expr_prefix(
        expr: &TypedExpr,
        target_id: NodeID,
        defined: &mut FxHashSet<Symbol>,
    ) {
        match &expr.kind {
            TypedExprKind::Block(block) => {
                Self::collect_definitions_before(block, target_id, defined);
            }
            TypedExprKind::If(_, conseq, alt) => {
                // Definitions in branches before target
                Self::collect_definitions_before(conseq, target_id, defined);
                Self::collect_definitions_before(alt, target_id, defined);
            }
            TypedExprKind::Match(_, arms) => {
                for arm in arms {
                    if arm.body.body.iter().any(|n| Self::node_contains_id(n, target_id)) {
                        Self::collect_pattern_bindings_hash(&arm.pattern, defined);
                        Self::collect_definitions_before(&arm.body, target_id, defined);
                    }
                }
            }
            _ => {}
        }
    }

    fn collect_all_definitions_in_node(node: &TypedNode, defined: &mut FxHashSet<Symbol>) {
        match node {
            TypedNode::Decl(decl) => {
                if let TypedDeclKind::Let { pattern, .. } = &decl.kind {
                    Self::collect_pattern_bindings_hash(pattern, defined);
                }
            }
            TypedNode::Stmt(stmt) => {
                if let TypedStmtKind::Loop(_, body) = &stmt.kind {
                    for n in &body.body {
                        Self::collect_all_definitions_in_node(n, defined);
                    }
                }
            }
            TypedNode::Expr(expr) => {
                Self::collect_all_definitions_in_expr(expr, defined);
            }
        }
    }

    fn collect_all_definitions_in_expr(expr: &TypedExpr, defined: &mut FxHashSet<Symbol>) {
        match &expr.kind {
            TypedExprKind::Block(block) => {
                for n in &block.body {
                    Self::collect_all_definitions_in_node(n, defined);
                }
            }
            TypedExprKind::If(_, conseq, alt) => {
                for n in &conseq.body {
                    Self::collect_all_definitions_in_node(n, defined);
                }
                for n in &alt.body {
                    Self::collect_all_definitions_in_node(n, defined);
                }
            }
            TypedExprKind::Match(_, arms) => {
                for arm in arms {
                    Self::collect_pattern_bindings_hash(&arm.pattern, defined);
                    for n in &arm.body.body {
                        Self::collect_all_definitions_in_node(n, defined);
                    }
                }
            }
            _ => {}
        }
    }

    fn collect_pattern_bindings_hash(pattern: &TypedPattern, defined: &mut FxHashSet<Symbol>) {
        match &pattern.kind {
            TypedPatternKind::Bind(sym) => {
                defined.insert(*sym);
            }
            TypedPatternKind::Tuple(pats) => {
                for p in pats {
                    Self::collect_pattern_bindings_hash(p, defined);
                }
            }
            TypedPatternKind::Variant { fields, .. } => {
                for field in fields {
                    Self::collect_pattern_bindings_hash(field, defined);
                }
            }
            TypedPatternKind::Record { fields } => {
                for field in fields {
                    Self::collect_record_field_pattern_bindings_hash(field, defined);
                }
            }
            TypedPatternKind::Struct { fields, .. } => {
                for field in fields {
                    Self::collect_pattern_bindings_hash(field, defined);
                }
            }
            TypedPatternKind::Or(pats) => {
                for p in pats {
                    Self::collect_pattern_bindings_hash(p, defined);
                }
            }
            _ => {}
        }
    }

    fn collect_record_field_pattern_bindings_hash(
        field: &crate::types::typed_ast::TypedRecordFieldPattern,
        defined: &mut FxHashSet<Symbol>,
    ) {
        use crate::types::typed_ast::TypedRecordFieldPatternKind;
        match &field.kind {
            TypedRecordFieldPatternKind::Bind(sym) => {
                defined.insert(*sym);
            }
            TypedRecordFieldPatternKind::Equals { value, .. } => {
                Self::collect_pattern_bindings_hash(value, defined);
            }
            TypedRecordFieldPatternKind::Rest => {}
        }
    }

    /// Collect all variables used after a specific expression
    fn collect_uses_after(block: &TypedBlock, target_id: NodeID, used: &mut FxHashSet<Symbol>) {
        let mut found = false;
        for node in &block.body {
            if found {
                // Everything after the target
                Self::collect_all_uses_in_node(node, used);
            } else if Self::node_contains_id(node, target_id) {
                found = true;
                // Collect uses in suffix of this node
                Self::collect_uses_in_node_suffix(node, target_id, used);
            }
        }
    }

    fn collect_uses_in_node_suffix(node: &TypedNode, target_id: NodeID, used: &mut FxHashSet<Symbol>) {
        match node {
            TypedNode::Expr(expr) => Self::collect_uses_in_expr_suffix(expr, target_id, used),
            TypedNode::Stmt(stmt) => Self::collect_uses_in_stmt_suffix(stmt, target_id, used),
            TypedNode::Decl(decl) => {
                // For let declarations, uses after the target in initializer
                if let TypedDeclKind::Let { initializer: Some(init), .. } = &decl.kind {
                    Self::collect_uses_in_expr_suffix(init, target_id, used);
                }
            }
        }
    }

    fn collect_uses_in_stmt_suffix(stmt: &TypedStmt, target_id: NodeID, used: &mut FxHashSet<Symbol>) {
        match &stmt.kind {
            TypedStmtKind::Loop(_, body) => {
                Self::collect_uses_after(body, target_id, used);
            }
            _ => {}
        }
    }

    fn collect_uses_in_expr_suffix(expr: &TypedExpr, target_id: NodeID, used: &mut FxHashSet<Symbol>) {
        match &expr.kind {
            TypedExprKind::Block(block) => {
                Self::collect_uses_after(block, target_id, used);
            }
            TypedExprKind::If(_, conseq, alt) => {
                Self::collect_uses_after(conseq, target_id, used);
                Self::collect_uses_after(alt, target_id, used);
            }
            TypedExprKind::Match(_, arms) => {
                for arm in arms {
                    if arm.body.body.iter().any(|n| Self::node_contains_id(n, target_id)) {
                        Self::collect_uses_after(&arm.body, target_id, used);
                    }
                }
            }
            _ => {}
        }
    }

    fn collect_all_uses_in_node(node: &TypedNode, used: &mut FxHashSet<Symbol>) {
        match node {
            TypedNode::Expr(expr) => Self::collect_all_uses_in_expr(expr, used),
            TypedNode::Stmt(stmt) => Self::collect_all_uses_in_stmt(stmt, used),
            TypedNode::Decl(decl) => {
                if let TypedDeclKind::Let { initializer: Some(init), .. } = &decl.kind {
                    Self::collect_all_uses_in_expr(init, used);
                }
            }
        }
    }

    fn collect_all_uses_in_stmt(stmt: &TypedStmt, used: &mut FxHashSet<Symbol>) {
        match &stmt.kind {
            TypedStmtKind::Expr(expr) => Self::collect_all_uses_in_expr(expr, used),
            TypedStmtKind::Assignment(lhs, rhs) => {
                Self::collect_all_uses_in_expr(lhs, used);
                Self::collect_all_uses_in_expr(rhs, used);
            }
            TypedStmtKind::Return(Some(expr)) => Self::collect_all_uses_in_expr(expr, used),
            TypedStmtKind::Continue(Some(expr)) => Self::collect_all_uses_in_expr(expr, used),
            TypedStmtKind::Loop(cond, body) => {
                Self::collect_all_uses_in_expr(cond, used);
                for n in &body.body {
                    Self::collect_all_uses_in_node(n, used);
                }
            }
            _ => {}
        }
    }

    fn collect_all_uses_in_expr(expr: &TypedExpr, used: &mut FxHashSet<Symbol>) {
        match &expr.kind {
            TypedExprKind::Variable(sym) => {
                used.insert(*sym);
            }
            TypedExprKind::CallEffect { args, .. } => {
                for arg in args {
                    Self::collect_all_uses_in_expr(arg, used);
                }
            }
            TypedExprKind::Call { callee, args, .. } => {
                Self::collect_all_uses_in_expr(callee, used);
                for arg in args {
                    Self::collect_all_uses_in_expr(arg, used);
                }
            }
            TypedExprKind::Block(block) => {
                for n in &block.body {
                    Self::collect_all_uses_in_node(n, used);
                }
            }
            TypedExprKind::If(cond, conseq, alt) => {
                Self::collect_all_uses_in_expr(cond, used);
                for n in &conseq.body {
                    Self::collect_all_uses_in_node(n, used);
                }
                for n in &alt.body {
                    Self::collect_all_uses_in_node(n, used);
                }
            }
            TypedExprKind::Match(scrutinee, arms) => {
                Self::collect_all_uses_in_expr(scrutinee, used);
                for arm in arms {
                    for n in &arm.body.body {
                        Self::collect_all_uses_in_node(n, used);
                    }
                }
            }
            TypedExprKind::Member { receiver, .. } => {
                Self::collect_all_uses_in_expr(receiver, used);
            }
            TypedExprKind::Tuple(exprs) | TypedExprKind::LiteralArray(exprs) => {
                for e in exprs {
                    Self::collect_all_uses_in_expr(e, used);
                }
            }
            TypedExprKind::RecordLiteral { fields } => {
                for f in fields {
                    Self::collect_all_uses_in_expr(&f.value, used);
                }
            }
            _ => {}
        }
    }

    /// Add a yield point and create a new state for it
    pub fn add_yield_point(&mut self, expr_id: NodeID, effect: Symbol, live_vars: Vec<(Symbol, Ty)>) {
        let resume_state = self.states.len();

        self.yield_points.push(YieldPoint {
            expr_id,
            effect,
            live_vars: live_vars.clone(),
            resume_state,
        });

        self.states.push(StateInfo {
            index: resume_state,
            live_vars,
            from_yield: Some(self.yield_points.len() - 1),
        });
    }

    /// Check if this function has any yield points
    pub fn has_yields(&self) -> bool {
        !self.yield_points.is_empty()
    }

    /// Get the number of states
    pub fn state_count(&self) -> usize {
        self.states.len()
    }

    /// Get the yield point index for a given expression ID, if any
    pub fn yield_point_for_expr(&self, expr_id: NodeID) -> Option<usize> {
        self.yield_points.iter().position(|yp| yp.expr_id == expr_id)
    }
}

impl Default for EffectAnalysis {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node_id::FileID;

    #[test]
    fn test_new_analysis_has_initial_state() {
        let analysis = EffectAnalysis::new();
        assert_eq!(analysis.state_count(), 1);
        assert!(!analysis.has_yields());
    }

    #[test]
    fn test_add_yield_point_creates_state() {
        let mut analysis = EffectAnalysis::new();
        let expr_id = NodeID(FileID(0), 1);
        let effect = Symbol::Main; // Using Main as a placeholder

        analysis.add_yield_point(expr_id, effect, vec![]);

        assert_eq!(analysis.state_count(), 2);
        assert!(analysis.has_yields());
        assert_eq!(analysis.yield_points.len(), 1);
        assert_eq!(analysis.yield_points[0].resume_state, 1);
    }

    #[test]
    fn test_multiple_yield_points() {
        let mut analysis = EffectAnalysis::new();

        analysis.add_yield_point(NodeID(FileID(0), 1), Symbol::Main, vec![]);
        analysis.add_yield_point(NodeID(FileID(0), 2), Symbol::Main, vec![]);
        analysis.add_yield_point(NodeID(FileID(0), 3), Symbol::Main, vec![]);

        assert_eq!(analysis.state_count(), 4); // Initial + 3 yield points
        assert_eq!(analysis.yield_points.len(), 3);
        assert_eq!(analysis.yield_points[0].resume_state, 1);
        assert_eq!(analysis.yield_points[1].resume_state, 2);
        assert_eq!(analysis.yield_points[2].resume_state, 3);
    }

    #[test]
    fn test_yield_point_lookup() {
        let mut analysis = EffectAnalysis::new();
        let expr1 = NodeID(FileID(0), 10);
        let expr2 = NodeID(FileID(0), 20);

        analysis.add_yield_point(expr1, Symbol::Main, vec![]);
        analysis.add_yield_point(expr2, Symbol::Main, vec![]);

        assert_eq!(analysis.yield_point_for_expr(expr1), Some(0));
        assert_eq!(analysis.yield_point_for_expr(expr2), Some(1));
        assert_eq!(analysis.yield_point_for_expr(NodeID(FileID(0), 99)), None);
    }

    #[test]
    fn test_state_info_tracks_from_yield() {
        let mut analysis = EffectAnalysis::new();

        analysis.add_yield_point(NodeID(FileID(0), 1), Symbol::Main, vec![]);
        analysis.add_yield_point(NodeID(FileID(0), 2), Symbol::Main, vec![]);

        // Initial state has no from_yield
        assert_eq!(analysis.states[0].from_yield, None);

        // State 1 comes from yield 0
        assert_eq!(analysis.states[1].from_yield, Some(0));

        // State 2 comes from yield 1
        assert_eq!(analysis.states[2].from_yield, Some(1));
    }

    #[test]
    fn test_live_vars_stored_in_yield_point() {
        let mut analysis = EffectAnalysis::new();

        let live_vars = vec![
            (Symbol::Main, Ty::Int),
            (Symbol::Library, Ty::Bool),
        ];

        analysis.add_yield_point(NodeID(FileID(0), 1), Symbol::Main, live_vars.clone());

        assert_eq!(analysis.yield_points[0].live_vars, live_vars);
        assert_eq!(analysis.states[1].live_vars, live_vars);
    }

    #[test]
    fn test_live_vars_stored_in_state() {
        let mut analysis = EffectAnalysis::new();

        let live_vars1 = vec![(Symbol::Main, Ty::Int)];
        let live_vars2 = vec![
            (Symbol::Main, Ty::Int),
            (Symbol::Library, Ty::Bool),
        ];

        analysis.add_yield_point(NodeID(FileID(0), 1), Symbol::Main, live_vars1.clone());
        analysis.add_yield_point(NodeID(FileID(0), 2), Symbol::Main, live_vars2.clone());

        // State 0 has no live vars (initial state)
        assert!(analysis.states[0].live_vars.is_empty());

        // State 1 has live vars from yield 0
        assert_eq!(analysis.states[1].live_vars, live_vars1);

        // State 2 has live vars from yield 1
        assert_eq!(analysis.states[2].live_vars, live_vars2);
    }
}
