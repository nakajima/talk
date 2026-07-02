//! Move checking: a flow-sensitive walk over HIR bodies tracking which
//! places have been consumed. HIR control flow is structured (no gotos), so
//! instead of the legacy MIR worklist this is a direct walk: branches check
//! against clones of the incoming state and union at the join (a value moved
//! on any path is moved after it — the legacy `MoveState::merge_from`
//! pessimism), and loop bodies are walked twice so back-edge moves are seen
//! (errors dedup, so the second pass is harmless).
//!
//! What consumes a value is the legacy rule set verbatim: binding rhs,
//! assignment rhs, by-value call argument, by-value/consuming receiver,
//! return/continue value, discarded statement value, aggregate-literal
//! element, `[consuming]` capture. A consume only moves when the type needs
//! a drop (`GradeView::needs_drop`); copy types never move.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::hir::{self, ExprKind};
use crate::node_id::NodeID;
use crate::ownership::OwnershipError;
use crate::types::TypeOutput;
use crate::types::output::stored_field_symbol;
use crate::types::ty::Ty;

use super::drops::{DropElaboration, DropReason, DropSchedule};
use super::grades::GradeView;
use super::place::Place;

#[derive(Clone, Default)]
pub(crate) struct MoveState {
    /// May-moved (or uninitialized) places — union at joins; drives
    /// use-after-move errors and the Conditional/Open drop kinds.
    moved: FxHashMap<Place, (NodeID, Ty)>,
    /// Must-moved places — intersection at joins; a must-moved place's
    /// scope-exit drop is Dead.
    moved_all: FxHashSet<Place>,
    /// Definitely-initialized places — intersection at joins.
    initialized_all: FxHashSet<Place>,
    /// Maybe-initialized places — union at joins.
    initialized_any: FxHashSet<Place>,
}

impl MoveState {
    /// CFG-join: may-sets union, must-sets intersect (the legacy
    /// `MoveState`/`DropState` merge semantics in one place).
    fn merge_from(&mut self, other: &MoveState) {
        for (place, fact) in &other.moved {
            self.moved.entry(place.clone()).or_insert_with(|| fact.clone());
        }
        self.moved_all.retain(|place| other.moved_all.contains(place));
        self.initialized_all
            .retain(|place| other.initialized_all.contains(place));
        self.initialized_any
            .extend(other.initialized_any.iter().cloned());
    }

    /// Re-initialize a place (binding or assignment target): the place and
    /// all its sub-places are live again.
    fn restore(&mut self, place: &Place) {
        self.moved.retain(|moved, _| !place.contains(moved));
        self.moved_all.retain(|moved| !place.contains(moved));
        self.initialized_all.insert(place.clone());
        self.initialized_any.insert(place.clone());
    }

    fn note_move(&mut self, place: Place, node: NodeID, ty: Ty) {
        self.moved_all.insert(place.clone());
        self.moved.insert(place, (node, ty));
    }

    /// A local left its scope: forget everything rooted at it.
    fn finish_local(&mut self, place: &Place) {
        self.moved.retain(|moved, _| !place.contains(moved));
        self.moved_all.retain(|moved| !place.contains(moved));
        self.initialized_all.retain(|init| !place.contains(init));
        self.initialized_any.retain(|init| !place.contains(init));
    }

    /// The moved entry that makes `use_place` invalid, if any: a moved
    /// ancestor covers any use; a moved sub-place blocks whole-value
    /// (owned) uses only.
    fn moved_for_use(&self, use_place: &Place, use_is_owned: bool) -> Option<(&Place, &(NodeID, Ty))> {
        self.moved.iter().find(|(moved, _)| {
            moved.contains(use_place) || (use_is_owned && use_place.contains(moved))
        })
    }
}

/// The legacy `classify_drop` rule, verbatim: how a scheduled drop of
/// `place` lowers given the state at the drop point.
fn classify(place: &Place, state: &MoveState) -> DropElaboration {
    if state.moved_all.contains(place) {
        return DropElaboration::Dead;
    }
    if state
        .moved
        .keys()
        .any(|moved| place.contains(moved) && moved != place)
    {
        return DropElaboration::Open;
    }
    if state
        .initialized_all
        .iter()
        .any(|init| init.contains(place))
        && !state.moved.contains_key(place)
    {
        return DropElaboration::Static;
    }
    if state
        .initialized_any
        .iter()
        .any(|init| init.contains(place))
    {
        return DropElaboration::Conditional;
    }
    DropElaboration::Dead
}

/// One scope's tracked locals, in declaration order.
struct ScopeFrame {
    block_id: NodeID,
    locals: Vec<ScopeLocal>,
}

#[derive(Clone)]
struct ScopeLocal {
    symbol: crate::name_resolution::symbol::Symbol,
    binder: NodeID,
    ty: Ty,
}

pub(crate) struct MoveChecker<'a> {
    pub(crate) types: &'a TypeOutput,
    pub(crate) grades: GradeView<'a>,
    pub(crate) errors: Vec<(OwnershipError, NodeID)>,
    reported: FxHashSet<(NodeID, String)>,
    /// Enclosing scopes of the body being walked, outermost first.
    scopes: Vec<ScopeFrame>,
    /// Drop schedules by owning HIR block / statement, written onto the tree
    /// after the walk (see `flow::annotate`).
    pub(crate) block_drops: FxHashMap<NodeID, Vec<DropSchedule>>,
    pub(crate) stmt_drops: FxHashMap<NodeID, Vec<DropSchedule>>,
    /// Expressions whose use consumes their place.
    pub(crate) consumed: FxHashSet<NodeID>,
}

impl<'a> MoveChecker<'a> {
    pub(crate) fn new(types: &'a TypeOutput) -> Self {
        MoveChecker {
            types,
            grades: GradeView::new(types),
            errors: vec![],
            reported: FxHashSet::default(),
            scopes: vec![],
            block_drops: FxHashMap::default(),
            stmt_drops: FxHashMap::default(),
            consumed: FxHashSet::default(),
        }
    }

    fn error(&mut self, error: OwnershipError, node: NodeID) {
        if self.reported.insert((node, error.to_string())) {
            self.errors.push((error, node));
        }
    }

    // ----- Bodies -----------------------------------------------------------

    /// Check a function body: fresh state, fresh scope stack (an inner body's
    /// early exits do not drop its parent's locals).
    pub(crate) fn check_body(&mut self, block: &hir::Block) {
        let outer_scopes = std::mem::take(&mut self.scopes);
        let mut state = MoveState::default();
        self.walk_block(block, &mut state);
        self.scopes = outer_scopes;
    }

    /// Check a file's top-level roots as one body (the file is the top-level
    /// scope), descending into every nested function declaration along the
    /// way. Returns the file's scope-exit drop schedules.
    pub(crate) fn check_roots(
        &mut self,
        roots: &[hir::Node],
        state: &mut MoveState,
    ) -> Vec<DropSchedule> {
        self.scopes.push(ScopeFrame {
            // The file scope has no HIR node; its schedules return to the
            // caller (annotated onto the `HirFile`) instead of `block_drops`.
            block_id: NodeID::SYNTHESIZED,
            locals: vec![],
        });
        let diverges = self.walk_block_nodes(roots, state);
        let Some(frame) = self.scopes.pop() else {
            unreachable!("file scope frame pushed above")
        };
        let mut schedules = vec![];
        if diverges == Diverges::No {
            for local in frame.locals.iter().rev().cloned().collect::<Vec<_>>() {
                self.schedule_drop(&local, DropReason::ScopeExit, state, &mut schedules);
            }
        }
        for local in &frame.locals {
            state.finish_local(&Place::root(local.symbol));
        }
        schedules
    }

    /// Function declarations reachable from a node list: their bodies are
    /// independent (fresh state); their capture lists act on `state`.
    fn check_decl(&mut self, decl: &hir::Decl, state: &mut MoveState) {
        match &decl.kind {
            hir::DeclKind::Func(func) => {
                self.apply_captures(func, state);
                self.check_body(&func.body);
            }
            hir::DeclKind::Method { func, .. } => self.check_body(&func.body),
            hir::DeclKind::Init { body, .. } => self.check_body(body),
            hir::DeclKind::Struct { body, .. }
            | hir::DeclKind::Enum { body, .. }
            | hir::DeclKind::Extend { body, .. }
            | hir::DeclKind::Protocol { body, .. } => {
                for member in &body.decls {
                    self.check_decl(member, state);
                }
            }
            hir::DeclKind::Let { lhs, rhs, .. } => self.check_let(lhs, rhs.as_ref(), state),
            hir::DeclKind::Property {
                default_value: Some(value),
                ..
            } => {
                self.consume_expr(value, state);
            }
            _ => {}
        }
    }

    fn check_let(&mut self, lhs: &hir::Pattern, rhs: Option<&hir::Expr>, state: &mut MoveState) {
        if let Some(rhs) = rhs {
            self.consume_expr(rhs, state);
        }
        // A single-binder let's type is its rhs type; destructuring binders
        // carry their own node types.
        let whole_binding_ty = match (&lhs.kind, rhs) {
            (hir::PatternKind::Bind(_), Some(rhs)) => Some(rhs.ty.clone()),
            _ => None,
        };
        for (id, binder) in lhs.collect_binders() {
            let ty = self
                .types
                .node_types
                .get(&id)
                .cloned()
                .or_else(|| whole_binding_ty.clone())
                .unwrap_or(Ty::Error);
            if let Some(frame) = self.scopes.last_mut() {
                frame.locals.push(ScopeLocal {
                    symbol: binder,
                    binder: id,
                    ty: ty.clone(),
                });
            }
            let place = Place::root(binder);
            if rhs.is_some() {
                state.restore(&place);
            } else {
                // `let s: String` with no initializer: the binder starts
                // uninitialized, which the move lattice models as moved.
                state.note_move(place, id, ty);
            }
        }
    }

    // ----- Drop scheduling ----------------------------------------------------

    /// Schedule one drop of a scope local at the current state, reporting
    /// the linear must-consume error when a linear value would be dropped.
    fn schedule_drop(
        &mut self,
        local: &ScopeLocal,
        reason: DropReason,
        state: &MoveState,
        out: &mut Vec<DropSchedule>,
    ) {
        if !self.grades.needs_drop(&local.ty) {
            return;
        }
        let place = Place::root(local.symbol);
        let kind = classify(&place, state);
        if kind != DropElaboration::Dead && self.ty_is_linear(&local.ty) {
            let error = OwnershipError::LinearNotConsumed {
                name: render_place(&place, self.types),
                ty: local.ty.render_mono(),
            };
            self.error(error, local.binder);
        }
        out.push(DropSchedule {
            place,
            ty: local.ty.clone(),
            kind,
            reason,
        });
    }

    fn ty_is_linear(&self, ty: &Ty) -> bool {
        use crate::types::catalog::Grade;
        matches!(ty, Ty::Nominal(symbol, _)
            if self.types.catalog.grade_of(*symbol) == Grade::Linear)
    }

    /// Early exit (`return`/`break`/`continue`): every enclosing scope's
    /// locals drop, innermost scope first, reverse declaration order within
    /// each (matching the legacy MIR builder's `emit_early_exit_drops`).
    fn schedule_early_exit_drops(&mut self, stmt_id: NodeID, state: &MoveState) {
        let locals: Vec<ScopeLocal> = self
            .scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.locals.iter().rev().cloned())
            .collect();
        let mut schedules = vec![];
        for local in &locals {
            self.schedule_drop(local, DropReason::EarlyExit, state, &mut schedules);
        }
        self.stmt_drops.insert(stmt_id, schedules);
    }

    // ----- Statement/node walk ----------------------------------------------

    /// Walk a block's nodes in order. Statements after a `return`/`break`/
    /// `continue` are unreachable and skipped (no fallthrough edge).
    fn walk_block_nodes(&mut self, nodes: &[hir::Node], state: &mut MoveState) -> Diverges {
        for (index, node) in nodes.iter().enumerate() {
            let is_last = index + 1 == nodes.len();
            let diverges = match node {
                hir::Node::Decl(decl) => {
                    self.check_decl(decl, state);
                    Diverges::No
                }
                hir::Node::Stmt(stmt) => self.walk_stmt(stmt, state),
                // Every expression node's value is consumed: a trailing
                // expression feeds the block's value, an interior one is
                // discarded (and dropped) — both are consume sites.
                hir::Node::Expr(expr) => {
                    let _ = is_last;
                    self.consume_expr(expr, state);
                    Diverges::No
                }
            };
            if diverges == Diverges::Yes {
                return Diverges::Yes;
            }
        }
        Diverges::No
    }

    fn walk_stmt(&mut self, stmt: &hir::Stmt, state: &mut MoveState) -> Diverges {
        match &stmt.kind {
            hir::StmtKind::Expr(expr) => {
                self.consume_expr(expr, state);
                Diverges::No
            }
            hir::StmtKind::If(cond, then_block, else_block) => {
                self.walk_expr(cond, state);
                let mut then_state = state.clone();
                let then_diverges = self.walk_block(then_block, &mut then_state);
                let mut else_state = state.clone();
                let else_diverges = match else_block {
                    Some(else_block) => self.walk_block(else_block, &mut else_state),
                    None => Diverges::No,
                };
                // Only paths that fall through reach the join.
                let mut merged = false;
                if then_diverges == Diverges::No {
                    state.merge_from(&then_state);
                    merged = true;
                }
                if else_diverges == Diverges::No {
                    state.merge_from(&else_state);
                    merged = true;
                }
                if merged || else_block.is_none() {
                    Diverges::No
                } else {
                    Diverges::Yes
                }
            }
            hir::StmtKind::Return(value) => {
                if let Some(value) = value {
                    if contains_borrow(&value.ty) {
                        self.walk_expr(value, state);
                    } else {
                        self.consume_expr(value, state);
                    }
                }
                self.schedule_early_exit_drops(stmt.id, state);
                Diverges::Yes
            }
            hir::StmtKind::Break => {
                self.schedule_early_exit_drops(stmt.id, state);
                Diverges::Yes
            }
            hir::StmtKind::Continue(value) => {
                if let Some(value) = value {
                    self.consume_expr(value, state);
                }
                self.schedule_early_exit_drops(stmt.id, state);
                Diverges::Yes
            }
            hir::StmtKind::Assignment(lhs, rhs) => {
                self.check_assignment(stmt.id, lhs, rhs, state);
                Diverges::No
            }
            hir::StmtKind::Loop(cond, body) => {
                // Two passes: the first surfaces the body's move effects for
                // the back edge, the second reports with loop-carried state.
                // Errors dedup, so double-reporting is harmless.
                for _ in 0..2 {
                    if let Some(cond) = cond {
                        self.walk_expr(cond, state);
                    }
                    let mut body_state = state.clone();
                    self.walk_block(body, &mut body_state);
                    state.merge_from(&body_state);
                }
                Diverges::No
            }
            hir::StmtKind::Handling { body, .. } => {
                // A handler body runs zero or more times; its move effects
                // propagate to the parent (legacy nested-body exit merge).
                let mut body_state = state.clone();
                self.walk_block(body, &mut body_state);
                state.merge_from(&body_state);
                Diverges::No
            }
        }
    }

    /// Walk a block as a scope: track its locals and, on the fallthrough
    /// exit, schedule their drops in reverse declaration order.
    fn walk_block(&mut self, block: &hir::Block, state: &mut MoveState) -> Diverges {
        self.scopes.push(ScopeFrame {
            block_id: block.id,
            locals: vec![],
        });
        let diverges = self.walk_block_nodes(&block.body, state);
        let Some(frame) = self.scopes.pop() else {
            unreachable!("scope frame pushed above")
        };
        if diverges == Diverges::No {
            let mut schedules = vec![];
            for local in frame.locals.iter().rev().cloned().collect::<Vec<_>>() {
                self.schedule_drop(&local, DropReason::ScopeExit, state, &mut schedules);
            }
            self.block_drops.insert(frame.block_id, schedules);
        }
        for local in &frame.locals {
            state.finish_local(&Place::root(local.symbol));
        }
        diverges
    }

    fn check_assignment(
        &mut self,
        stmt_id: NodeID,
        lhs: &hir::Expr,
        rhs: &hir::Expr,
        state: &mut MoveState,
    ) {
        self.consume_expr(rhs, state);
        if let Some(place) = self.place(lhs) {
            // Writing through a moved root is a use of the moved value
            // (`person.name = x` after `person` moved), but assigning to the
            // moved place itself re-initializes it.
            let root = Place::root(place.root);
            if let Some((moved, (_, ty))) = state.moved_for_use(&root, false)
                && !place.contains(moved)
            {
                let error = OwnershipError::UseAfterMove {
                    name: render_place(moved, self.types),
                    ty: ty.render_mono(),
                };
                self.error(error, lhs.id);
            }
            // The old value is replaced: drop it first (classified at the
            // pre-assignment state, so a moved-out place drops Dead).
            if self.grades.needs_drop(&lhs.ty) {
                let kind = classify(&place, state);
                self.stmt_drops.entry(stmt_id).or_default().push(DropSchedule {
                    place: place.clone(),
                    ty: lhs.ty.clone(),
                    kind,
                    reason: DropReason::AssignmentReplace,
                });
            }
            state.restore(&place);
        } else {
            self.walk_expr(lhs, state);
        }
    }

    // ----- Expression walk ---------------------------------------------------

    /// Walk an expression whose value is consumed by its context: a place is
    /// moved (if owned), an aggregate literal consumes its elements, and
    /// anything else evaluates normally (its interior consume sites are its
    /// own).
    fn consume_expr(&mut self, expr: &hir::Expr, state: &mut MoveState) {
        if let Some(place) = self.place(expr) {
            self.move_place(expr, place, state);
            return;
        }
        match &expr.kind {
            ExprKind::Tuple(items) | ExprKind::LiteralArray(items) => {
                for item in items {
                    self.consume_expr(item, state);
                }
            }
            ExprKind::RecordLiteral { fields, spread } => {
                for field in fields {
                    self.consume_expr(&field.value, state);
                }
                if let Some(spread) = spread {
                    self.consume_expr(spread, state);
                }
            }
            ExprKind::As(inner, _) => self.consume_expr(inner, state),
            ExprKind::Block(block) => {
                self.walk_block(block, state);
            }
            ExprKind::If(cond, then_block, else_block) => {
                self.walk_expr(cond, state);
                let mut then_state = state.clone();
                let then_diverges = self.walk_block(then_block, &mut then_state);
                let mut else_state = state.clone();
                let else_diverges = self.walk_block(else_block, &mut else_state);
                if then_diverges == Diverges::No {
                    state.merge_from(&then_state);
                }
                if else_diverges == Diverges::No {
                    state.merge_from(&else_state);
                }
            }
            ExprKind::Match(scrutinee, arms) => {
                self.consume_expr(scrutinee, state);
                let entry = state.clone();
                for arm in arms {
                    let mut arm_state = entry.clone();
                    if self.walk_block(&arm.body, &mut arm_state) == Diverges::No {
                        state.merge_from(&arm_state);
                    }
                }
            }
            _ => self.walk_expr(expr, state),
        }
    }

    /// Walk an expression for its uses (reads); consume sites inside it
    /// (call arguments, receivers, aggregate elements) apply their own rules.
    fn walk_expr(&mut self, expr: &hir::Expr, state: &mut MoveState) {
        if let Some(place) = self.place(expr) {
            self.check_use(expr, &place, false, state);
            return;
        }
        match &expr.kind {
            ExprKind::Call {
                callee,
                args,
                trailing_block,
                ..
            } => {
                self.check_call(expr, callee, args, trailing_block.as_ref(), state);
            }
            ExprKind::CallEffect { args, .. } => {
                for arg in args {
                    self.consume_expr(&arg.value, state);
                }
            }
            ExprKind::Member(Some(receiver), _) => self.walk_expr(receiver, state),
            ExprKind::Member(None, _) | ExprKind::Variable(_) | ExprKind::Constructor(_) => {}
            ExprKind::Tuple(items) | ExprKind::LiteralArray(items) => {
                for item in items {
                    self.consume_expr(item, state);
                }
            }
            ExprKind::RecordLiteral { fields, spread } => {
                for field in fields {
                    self.consume_expr(&field.value, state);
                }
                if let Some(spread) = spread {
                    self.consume_expr(spread, state);
                }
            }
            ExprKind::As(inner, _) => self.walk_expr(inner, state),
            ExprKind::Block(block) => {
                self.walk_block(block, state);
            }
            ExprKind::If(cond, then_block, else_block) => {
                self.walk_expr(cond, state);
                let mut then_state = state.clone();
                let then_diverges = self.walk_block(then_block, &mut then_state);
                let mut else_state = state.clone();
                let else_diverges = self.walk_block(else_block, &mut else_state);
                if then_diverges == Diverges::No {
                    state.merge_from(&then_state);
                }
                if else_diverges == Diverges::No {
                    state.merge_from(&else_state);
                }
            }
            ExprKind::Match(scrutinee, arms) => {
                self.consume_expr(scrutinee, state);
                let entry = state.clone();
                for arm in arms {
                    let mut arm_state = entry.clone();
                    if self.walk_block(&arm.body, &mut arm_state) == Diverges::No {
                        state.merge_from(&arm_state);
                    }
                }
            }
            ExprKind::Func(func) => {
                self.apply_captures(func, state);
                self.check_body(&func.body);
            }
            ExprKind::InlineIR(ir) => {
                for bind in &ir.binds {
                    self.walk_expr(bind, state);
                }
            }
            ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_)
            | ExprKind::RowVariable(_) => {}
        }
    }

    fn check_call(
        &mut self,
        _call: &hir::Expr,
        callee: &hir::Expr,
        args: &[hir::CallArg],
        trailing_block: Option<&hir::Block>,
        state: &mut MoveState,
    ) {
        // Receiver: a borrowed self parameter (from the method's scheme, which
        // is self-first) reads; a by-value/`consuming` self consumes. A member
        // that is a stored field being *called* is a closure-typed field, not
        // a method — its receiver reads.
        let mut value_params: Option<Vec<Ty>> = None;
        if let ExprKind::Member(Some(receiver), _) = &callee.kind {
            if self.field_place(callee).is_some() {
                self.walk_expr(callee, state);
            } else {
                let method_params = self.member_callable_params(callee);
                let self_param_is_borrow = method_params
                    .as_ref()
                    .and_then(|params| params.first())
                    .is_some_and(|param| matches!(param, Ty::Borrow(..)));
                if self_param_is_borrow {
                    self.walk_expr(receiver, state);
                } else {
                    self.consume_expr(receiver, state);
                }
                value_params =
                    method_params.map(|params| params.get(1..).unwrap_or(&[]).to_vec());
            }
        } else {
            self.walk_expr(callee, state);
        }
        let params = value_params.unwrap_or_else(|| callee_params(callee));

        let borrowed_constructor = matches!(callee.kind, ExprKind::Constructor(_))
            && !self.grades.needs_drop(&result_ty(callee));

        for (index, arg) in args.iter().enumerate() {
            let param = params.get(index);
            let param_is_borrow = param.is_some_and(|param| matches!(param, Ty::Borrow(..)));
            if param_is_borrow || borrowed_constructor {
                self.walk_expr(&arg.value, state);
            } else {
                self.consume_expr(&arg.value, state);
            }
        }

        if let Some(block) = trailing_block {
            // A trailing block body runs inside the callee; its move effects
            // propagate to the parent (legacy nested-body exit merge).
            let mut body_state = state.clone();
            self.walk_block(block, &mut body_state);
            state.merge_from(&body_state);
        }
    }

    /// The full self-first parameter list of a member call's method, from
    /// the resolved member's scheme (the callee expression's own type is the
    /// bound-method type with self already stripped).
    fn member_callable_params(&self, callee: &hir::Expr) -> Option<Vec<Ty>> {
        use crate::types::output::MemberResolution;
        match callee.member_resolution.as_ref()? {
            MemberResolution::Direct(symbol) => self
                .types
                .schemes
                .get(symbol)
                .and_then(|scheme| func_params(&scheme.ty)),
            MemberResolution::ViaConformance { protocol, witness } => self
                .types
                .schemes
                .get(witness)
                .and_then(|scheme| func_params(&scheme.ty))
                .or_else(|| {
                    let ExprKind::Member(_, label) = &callee.kind else {
                        return None;
                    };
                    self.types
                        .catalog
                        .requirement_in(*protocol, &label.to_string())
                        .and_then(|(_, requirement)| func_params(&requirement.sig))
                }),
        }
    }

    /// Whether the member expression is a stored field access (a place),
    /// as opposed to a method reference.
    fn field_place(&self, expr: &hir::Expr) -> Option<Place> {
        self.place(expr)
    }

    fn apply_captures(&mut self, func: &hir::Func, state: &mut MoveState) {
        for capture in &func.captures {
            let Ok(symbol) = capture.name.symbol() else {
                continue;
            };
            let place = Place::root(symbol);
            let is_move = matches!(capture.mode, crate::node_kinds::func::CaptureMode::Move);
            if let Some((moved, (_, ty))) = state.moved_for_use(&place, is_move) {
                let error = OwnershipError::UseAfterMove {
                    name: render_place(moved, self.types),
                    ty: ty.render_mono(),
                };
                self.error(error, func.id);
            }
            if is_move {
                let ty = self
                    .types
                    .schemes
                    .get(&symbol)
                    .map(|scheme| scheme.ty.clone())
                    .unwrap_or(Ty::Error);
                state.moved.insert(place, (func.id, ty));
            }
        }
    }

    // ----- Places, uses, moves ------------------------------------------------

    /// The place an expression names, if it is one: a variable, or a chain
    /// of stored-field accesses off one.
    fn place(&self, expr: &hir::Expr) -> Option<Place> {
        match &expr.kind {
            ExprKind::Variable(name) => name.symbol().ok().map(Place::root),
            ExprKind::Member(Some(receiver), _) => {
                let field = stored_field_symbol(self.types, expr.member_resolution.as_ref())?;
                Some(self.place(receiver)?.child(field))
            }
            _ => None,
        }
    }

    fn check_use(
        &mut self,
        expr: &hir::Expr,
        place: &Place,
        use_is_owned: bool,
        state: &MoveState,
    ) {
        if let Some((moved, (_, ty))) = state.moved_for_use(place, use_is_owned) {
            let error = OwnershipError::UseAfterMove {
                name: render_place(moved, self.types),
                ty: ty.render_mono(),
            };
            self.error(error, expr.id);
        }
    }

    fn move_place(&mut self, expr: &hir::Expr, place: Place, state: &mut MoveState) {
        let owned = self.grades.needs_drop(&expr.ty);
        self.check_use(expr, &place, owned, state);
        if owned && tracked_root(place.root) {
            self.consumed.insert(expr.id);
            state.note_move(place, expr.id, expr.ty.clone());
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum Diverges {
    No,
    Yes,
}

fn tracked_root(root: crate::name_resolution::symbol::Symbol) -> bool {
    use crate::name_resolution::symbol::Symbol;
    matches!(
        root,
        Symbol::DeclaredLocal(_)
            | Symbol::PatternBindLocal(_)
            | Symbol::ParamLocal(_)
            | Symbol::Global(_)
    )
}

fn contains_borrow(ty: &Ty) -> bool {
    use std::ops::ControlFlow;
    ty.try_visit(&mut |t| {
        if matches!(t, Ty::Borrow(..)) {
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(())
        }
    })
    .is_break()
}

/// The callee expression's own parameter types (no self).
fn callee_params(callee: &hir::Expr) -> Vec<Ty> {
    func_params(&callee.ty).unwrap_or_default()
}

fn func_params(ty: &Ty) -> Option<Vec<Ty>> {
    match ty {
        Ty::Func(params, ..) => Some(params.clone()),
        _ => None,
    }
}

/// A constructor call's produced type (the function's return).
fn result_ty(callee: &hir::Expr) -> Ty {
    match &callee.ty {
        Ty::Func(_, ret, _) => (**ret).clone(),
        other => other.clone(),
    }
}

fn render_place(place: &Place, types: &TypeOutput) -> String {
    let mut out = render_symbol(place.root, types);
    for field in &place.fields {
        out.push('.');
        out.push_str(&render_symbol(*field, types));
    }
    out
}

fn render_symbol(symbol: crate::name_resolution::symbol::Symbol, types: &TypeOutput) -> String {
    types
        .display_names
        .get(&symbol)
        .map(|name| name.to_string())
        .unwrap_or_else(|| format!("{symbol}"))
}
