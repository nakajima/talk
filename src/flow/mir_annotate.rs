//! Writing the flow checker's answers onto the MIR. The builder places
//! drop candidates structurally with empty elaborations; the CFG engine
//! classifies them per-point and then uses [`annotate_flags_and_moves`] to
//! stamp consume/auto-clone flags onto the statement-embedded expressions
//! and fill each statement's move set, so lowering reads everything off
//! the statement it walks. The schedule join ([`annotate_body`]) survives
//! only for lowering's standalone-body fallback, fed by the schedules the
//! engine records for statement-embedded blocks (handler bodies).

use derive_visitor::{DriveMut, VisitorMut};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::hir::{self, ExprKind};
use crate::lower::mir;
use crate::node_id::NodeID;

use super::drops::{DropReason, DropSchedule};
use super::place::{Place, place_for_expr};

/// The flow checker's results for one module, borrowed for annotation.
pub(crate) struct FlowResults<'a> {
    /// Scope-exit schedules by owning HIR block.
    pub(crate) block_drops: &'a FxHashMap<NodeID, Vec<DropSchedule>>,
    /// Early-exit and assignment-replace schedules by owning HIR statement.
    pub(crate) stmt_drops: &'a FxHashMap<NodeID, Vec<DropSchedule>>,
    /// Expressions whose use consumes their place.
    pub(crate) consumed: &'a FxHashSet<NodeID>,
    /// Expressions that clone (an O(1) retain) instead of moving.
    pub(crate) auto_clones: &'a FxHashSet<NodeID>,
}

/// Bakes flow results onto HIR nodes in place: schedules onto blocks and
/// statements, consume/auto-clone flags onto expressions. Non-consuming, so
/// the same results annotate the HIR tree and every embedded copy of its
/// nodes inside MIR statements.
#[derive(VisitorMut)]
#[visitor(hir::Block(enter), hir::Stmt(enter), hir::Expr(enter))]
pub(crate) struct Annotator<'a> {
    results: &'a FlowResults<'a>,
}

impl<'a> Annotator<'a> {
    pub(crate) fn new(results: &'a FlowResults<'a>) -> Self {
        Annotator { results }
    }

    fn enter_block(&mut self, block: &mut hir::Block) {
        if let Some(schedules) = self.results.block_drops.get(&block.id) {
            block.drops = schedules.clone();
        }
    }

    fn enter_stmt(&mut self, stmt: &mut hir::Stmt) {
        if let Some(schedules) = self.results.stmt_drops.get(&stmt.id) {
            stmt.drops = schedules.clone();
        }
    }

    fn enter_expr(&mut self, expr: &mut hir::Expr) {
        if self.results.consumed.contains(&expr.id) {
            expr.ownership.consumes = true;
        }
        if self.results.auto_clones.contains(&expr.id) {
            expr.ownership.auto_clone = true;
        }
    }
}

/// Annotate one MIR body in place from the flow results: embedded HIR nodes
/// get their flags and schedules, every statement gets its move set, and
/// every drop candidate gets its elaboration (joined from the schedules —
/// the standalone-body fallback; the CFG engine writes per-point
/// elaborations itself and uses [`annotate_flags_and_moves`]).
pub(crate) fn annotate_body(body: &mut mir::Body, results: &FlowResults) {
    annotate(body, results, true);
}

/// Flags, schedules-on-embedded-nodes, and move sets only — candidate
/// elaborations stay as written (the CFG engine's per-point results).
pub(crate) fn annotate_flags_and_moves(body: &mut mir::Body, results: &FlowResults) {
    annotate(body, results, false);
}

fn annotate(body: &mut mir::Body, results: &FlowResults, elaborate_candidates: bool) {
    let mut annotator = Annotator::new(results);
    for block in &mut body.blocks {
        for statement in &mut block.statements {
            if let mir::Statement::Read { node, consumes, .. } = &mut statement.kind {
                *consumes = results.consumed.contains(node);
            }
            drive_embedded(&mut statement.kind, &mut annotator);
            statement.ownership.moves = statement_moves(&statement.kind);
            if elaborate_candidates
                && let mir::Statement::DropCandidate {
                    target,
                    reason,
                    source,
                    ..
                } = &statement.kind
            {
                statement.ownership.drop = candidate_elaboration(results, *reason, *source, target);
            }
        }
        drive_terminator(&mut block.terminator, &mut annotator);
    }
}

/// The schedule elaborating a drop candidate, joined by the candidate's
/// source node, reason, and (for symbol targets) root symbol.
fn candidate_elaboration(
    results: &FlowResults,
    reason: DropReason,
    source: NodeID,
    target: &mir::DropTarget,
) -> Option<mir::DropElaborationResult> {
    let schedule = match reason {
        DropReason::ScopeExit => {
            let schedules = results.block_drops.get(&source)?;
            let mir::DropTarget::Symbol { symbol, .. } = target else {
                return None;
            };
            schedules
                .iter()
                .find(|schedule| schedule.place.root == *symbol)?
        }
        DropReason::EarlyExit => {
            let mir::DropTarget::Symbol { symbol, .. } = target else {
                return None;
            };
            results.stmt_drops.get(&source)?.iter().find(|schedule| {
                schedule.reason == DropReason::EarlyExit && schedule.place.root == *symbol
            })?
        }
        DropReason::AssignmentReplace => results
            .stmt_drops
            .get(&source)?
            .iter()
            .find(|schedule| schedule.reason == DropReason::AssignmentReplace)?,
    };
    Some(mir::DropElaborationResult {
        key_path: schedule.place.clone(),
        kind: schedule.kind,
    })
}

/// Drive the annotator over every HIR node a statement embeds (lowering
/// evaluates these copies, so they must carry the same annotations as the
/// tree they were cloned from).
fn drive_embedded(statement: &mut mir::Statement, annotator: &mut Annotator) {
    match statement {
        mir::Statement::Read { .. } => {}
        mir::Statement::ConsumeValue { expr }
        | mir::Statement::ReturnValue { expr, .. }
        | mir::Statement::ContinueValue { expr } => expr.drive_mut(annotator),
        mir::Statement::Bind { lhs, rhs, .. } => {
            lhs.drive_mut(annotator);
            if let Some(rhs) = rhs {
                rhs.drive_mut(annotator);
            }
        }
        mir::Statement::Assign { lhs, rhs, .. } => {
            lhs.drive_mut(annotator);
            rhs.drive_mut(annotator);
        }
        mir::Statement::DropCandidate {
            target: mir::DropTarget::Expr(expr),
            ..
        } => expr.drive_mut(annotator),
        mir::Statement::Call {
            expr,
            callee,
            args,
            trailing_block,
            ..
        } => {
            expr.drive_mut(annotator);
            callee.drive_mut(annotator);
            for arg in args {
                arg.drive_mut(annotator);
            }
            if let Some(block) = trailing_block {
                block.drive_mut(annotator);
            }
        }
        mir::Statement::Function { body, .. } => body.drive_mut(annotator),
        mir::Statement::Handling { stmt, body, .. } => {
            stmt.drive_mut(annotator);
            body.drive_mut(annotator);
        }
        mir::Statement::DeclBody { body } => body.drive_mut(annotator),
        mir::Statement::Perform { expr, .. } => expr.drive_mut(annotator),
        mir::Statement::ScopeEnter { .. }
        | mir::Statement::ScopeExit { .. }
        | mir::Statement::StorageLive { .. }
        | mir::Statement::StorageDead { .. }
        | mir::Statement::AssignmentRootUse { .. }
        | mir::Statement::DropCandidate { .. } => {}
    }
}

fn drive_terminator(terminator: &mut mir::Terminator, annotator: &mut Annotator) {
    match terminator {
        mir::Terminator::Handler { .. } => {}
        mir::Terminator::Branch { condition, .. } => condition.drive_mut(annotator),
        mir::Terminator::Switch {
            scrutinee,
            match_arms,
            ..
        } => {
            scrutinee.drive_mut(annotator);
            if let Some(arms) = match_arms {
                for arm in arms {
                    arm.drive_mut(annotator);
                }
            }
        }
        mir::Terminator::Loop { condition, .. } => {
            if let Some(condition) = condition {
                condition.drive_mut(annotator);
            }
        }
        mir::Terminator::Unset
        | mir::Terminator::Return
        | mir::Terminator::ReturnVoid
        | mir::Terminator::Jump(_)
        | mir::Terminator::Break
        | mir::Terminator::Continue => {}
    }
}

/// The places a statement moves, read off the `Expr.ownership.consumes`
/// flags on its embedded expressions (plus `[consuming]` closure captures).
/// Lowering clears these places' drop flags after the statement. The same
/// expression may be embedded in more than one statement; flag-clearing is
/// idempotent, so the duplication is harmless.
fn statement_moves(statement: &mir::Statement) -> Vec<Place> {
    let mut exprs: Vec<&hir::Expr> = vec![];
    match statement {
        mir::Statement::ConsumeValue { expr, .. }
        | mir::Statement::ReturnValue { expr, .. }
        | mir::Statement::ContinueValue { expr, .. } => exprs.push(expr),
        mir::Statement::Read {
            place: Some(place),
            consumes: true,
            ..
        } => return vec![place.clone()],
        mir::Statement::Bind { rhs: Some(rhs), .. } => exprs.push(rhs),
        mir::Statement::Assign { rhs, .. } => exprs.push(rhs),
        mir::Statement::Call { callee, args, .. } => {
            exprs.push(callee);
            exprs.extend(args.iter().map(|arg| &arg.value));
        }
        mir::Statement::Function { captures, .. } => {
            return captures
                .iter()
                .filter(|capture| {
                    matches!(capture.mode, crate::node_kinds::func::CaptureMode::Move)
                })
                .filter_map(|capture| capture.name.symbol().ok())
                .map(Place::root)
                .collect();
        }
        _ => {}
    }
    let mut moves = vec![];
    for expr in exprs {
        collect_consumed_places(expr, &mut moves);
    }
    moves
}

/// Collect the consumed places directly moved by this statement's
/// expression: a consumed place expression, or place-typed elements of
/// aggregate literals — exactly the legacy `collect_consumed_value_exprs`
/// recursion. Nested control flow, calls, and function bodies are NOT
/// descended: their moves ride their own statements, keeping drop-flag
/// clearing per-path precise.
fn collect_consumed_places(expr: &hir::Expr, out: &mut Vec<Place>) {
    if expr.ownership.consumes
        && let Some(key_path) = place_for_expr(expr)
    {
        out.push(key_path);
        return;
    }
    match &expr.kind {
        ExprKind::Tuple(items)
        | ExprKind::LiteralArray(items)
        | ExprKind::Con { args: items, .. } => {
            for item in items {
                collect_consumed_places(item, out);
            }
        }
        ExprKind::RecordLiteral { fields, spread } => {
            for field in fields {
                collect_consumed_places(&field.value, out);
            }
            if let Some(spread) = spread {
                collect_consumed_places(spread, out);
            }
        }
        _ => {}
    }
}

/// Schedules collected back off an annotated HIR subtree, for annotating a
/// MIR body built from it after the flow pass has already run (lowering's
/// build-on-miss path). Dies with stage 4, when the HIR no longer carries
/// drop annotations and every body comes annotated from the store.
#[derive(Default, derive_visitor::Visitor)]
#[visitor(hir::Block(enter), hir::Stmt(enter))]
pub(crate) struct CollectedSchedules {
    block_drops: FxHashMap<NodeID, Vec<DropSchedule>>,
    stmt_drops: FxHashMap<NodeID, Vec<DropSchedule>>,
}

impl CollectedSchedules {
    pub(crate) fn of_block(block: &hir::Block) -> Self {
        use derive_visitor::Drive;
        let mut collected = Self::default();
        block.drive(&mut collected);
        collected
    }

    fn enter_block(&mut self, block: &hir::Block) {
        if !block.drops.is_empty() {
            self.block_drops.insert(block.id, block.drops.clone());
        }
    }

    fn enter_stmt(&mut self, stmt: &hir::Stmt) {
        if !stmt.drops.is_empty() {
            self.stmt_drops.insert(stmt.id, stmt.drops.clone());
        }
    }
}

/// Annotate a MIR body from the annotations already present on the HIR
/// subtree it was built from (the standalone-body fallback).
pub(crate) fn annotate_body_from_hir(body: &mut mir::Body, collected: &CollectedSchedules) {
    let empty = FxHashSet::default();
    let results = FlowResults {
        block_drops: &collected.block_drops,
        stmt_drops: &collected.stmt_drops,
        consumed: &empty,
        auto_clones: &empty,
    };
    annotate_body(body, &results);
}

#[cfg(test)]
mod tests {
    use super::super::drops::DropElaboration;
    use super::*;

    /// The stored, flow-annotated body of every top-level function in
    /// `source` (checked through the real pipeline, core included), in
    /// source order.
    fn annotated_bodies(source: &'static str) -> Vec<std::sync::Arc<mir::Body>> {
        let typed = crate::compiling::driver::Driver::new(
            vec![crate::compiling::driver::Source::from(source)],
            crate::compiling::driver::DriverConfig::new("AnnotateTest"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
        let mut bodies = vec![];
        for file in typed.phase.hir.values() {
            for node in &file.roots {
                let hir::Node::Decl(decl) = node else {
                    continue;
                };
                let hir::DeclKind::Let { rhs: Some(rhs), .. } = &decl.kind else {
                    continue;
                };
                let ExprKind::Func(func) = &rhs.kind else {
                    continue;
                };
                bodies.push(
                    typed
                        .phase
                        .mir_bodies
                        .get(func.body.id)
                        .expect("function body stored"),
                );
            }
        }
        bodies
    }

    fn candidate_kinds(body: &mir::Body) -> Vec<(DropReason, Option<DropElaboration>)> {
        body.blocks
            .iter()
            .flat_map(|block| &block.statements)
            .filter_map(|statement| match &statement.kind {
                mir::Statement::DropCandidate { reason, .. } => Some((
                    *reason,
                    statement.ownership.drop.as_ref().map(|drop| drop.kind),
                )),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn stored_bodies_carry_per_point_candidate_elaborations() {
        let bodies = annotated_bodies(
            "func take(name: String) -> Int {\n\tname.byte_count\n}\nfunc check() -> Int {\n\tlet s = \"hello\" + \" world\"\n\ttake(s)\n}\ncheck()",
        );
        assert_eq!(bodies.len(), 2, "take and check");
        // take: the owned by-value parameter is live at exit → Static.
        assert_eq!(
            candidate_kinds(&bodies[0]),
            vec![(DropReason::ScopeExit, Some(DropElaboration::Static))],
            "{:#?}",
            bodies[0]
        );
        // check: `s` moved into take(s) at the tail → Dead.
        assert_eq!(
            candidate_kinds(&bodies[1]),
            vec![(DropReason::ScopeExit, Some(DropElaboration::Dead))],
            "{:#?}",
            bodies[1]
        );
    }

    #[test]
    fn driver_stores_annotated_bodies_at_type_check() {
        let typed = crate::compiling::driver::Driver::new(
            vec![crate::compiling::driver::Source::from(
                "func take(name: String) -> Int {\n\tname.byte_count\n}\nfunc check() -> Int {\n\tlet s = \"hello\" + \" world\"\n\ttake(s)\n}\ncheck()",
            )],
            crate::compiling::driver::DriverConfig::new("AnnotateTest"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
        assert!(
            typed.phase.mir_bodies.len() >= 2,
            "take and check are stored"
        );
        // Every stored function body carries the flow checker's drop
        // elaborations (the store was annotated in place, pre-lowering).
        let mut elaborated = 0;
        for file in typed.phase.hir.values() {
            for node in &file.roots {
                let hir::Node::Decl(decl) = node else {
                    continue;
                };
                let hir::DeclKind::Let { rhs: Some(rhs), .. } = &decl.kind else {
                    continue;
                };
                let ExprKind::Func(func) = &rhs.kind else {
                    continue;
                };
                let body = typed
                    .phase
                    .mir_bodies
                    .get(func.body.id)
                    .expect("function body stored");
                elaborated += body
                    .blocks
                    .iter()
                    .flat_map(|block| &block.statements)
                    .filter(|statement| statement.ownership.drop.is_some())
                    .count();
            }
        }
        assert!(elaborated >= 2, "stored bodies carry drop elaborations");
    }

    #[test]
    fn annotation_records_statement_moves() {
        let bodies = annotated_bodies(
            "func take(name: String) -> Int {\n\tname.byte_count\n}\nfunc check() -> Int {\n\tlet s = \"hello\" + \" world\"\n\ttake(s)\n}\ncheck()",
        );
        let moved: Vec<_> = bodies[1]
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .flat_map(|statement| &statement.ownership.moves)
            .collect();
        assert!(
            !moved.is_empty(),
            "take(s) moves s; the move set rides the statement: {:#?}",
            bodies[1]
        );
    }
}
