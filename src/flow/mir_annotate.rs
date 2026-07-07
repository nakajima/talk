//! Writing the flow checker's facts onto embedded typed nodes in checked MIR.
//! The CFG engine is the owner of per-point drop elaborations and runtime move
//! sets; this module only mirrors clone flags onto cloned typed nodes and
//! consume bits onto checked MIR reads so diagnostics and expression lowering
//! read the same typed facts.

use derive_visitor::{DriveMut, VisitorMut};
use rustc_hash::FxHashSet;

use crate::lower::mir;
use crate::node_id::NodeID;
use crate::typed_ast;

/// The flow checker's expression-node results for one module, borrowed for
/// annotation.
pub(crate) struct FlowResults<'a> {
    /// Expressions whose use consumes their place.
    pub(crate) consumed: &'a FxHashSet<NodeID>,
    /// Expressions that clone (an O(1) retain) instead of moving.
    pub(crate) auto_clones: &'a FxHashSet<NodeID>,
}

/// Bakes auto-clone flow results onto typed expression nodes. Non-consuming,
/// so the same results annotate the typed tree and every embedded copy of its
/// nodes inside MIR statements.
#[derive(VisitorMut)]
#[visitor(typed_ast::Expr(enter))]
pub(crate) struct Annotator<'a> {
    results: &'a FlowResults<'a>,
}

impl<'a> Annotator<'a> {
    pub(crate) fn new(results: &'a FlowResults<'a>) -> Self {
        Annotator { results }
    }

    fn enter_expr(&mut self, expr: &mut typed_ast::Expr) {
        if self.results.auto_clones.contains(&expr.id) {
            expr.ownership.auto_clone = true;
        }
    }
}

/// Mirror expression flags onto the typed-node copies embedded in one checked
/// MIR body. Candidate elaborations and move sets stay exactly as the CFG flow
/// pass wrote them.
pub(crate) fn annotate_flags_and_moves(body: &mut mir::Body, results: &FlowResults) {
    let mut annotator = Annotator::new(results);
    for block in &mut body.blocks {
        for statement in &mut block.statements {
            if let mir::Statement::Read { node, consumes, .. } = &mut statement.kind {
                *consumes = results.consumed.contains(node);
            }
            drive_embedded(&mut statement.kind, &mut annotator);
        }
        drive_terminator(&mut block.terminator, &mut annotator);
    }
}

/// Drive the annotator over every typed node a statement embeds (lowering
/// evaluates these copies, so they must carry the same clone facts as the tree
/// they were cloned from).
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

#[cfg(test)]
mod tests {
    use super::super::drops::{DropElaboration, DropReason};
    use super::*;
    use crate::typed_ast::ExprKind;

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
        for file in typed.phase.program.files().values() {
            for node in &file.roots {
                let typed_ast::Node::Decl(decl) = node else {
                    continue;
                };
                let typed_ast::DeclKind::Let { rhs: Some(rhs), .. } = &decl.kind else {
                    continue;
                };
                let ExprKind::Func(func) = &rhs.kind else {
                    continue;
                };
                bodies.push(
                    typed
                        .phase
                        .checked_mir
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
        // check: the concat temp is consumed by the binding (Dead), the
        // Int-typed take(s) temp stays unelaborated (nothing to drop),
        // and `s` moved into take(s) at the tail → Dead.
        assert_eq!(
            candidate_kinds(&bodies[1]),
            vec![
                (DropReason::TemporaryEnd, Some(DropElaboration::Dead)),
                (DropReason::TemporaryEnd, None),
                (DropReason::ScopeExit, Some(DropElaboration::Dead)),
            ],
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
            typed.phase.checked_mir.len() >= 2,
            "take and check are stored"
        );
        // Every stored function body carries the flow checker's drop
        // elaborations (the store was annotated in place, pre-lowering).
        let mut elaborated = 0;
        for file in typed.phase.program.files().values() {
            for node in &file.roots {
                let typed_ast::Node::Decl(decl) = node else {
                    continue;
                };
                let typed_ast::DeclKind::Let { rhs: Some(rhs), .. } = &decl.kind else {
                    continue;
                };
                let ExprKind::Func(func) = &rhs.kind else {
                    continue;
                };
                let body = typed
                    .phase
                    .checked_mir
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
    fn cfg_flow_records_runtime_move_sets() {
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
