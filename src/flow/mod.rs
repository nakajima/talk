//! The flow checker: the small flow-sensitive companion to the type system's
//! substructural core. Permissions and grades live in types (`src/types`);
//! this pass answers only the flow-sensitive questions — where each value
//! moves, where borrows end, where drops go — and writes its answers onto the
//! HIR in place, per the annotated-tree architecture. It replaces
//! `src/ownership` (selected by `DriverConfig::checker`; the legacy checker
//! is deleted once this reaches parity).
//!
//! Scope so far: moves, use-after-move, copy exemption, unsafe gating.
//! Drop placement, loans/provenance, and capture inference land in later
//! phases.

pub mod drops;
mod grades;
mod moves;
pub mod place;
mod unsafe_gate;

#[cfg(test)]
mod flow_tests;

pub use place::Place;

use indexmap::IndexMap;

use crate::compiling::driver::Source;
use crate::compiling::module::ModuleId;
use crate::diagnostic::{AnyDiagnostic, Diagnostic, Severity};
use crate::hir::HirFile;
use crate::types::TypeOutput;

/// Check every file's HIR: move discipline per body, drop scheduling, raw-
/// pointer gating per file — and write the results onto the tree in place
/// (`Expr.ownership`, `Block::drops`, `Stmt::drops`). Diagnostics reuse the
/// legacy `OwnershipError` surface (message parity for free); the enum moves
/// here when the legacy checker is deleted.
pub fn check_flow(
    hir: &mut IndexMap<Source, HirFile>,
    types: &TypeOutput,
    module_id: ModuleId,
) -> Vec<AnyDiagnostic> {
    let mut checker = moves::MoveChecker::new(types);
    let mut file_drops = vec![];
    for file in hir.values() {
        let mut state = Default::default();
        file_drops.push(checker.check_roots(&file.roots, &mut state));
    }
    let mut errors = checker.errors;
    errors.extend(unsafe_gate::check(hir, module_id));

    // Bake the analysis onto the tree: this map dies here — downstream
    // stages read the annotations, never a side table.
    let mut annotator = Annotator {
        block_drops: checker.block_drops,
        stmt_drops: checker.stmt_drops,
        consumed: checker.consumed,
    };
    for (file, drops) in hir.values_mut().zip(file_drops) {
        file.drops = drops;
        for root in &mut file.roots {
            use derive_visitor::DriveMut;
            root.drive_mut(&mut annotator);
        }
    }

    errors
        .into_iter()
        .map(|(kind, id)| {
            AnyDiagnostic::Ownership(Diagnostic {
                id,
                severity: Severity::Error,
                kind,
            })
        })
        .collect()
}

#[derive(derive_visitor::VisitorMut)]
#[visitor(crate::hir::Block(enter), crate::hir::Stmt(enter), crate::hir::Expr(enter))]
struct Annotator {
    block_drops: rustc_hash::FxHashMap<crate::node_id::NodeID, Vec<drops::DropSchedule>>,
    stmt_drops: rustc_hash::FxHashMap<crate::node_id::NodeID, Vec<drops::DropSchedule>>,
    consumed: rustc_hash::FxHashSet<crate::node_id::NodeID>,
}

impl Annotator {
    fn enter_block(&mut self, block: &mut crate::hir::Block) {
        if let Some(schedules) = self.block_drops.remove(&block.id) {
            block.drops = schedules;
        }
    }

    fn enter_stmt(&mut self, stmt: &mut crate::hir::Stmt) {
        if let Some(schedules) = self.stmt_drops.remove(&stmt.id) {
            stmt.drops = schedules;
        }
    }

    fn enter_expr(&mut self, expr: &mut crate::hir::Expr) {
        if self.consumed.contains(&expr.id) {
            expr.ownership.consumes = true;
        }
    }
}
