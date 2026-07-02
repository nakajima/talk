//! The flow checker: the small flow-sensitive companion to the type system's
//! substructural core. Permissions and grades live in types (`src/types`);
//! this pass answers only the flow-sensitive questions — where each value
//! moves, where borrows end, where drops go — and writes its answers onto the
//! HIR in place, per the annotated-tree architecture: moves, drops (with
//! linear must-consume), loans/provenance (NLL borrow ends at last use),
//! closure captures, and raw-pointer gating.

mod captures;
pub mod drops;
pub mod errors;
pub(crate) mod grades;
mod liveness;
mod loans;
mod moves;
pub mod place;
mod unsafe_gate;

#[cfg(test)]
mod flow_borrow_tests;
#[cfg(test)]
mod flow_tests;

pub use errors::OwnershipError;
pub use place::{Place, place_for_expr};

use indexmap::IndexMap;

/// Editor-facing facts the flow checker accumulates while walking: what
/// moves, what borrows, what drops — with the nodes to anchor hints and
/// hover details. A product for the analysis layer, not a compiler stage
/// input (lowering reads the HIR annotations, never this).
#[derive(Clone, Debug, Default)]
pub struct FlowFacts {
    pub moves: Vec<FlowMoveFact>,
    pub borrows: Vec<FlowBorrowFact>,
    pub drops: Vec<FlowDropFact>,
    /// Silent CheapClone sites (tier 2): the value is cloned — an O(1)
    /// buffer retain — instead of moved or borrowed.
    pub clones: Vec<FlowCloneFact>,
}

#[derive(Clone, Debug)]
pub struct FlowMoveFact {
    pub node: crate::node_id::NodeID,
    pub place: String,
    pub ty: String,
}

#[derive(Clone, Debug)]
pub struct FlowCloneFact {
    pub node: crate::node_id::NodeID,
    pub ty: String,
}

#[derive(Clone, Debug)]
pub struct FlowBorrowFact {
    pub node: crate::node_id::NodeID,
    pub borrower: String,
    pub owner: String,
    pub exclusive: bool,
}

#[derive(Clone, Debug)]
pub struct FlowDropFact {
    pub node: crate::node_id::NodeID,
    pub place: String,
    pub ty: String,
    pub kind: drops::DropElaboration,
    pub reason: drops::DropReason,
}

use crate::compiling::driver::Source;
use crate::compiling::module::ModuleId;
use crate::diagnostic::{AnyDiagnostic, Diagnostic, Severity};
use crate::hir::HirFile;
use crate::types::TypeOutput;

/// Check every file's HIR — moves, drops, loans, provenance, captures,
/// raw-pointer gating — writing the results onto the tree in place
/// (`Expr.ownership`, `Block::drops`, `Stmt::drops`, `HirFile::drops`) and
/// returning the editor-facing facts plus diagnostics.
pub fn check_flow(
    hir: &mut IndexMap<Source, HirFile>,
    types: &TypeOutput,
    module_id: ModuleId,
) -> (FlowFacts, Vec<AnyDiagnostic>) {
    let mut checker = moves::MoveChecker::new(types, module_id);
    // Which parameter indices each free function's returned borrow reaches:
    // a single structural pre-pass, consumed at call sites for precise
    // borrowed-return provenance.
    checker.seed_return_reach(hir.values());
    let mut file_drops = vec![];
    for file in hir.values() {
        checker.check_global_storage(&file.roots);
        checker.check_borrow_storage(&file.roots);
        let mut state = Default::default();
        file_drops.push(checker.check_roots(&file.roots, &mut state));
    }
    // Cross-procedural write protection: a global borrowed by another
    // global is immutable everywhere — the borrower would dangle when the
    // assignment drops the old value. (Top-level reassignments are already
    // tracked by the NLL walk; this covers writes from function bodies.)
    let global_writes = std::mem::take(&mut checker.global_writes);
    for (node, global) in global_writes {
        if let Some(borrower) = checker.global_borrows.get(&global).copied() {
            let error = errors::OwnershipError::MutatingBorrowedGlobal {
                name: moves::render_symbol(global, types),
                borrower: moves::render_symbol(borrower, types),
            };
            checker.error(error, node);
        }
    }

    let mut errors = checker.errors;
    errors.extend(unsafe_gate::check(hir, module_id));

    // Silent-clone facts, from both tier-2 sources: the flow checker's
    // borrowed-field extractions and the type checker's borrowed-argument
    // coercions. Rendered as the owned type the clone produces.
    for node in checker.auto_clones.iter().chain(&types.coerce_clones) {
        let Some(ty) = types.node_types.get(node) else {
            continue;
        };
        let ty = match ty {
            crate::types::ty::Ty::Borrow(_, inner) => inner.render_mono(),
            other => other.render_mono(),
        };
        checker.facts.clones.push(FlowCloneFact { node: *node, ty });
    }

    // Bake the analysis onto the tree: this map dies here — downstream
    // stages read the annotations, never a side table.
    let mut annotator = Annotator {
        block_drops: checker.block_drops,
        stmt_drops: checker.stmt_drops,
        consumed: checker.consumed,
        auto_clones: checker.auto_clones,
    };
    for (file, drops) in hir.values_mut().zip(file_drops) {
        file.drops = drops;
        for root in &mut file.roots {
            use derive_visitor::DriveMut;
            root.drive_mut(&mut annotator);
        }
    }

    let diagnostics = errors
        .into_iter()
        .map(|(kind, id)| {
            AnyDiagnostic::Ownership(Diagnostic {
                id,
                severity: Severity::Error,
                kind,
            })
        })
        .collect();
    (checker.facts, diagnostics)
}

#[derive(derive_visitor::VisitorMut)]
#[visitor(crate::hir::Block(enter), crate::hir::Stmt(enter), crate::hir::Expr(enter))]
struct Annotator {
    block_drops: rustc_hash::FxHashMap<crate::node_id::NodeID, Vec<drops::DropSchedule>>,
    stmt_drops: rustc_hash::FxHashMap<crate::node_id::NodeID, Vec<drops::DropSchedule>>,
    consumed: rustc_hash::FxHashSet<crate::node_id::NodeID>,
    auto_clones: rustc_hash::FxHashSet<crate::node_id::NodeID>,
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
        if self.auto_clones.contains(&expr.id) {
            expr.ownership.auto_clone = true;
        }
    }
}
