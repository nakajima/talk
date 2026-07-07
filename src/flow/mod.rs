//! The flow checker: the small flow-sensitive companion to the type system's
//! substructural core. Permissions and grades live in types (`src/types`);
//! this pass answers only the flow-sensitive questions — where each value
//! moves, where borrows end, where drops go — as a dataflow analysis over
//! each body's MIR CFG (`cfg`, ADR 0010). Per-point drop elaborations and
//! runtime move sets are recorded on checked MIR; editor-facing move/borrow/drop
//! facts are returned separately. The pass also records provenance (NLL borrow
//! ends at last use), closure captures, CheapClone sites, and raw-pointer
//! gating.

mod captures;
pub(crate) mod cfg;
pub mod drops;
pub mod errors;
pub(crate) mod grades;
mod liveness;
mod loans;
pub(crate) mod mir_annotate;
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
/// input.
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
use crate::typed_ast::TypedFile;
use crate::types::TypeOutput;

/// Check every structural MIR body's CFG — moves, drops, loans, provenance,
/// captures, raw-pointer gating — writing checked ownership facts onto the
/// bodies that lowering consumes, returning editor-facing facts plus
/// diagnostics.
pub(crate) fn check_flow(
    files: &mut IndexMap<Source, TypedFile>,
    bodies: &mut crate::lower::mir::ModuleBodies,
    types: &TypeOutput,
    module_id: ModuleId,
) -> (FlowFacts, Vec<AnyDiagnostic>) {
    let mut checker = moves::MoveChecker::new(types, module_id);
    // Which parameter indices each free function's returned borrow reaches:
    // a single structural pre-pass, consumed at call sites for precise
    // borrowed-return provenance.
    checker.seed_return_reach(files.values());
    for file in files.values() {
        checker.check_global_storage(&file.roots);
        checker.check_borrow_storage(&file.roots);
    }

    // The CFG engine: dataflow over each stored body's blocks — the flow
    // errors, the editor facts, the consume/auto-clone flags, and every
    // per-point candidate elaboration come from it.
    cfg::check_bodies(&mut checker, files, bodies);

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

    let mut errors = std::mem::take(&mut checker.errors);
    errors.extend(unsafe_gate::check(files, module_id));

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

    // Auto-clone flags onto the typed tree too: lowering inlines constant
    // top-level `let` right-hand sides straight from it.
    let results = mir_annotate::FlowResults {
        consumed: &checker.consumed,
        auto_clones: &checker.auto_clones,
    };
    let mut annotator = mir_annotate::Annotator::new(&results);
    for file in files.values_mut() {
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
