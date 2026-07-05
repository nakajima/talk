//! Drop scheduling: the annotation types the flow checker writes onto HIR
//! blocks and statements, and the classification rule that decides how each
//! drop lowers. Lowering emits exactly what these schedules say — no
//! re-analysis downstream.

use crate::types::ty::Ty;

use super::place::Place;

/// How a scheduled drop lowers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DropElaboration {
    /// Definitely live here: drop unconditionally.
    Static,
    /// Definitely moved or never initialized: no drop.
    Dead,
    /// Live on some paths only: guard with a runtime drop flag.
    Conditional,
    /// A sub-place was moved out: drop the remaining fields precisely.
    Open,
}

/// Why a drop is scheduled where it is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DropReason {
    /// Normal end of the declaring scope (reverse declaration order).
    ScopeExit,
    /// An assignment overwrites the place; the old value drops first.
    AssignmentReplace,
    /// A `return`/`break`/`continue` leaves the scope early.
    EarlyExit,
    /// The full expression that created a call/construct temp ended: an
    /// unconsumed owned temporary (e.g. a call result that was only
    /// borrowed) releases here.
    TemporaryEnd,
}

/// One drop the lowerer must emit. `node` is the dropped binding's
/// declaration (or the assignment overwriting it) — the editor's anchor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DropSchedule {
    pub place: Place,
    pub ty: Ty,
    pub kind: DropElaboration,
    pub reason: DropReason,
    pub node: crate::node_id::NodeID,
}
