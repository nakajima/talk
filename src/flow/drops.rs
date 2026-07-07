//! Drop scheduling: the flow vocabulary for drop sites and the classification
//! rule that decides how each drop lowers. Checked MIR stores these
//! classifications at the drop program points so lowering does not re-analyze
//! ownership.

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
