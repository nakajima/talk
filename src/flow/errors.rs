//! The flow checker's diagnostics: user-facing ownership errors. Message
//! text is stable — the ported legacy corpus pins it verbatim.

use std::error::Error;
use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OwnershipError {
    BorrowedGlobal {
        name: String,
        ty: String,
    },
    /// A `&T` in a struct field or enum payload.
    BorrowInStorage {
        owner: String,
        field: String,
        ty: String,
    },
    ReturningLocalBorrow {
        ty: String,
    },
    UnknownBorrowProvenance {
        ty: String,
    },
    UseAfterMove {
        name: String,
        ty: String,
    },
    /// A linear value would be silently dropped (flow checker only; linearity
    /// is a grade, which the legacy checker does not know).
    LinearNotConsumed {
        name: String,
        ty: String,
    },
    UseAfterInvalidatedBorrow {
        name: String,
        owner: String,
        ty: String,
    },
    MoveOutOfBorrowedValue {
        name: String,
        owner: String,
        ty: String,
    },
    AssignThroughSharedBorrow {
        name: String,
        ty: String,
    },
    OverlappingBorrow {
        owner: String,
        existing: String,
        existing_kind: String,
        requested_kind: String,
    },
    MoveWhileBorrowed {
        name: String,
        borrower: String,
    },
    UnsupportedClosureCapture {
        name: String,
        ty: String,
    },
    ImplicitClosureCapture {
        name: String,
        ty: String,
    },
    InvalidClosureCaptureMode {
        name: String,
        mode: String,
        ty: String,
        reason: String,
    },
    EscapingClosureCapture {
        name: String,
        ty: String,
        reason: String,
    },
    UnsafeRawPointerUsage {
        ty: String,
    },
    /// A `'heap` reference captured by a closure that escapes the frame —
    /// closure environments are invisible to the region ledger.
    EscapingObjectCapture {
        name: String,
        ty: String,
    },
    /// A `'heap` value packed behind `any P` — existential payloads are
    /// invisible to the region ledger.
    ObjectInExistential {
        ty: String,
    },
    /// A `'heap` type argument to a raw-storage container — raw memory is
    /// invisible to the region ledger.
    ObjectInRawStorage {
        container: String,
        ty: String,
    },
}

impl Error for OwnershipError {}

impl Display for OwnershipError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OwnershipError::BorrowInStorage { owner, field, ty } => {
                write!(
                    f,
                    "Borrow type {ty} cannot be stored in '{owner}.{field}'; borrows end with their owner's scope"
                )
            }
            OwnershipError::BorrowedGlobal { name, ty } => {
                write!(f, "Borrowed type {ty} cannot be stored in global '{name}'")
            }
            OwnershipError::ReturningLocalBorrow { ty } => {
                write!(
                    f,
                    "Cannot return borrowed value {ty}; it borrows from a value owned by this function"
                )
            }
            OwnershipError::UnknownBorrowProvenance { ty } => {
                write!(
                    f,
                    "Cannot use borrowed value {ty}; its borrow provenance is unknown"
                )
            }
            OwnershipError::UseAfterMove { name, ty } => {
                write!(f, "Use of moved value '{name}' of type {ty}")
            }
            OwnershipError::LinearNotConsumed { name, ty } => {
                write!(
                    f,
                    "'{name}' of type {ty} is linear and must be consumed exactly once; it would be dropped here"
                )
            }
            OwnershipError::UseAfterInvalidatedBorrow { name, owner, ty } => {
                write!(
                    f,
                    "Use of borrowed value '{name}' of type {ty} after owner '{owner}' moved or was reassigned"
                )
            }
            OwnershipError::MoveOutOfBorrowedValue { name, owner, ty } => {
                write!(
                    f,
                    "Cannot move owned value '{name}' of type {ty} out of borrowed value '{owner}'"
                )
            }
            OwnershipError::AssignThroughSharedBorrow { name, ty } => {
                write!(
                    f,
                    "Cannot assign through shared borrow '{name}' of type {ty}"
                )
            }
            OwnershipError::OverlappingBorrow {
                owner,
                existing,
                existing_kind,
                requested_kind,
            } => write!(
                f,
                "Cannot take {requested_kind} borrow of '{owner}' while it is already {existing_kind} borrowed as '{existing}'"
            ),
            OwnershipError::MoveWhileBorrowed { name, borrower } => {
                write!(
                    f,
                    "Cannot move '{name}' while it is borrowed as '{borrower}'"
                )
            }
            OwnershipError::UnsupportedClosureCapture { name, ty } => {
                write!(
                    f,
                    "Cannot capture ownership-sensitive value '{name}' of type {ty} in a closure until capture ownership modes are explicit"
                )
            }
            OwnershipError::ImplicitClosureCapture { name, ty } => {
                write!(
                    f,
                    "Cannot implicitly capture '{name}' of type {ty}; add it to the closure capture list"
                )
            }
            OwnershipError::InvalidClosureCaptureMode {
                name,
                mode,
                ty,
                reason,
            } => {
                write!(
                    f,
                    "Cannot capture '{name}' of type {ty} with {mode}; {reason}"
                )
            }
            OwnershipError::EscapingClosureCapture { name, ty, reason } => {
                write!(
                    f,
                    "Cannot let closure capture '{name}' of type {ty} escape; {reason}"
                )
            }
            OwnershipError::UnsafeRawPointerUsage { ty } => {
                write!(
                    f,
                    "Raw pointer type {ty} is only available in core or sources marked '// unsafe'"
                )
            }
            OwnershipError::EscapingObjectCapture { name, ty } => {
                write!(
                    f,
                    "Cannot let closure capture heap value '{name}' of type {ty} escape; heap references cannot outlive the frame through a closure yet"
                )
            }
            OwnershipError::ObjectInExistential { ty } => {
                write!(
                    f,
                    "Heap type {ty} cannot be packed into an existential yet"
                )
            }
            OwnershipError::ObjectInRawStorage { container, ty } => {
                write!(
                    f,
                    "Heap type {ty} cannot be stored in {container}: raw storage bypasses region tracking"
                )
            }
        }
    }
}
