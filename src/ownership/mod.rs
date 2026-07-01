use std::{collections::VecDeque, error::Error, fmt::Display};

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    compiling::{driver::Source, module::ModuleId},
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    hir::{self, Block, Body, Decl, DeclKind, Expr, ExprKind, HirFile, Node, Parameter, StmtKind},
    mir,
    name_resolution::{
        name_resolver::ResolvedNames,
        symbol::{Symbol, set_symbol_names},
    },
    node_id::{FileID, NodeID},
    node_kinds::{
        func::{CaptureMode, CaptureSpec},
        type_annotation::TypeAnnotationKind,
    },
    types::{
        TypeOutput,
        output::stored_field_symbol,
        ty::{BorrowKind, Row, Ty},
    },
};

#[derive(Clone, Debug, Default)]
pub struct OwnershipOutput {
    pub borrowed_types: FxHashSet<Symbol>,
    pub owned_types: FxHashSet<Symbol>,
    pub copyable_types: FxHashSet<Symbol>,
    /// Compatibility summary for nominal heads; new code should prefer
    /// `needs_drop_types` plus structural checks with the current type catalog.
    pub droppable_types: FxHashSet<Symbol>,
    pub needs_drop_types: FxHashSet<Ty>,
    pub facts: OwnershipFacts,
    pub drop_plan: DropPlan,
    /// Every body the ownership pass built, borrow-checked, and elaborated, keyed so a later
    /// phase can reuse it instead of rebuilding the MIR. Lowering looks its bodies up here and
    /// reads the drop/move results already projected onto each statement — so the MIR is built
    /// and the drops elaborated exactly once, in this pass, for both the compiler and the editor.
    pub(crate) mir_bodies: FxHashMap<BodyCacheKey, crate::mir::Body>,
}

impl OwnershipOutput {
    /// The already-built, already-elaborated MIR for a function body, if this pass produced it.
    /// Lowering reuses this so the MIR is built and its drops elaborated exactly once. (The
    /// top-level body is not reused: lowering builds one combined cross-file `main` body, whereas
    /// this pass builds a body per file, so the granularities don't line up.)
    pub(crate) fn function_body(
        &self,
        body: NodeID,
        owner: Option<Symbol>,
    ) -> Option<&crate::mir::Body> {
        self.mir_bodies.get(&BodyCacheKey::Function { body, owner })
    }

    pub fn type_is_borrowed_nominal(&self, symbol: Symbol) -> bool {
        self.borrowed_types.contains(&symbol)
    }

    pub fn type_has_needs_drop_fact(&self, ty: &Ty) -> bool {
        self.needs_drop_types.contains(ty)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BodyId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OwnershipPoint {
    pub body: BodyId,
    pub point: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OriginId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LoanId(pub u32);

#[derive(Clone, Debug, Default)]
pub struct OwnershipFacts {
    pub bodies: Vec<OwnershipBody>,
    pub points: Vec<PointFact>,
    pub cfg_edges: Vec<(OwnershipPoint, OwnershipPoint)>,
    pub scopes: Vec<ScopeFact>,
    pub storage_live: Vec<StorageFact>,
    pub storage_dead: Vec<StorageFact>,
    pub moves: Vec<MoveFact>,
    pub origins: Vec<OriginFact>,
    pub borrows: Vec<LoanFact>,
    pub invalidations: Vec<InvalidationFact>,
    pub assignments: Vec<AssignmentFact>,
    pub candidate_drops: Vec<CandidateDropFact>,
}

#[derive(Clone, Debug)]
pub struct OwnershipBody {
    pub id: BodyId,
    pub kind: BodyKind,
    pub owner: Option<Symbol>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodyKind {
    TopLevel,
    Function,
    DeclBody,
    Nested,
}

#[derive(Clone, Debug)]
pub struct PointFact {
    pub point: OwnershipPoint,
    pub kind: PointKind,
    pub node: Option<NodeID>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PointKind {
    ScopeEnter,
    ScopeExit,
    StorageLive,
    StorageDead,
    Read,
    ConsumeValue,
    AssignmentRootUse,
    Bind,
    Assign,
    DropCandidate,
    Call,
    Perform,
    ReturnValue,
    ContinueValue,
    Function,
    Handling,
    DeclBody,
}

#[derive(Clone, Debug)]
pub struct ScopeFact {
    pub body: BodyId,
    pub scope: u32,
    pub parent: Option<u32>,
}

#[derive(Clone, Debug)]
pub struct StorageFact {
    pub point: OwnershipPoint,
    pub node: Option<NodeID>,
    pub key_path: KeyPath,
    pub ty: Option<Ty>,
}

#[derive(Clone, Debug)]
pub struct MoveFact {
    pub point: OwnershipPoint,
    pub node: Option<NodeID>,
    pub source: KeyPath,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub struct OriginFact {
    pub id: OriginId,
    pub point: OwnershipPoint,
    pub node: Option<NodeID>,
    pub borrower: KeyPath,
    pub ty: Option<Ty>,
}

#[derive(Clone, Debug)]
pub struct LoanFact {
    pub id: LoanId,
    pub origin: OriginId,
    pub point: OwnershipPoint,
    pub node: Option<NodeID>,
    pub borrower: KeyPath,
    pub owner: Option<KeyPath>,
    pub kind: BorrowKind,
}

#[derive(Clone, Debug)]
pub struct InvalidationFact {
    pub point: Option<OwnershipPoint>,
    pub node: Option<NodeID>,
    pub loan: Option<LoanId>,
    pub owner: KeyPath,
}

#[derive(Clone, Debug)]
pub struct AssignmentFact {
    pub point: OwnershipPoint,
    pub node: Option<NodeID>,
    pub target: KeyPath,
    pub ty: Option<Ty>,
}

#[derive(Clone, Debug)]
pub struct CandidateDropFact {
    pub point: OwnershipPoint,
    pub node: Option<NodeID>,
    pub target: KeyPath,
    pub ty: Option<Ty>,
    pub reason: mir::DropReason,
}

#[derive(Clone, Debug, Default)]
pub struct DropPlan {
    pub obligations: Vec<DropObligation>,
}

#[derive(Clone, Debug)]
pub struct DropObligation {
    pub point: OwnershipPoint,
    pub node: Option<NodeID>,
    pub key_path: KeyPath,
    pub ty: Ty,
    pub kind: mir::DropElaboration,
    pub reason: mir::DropReason,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OwnershipError {
    BorrowedField {
        owner: String,
        field: String,
        ty: String,
    },
    BorrowedEnumPayload {
        owner: String,
        variant: String,
        ty: String,
    },
    BorrowedGlobal {
        name: String,
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
}

impl Error for OwnershipError {}

impl Display for OwnershipError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OwnershipError::BorrowedField { owner, field, ty } => {
                write!(
                    f,
                    "Borrowed type {ty} cannot be stored in owned struct {owner}.{field}"
                )
            }
            OwnershipError::BorrowedEnumPayload { owner, variant, ty } => {
                write!(
                    f,
                    "Borrowed type {ty} cannot be stored in owned enum {owner}.{variant}"
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
        }
    }
}

/// Borrow-check a program and build its MIR once. Returns diagnostics plus the
/// `OwnershipOutput`: borrow/assignment/drop-candidate facts, the elaborated drop/move facts
/// (`drop_plan` + `facts.moves`) the editor renders, and every elaborated MIR body keyed for
/// lowering to reuse. The MIR is built and the drops elaborated exactly once here, for both the
/// compiler (which lowers the persisted bodies) and the editor (which reads the facts).
pub fn check_ownership(
    asts: &IndexMap<Source, HirFile>,
    types: &TypeOutput,
    resolved: &ResolvedNames,
    module_id: ModuleId,
) -> (OwnershipOutput, Vec<AnyDiagnostic>) {
    let checker = run_ownership(asts, types, resolved, module_id);
    (checker.output, checker.diagnostics)
}

fn run_ownership<'a>(
    asts: &IndexMap<Source, HirFile>,
    types: &'a TypeOutput,
    resolved: &'a ResolvedNames,
    module_id: ModuleId,
) -> OwnershipChecker<'a> {
    let _names = set_symbol_names(types.display_names.clone());
    let mut checker = OwnershipChecker {
        types,
        resolved,
        module_id,
        diagnostics: vec![],
        reported: FxHashSet::default(),
        output: OwnershipOutput::default(),
        recorded_mir_bodies: FxHashMap::default(),
        elaborated_mir_bodies: FxHashSet::default(),
        checked_independent_bodies: FxHashSet::default(),
        recorded_move_facts: FxHashSet::default(),
        recorded_borrow_facts: FxHashMap::default(),
        nested_body_memos: vec![],
    };
    checker.discover_borrowed_types();
    checker.discover_owned_types();
    checker.discover_copy_drop_abilities();
    checker.check_top_level_globals(asts);
    checker.check_raw_pointer_surface(asts);
    checker.check_moves(asts);
    checker
}

/// Annotate `body`'s statements with the drop/move results lowering needs, reusing the
/// type-ability summary `check_ownership` already produced. Lowering calls this on the MIR
/// body it builds, then reads the results back off each statement's `ownership` — so it never
/// looks them up in a side table keyed by program point. The drop elaboration runs on this
/// exact body (a transient checker), then the per-point obligations/moves are projected onto
/// the statements they belong to.
pub(crate) fn elaborate_body_drops(
    types: &TypeOutput,
    resolved: &ResolvedNames,
    summary: &OwnershipOutput,
    body: &mut mir::Body,
) {
    let _names = set_symbol_names(types.display_names.clone());
    let mut checker = OwnershipChecker {
        types,
        resolved,
        // Unused by drop elaboration (only `check_raw_pointer_surface` reads it).
        module_id: ModuleId::Core,
        diagnostics: vec![],
        reported: FxHashSet::default(),
        output: OwnershipOutput {
            borrowed_types: summary.borrowed_types.clone(),
            owned_types: summary.owned_types.clone(),
            copyable_types: summary.copyable_types.clone(),
            droppable_types: summary.droppable_types.clone(),
            needs_drop_types: summary.needs_drop_types.clone(),
            ..OwnershipOutput::default()
        },
        recorded_mir_bodies: FxHashMap::default(),
        elaborated_mir_bodies: FxHashSet::default(),
        checked_independent_bodies: FxHashSet::default(),
        recorded_move_facts: FxHashSet::default(),
        recorded_borrow_facts: FxHashMap::default(),
        nested_body_memos: vec![],
    };
    // A fresh checker has one body, so every obligation/move is keyed to `BodyId(0)` and
    // matched onto its statement purely by point index.
    let body_id = BodyId(0);
    checker.elaborate_drops(body_id, body);
    let obligations = checker.output.drop_plan.obligations;
    let moves = checker.output.facts.moves;
    for statement in body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.statements)
    {
        let point = statement.point.0 as u32;
        if let Some(obligation) = obligations
            .iter()
            .find(|obligation| obligation.point.point == point)
        {
            statement.ownership.drop = Some(mir::DropElaborationResult {
                key_path: obligation.key_path.clone(),
                kind: obligation.kind,
            });
        }
        statement.ownership.moves = moves
            .iter()
            .filter(|fact| fact.point.point == point)
            .map(|fact| fact.source.clone())
            .collect();
    }
}

struct OwnershipChecker<'a> {
    types: &'a TypeOutput,
    resolved: &'a ResolvedNames,
    module_id: ModuleId,
    diagnostics: Vec<AnyDiagnostic>,
    reported: FxHashSet<(NodeID, OwnershipError)>,
    output: OwnershipOutput,
    recorded_mir_bodies: FxHashMap<BodyCacheKey, BodyId>,
    elaborated_mir_bodies: FxHashSet<BodyCacheKey>,
    checked_independent_bodies: FxHashSet<BodyCacheKey>,
    recorded_move_facts: FxHashSet<MoveFactKey>,
    recorded_borrow_facts: FxHashMap<BorrowFactKey, LoanId>,
    nested_body_memos: Vec<NestedBodyMemo>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum BodyCacheKey {
    TopLevel(FileID),
    Decl(NodeID),
    Function { body: NodeID, owner: Option<Symbol> },
    Nested(NodeID),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct MoveFactKey {
    point: OwnershipPoint,
    node: Option<NodeID>,
    source: KeyPath,
    ty: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct BorrowFactKey {
    point: OwnershipPoint,
    node: Option<NodeID>,
    borrower: KeyPath,
    owner: Option<KeyPath>,
    kind: BorrowKind,
}

#[derive(Clone, Debug)]
struct NestedBodyMemo {
    key: BodyCacheKey,
    live_at_exit: FxHashSet<Symbol>,
    input: MoveState,
    output: MoveState,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BorrowOrigin {
    BorrowedParam,
    OwnedParam,
    Local,
    Static,
    Unknown,
}

impl BorrowOrigin {
    fn can_have_owner(self) -> bool {
        matches!(
            self,
            BorrowOrigin::BorrowedParam | BorrowOrigin::OwnedParam | BorrowOrigin::Local
        )
    }

    fn is_function_owned(self) -> bool {
        matches!(self, BorrowOrigin::OwnedParam | BorrowOrigin::Local)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct KeyPath {
    pub root: Symbol,
    pub fields: Vec<Symbol>,
}

impl KeyPath {
    pub fn root(root: Symbol) -> Self {
        Self {
            root,
            fields: vec![],
        }
    }

    pub fn child(&self, field: Symbol) -> Self {
        let mut fields = self.fields.clone();
        fields.push(field);
        Self {
            root: self.root,
            fields,
        }
    }

    pub fn contains(&self, other: &Self) -> bool {
        self.root == other.root
            && self.fields.len() <= other.fields.len()
            && self
                .fields
                .iter()
                .zip(&other.fields)
                .all(|(left, right)| left == right)
    }

    pub fn overlaps(&self, other: &Self) -> bool {
        self.contains(other) || other.contains(self)
    }

    fn is_tracked_storage_root(&self) -> bool {
        matches!(
            self.root,
            Symbol::DeclaredLocal(_)
                | Symbol::PatternBindLocal(_)
                | Symbol::ParamLocal(_)
                | Symbol::Global(_)
        )
    }
}

type BorrowEnv = BorrowInfoEnv;
type MoveEnv = FxHashMap<KeyPath, (NodeID, Ty)>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MarkerAbility {
    Borrowed,
    Owner,
}

impl MarkerAbility {
    fn protocol(self) -> Symbol {
        match self {
            MarkerAbility::Borrowed => Symbol::Borrowed,
            MarkerAbility::Owner => Symbol::Owner,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct DropState {
    initialized_all: FxHashSet<KeyPath>,
    initialized_any: FxHashSet<KeyPath>,
    moved_all: FxHashMap<KeyPath, NodeID>,
    moved_any: FxHashMap<KeyPath, NodeID>,
    root_tys: FxHashMap<Symbol, Ty>,
}

impl DropState {
    fn merge_from(&mut self, other: &Self) -> bool {
        let before = self.clone();
        self.initialized_all
            .retain(|key_path| other.initialized_all.contains(key_path));
        self.initialized_any
            .extend(other.initialized_any.iter().cloned());
        self.moved_all
            .retain(|key_path, _| other.moved_all.contains_key(key_path));
        self.moved_any.extend(other.moved_any.clone());
        self.root_tys.extend(other.root_tys.clone());
        before != *self
    }

    fn note_move(&mut self, key_path: KeyPath, id: NodeID) {
        self.moved_all.insert(key_path.clone(), id);
        self.moved_any.insert(key_path, id);
    }

    fn initialize_key_path(&mut self, key_path: KeyPath) {
        self.initialized_all.insert(key_path.clone());
        self.initialized_any.insert(key_path.clone());
        self.moved_all
            .retain(|moved_path, _| !key_path.contains(moved_path));
        self.moved_any
            .retain(|moved_path, _| !key_path.contains(moved_path));
    }

    fn mark_uninitialized(&mut self, key_path: KeyPath, id: NodeID) {
        self.initialized_all.remove(&key_path);
        self.initialized_any.remove(&key_path);
        self.note_move(key_path, id);
    }

    fn finish_storage(&mut self, key_path: &KeyPath) {
        self.initialized_all.remove(key_path);
        self.initialized_any.remove(key_path);
        self.root_tys.remove(&key_path.root);
        self.moved_all
            .retain(|moved_path, _| !key_path.contains(moved_path));
        self.moved_any
            .retain(|moved_path, _| !key_path.contains(moved_path));
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BorrowInfo {
    origin: BorrowOrigin,
    owner: Option<KeyPath>,
    kind: BorrowKind,
}

impl BorrowInfo {
    fn new(origin: BorrowOrigin, owner: Option<KeyPath>) -> Self {
        Self {
            origin,
            owner,
            kind: BorrowKind::Shared,
        }
    }

    fn with_kind(origin: BorrowOrigin, owner: Option<KeyPath>, kind: BorrowKind) -> Self {
        Self {
            origin,
            owner,
            kind,
        }
    }
}

/// One loan carried by a borrowed value. Aggregates such as `Optional<&T>`
/// and records can carry more than one loan, so provenance is tracked as a
/// set instead of being collapsed into one owner.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ProvenanceLoan {
    origin: BorrowOrigin,
    owner: Option<KeyPath>,
    kind: BorrowKind,
}

impl ProvenanceLoan {
    fn from_info(info: &BorrowInfo) -> Self {
        Self {
            origin: info.origin,
            owner: info.owner.clone(),
            kind: info.kind,
        }
    }

    fn unknown(kind: BorrowKind) -> Self {
        Self {
            origin: BorrowOrigin::Unknown,
            owner: None,
            kind,
        }
    }
}

/// Provenance attached to a value whose type contains borrows. This mirrors
/// the origin-to-loan relation used by region/loan based checkers: origins are
/// facts, and each origin may contain one or more loans with independent owners.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct BorrowProvenance {
    loans: Vec<ProvenanceLoan>,
}

impl BorrowProvenance {
    fn direct(info: BorrowInfo) -> Self {
        Self {
            loans: vec![ProvenanceLoan::from_info(&info)],
        }
    }

    fn unknown(kind: BorrowKind) -> Self {
        Self {
            loans: vec![ProvenanceLoan::unknown(kind)],
        }
    }

    fn is_empty(&self) -> bool {
        self.loans.is_empty()
    }

    fn push(&mut self, loan: ProvenanceLoan) {
        if !self.loans.contains(&loan) {
            self.loans.push(loan);
        }
    }

    fn extend(&mut self, other: BorrowProvenance) {
        for loan in other.loans {
            self.push(loan);
        }
    }

    fn with_kind(mut self, kind: BorrowKind) -> Self {
        for loan in &mut self.loans {
            loan.kind = kind;
        }
        self
    }

    fn first_info(&self) -> Option<BorrowInfo> {
        self.loans.first().map(|loan| BorrowInfo {
            origin: loan.origin,
            owner: loan.owner.clone(),
            kind: loan.kind,
        })
    }

    fn has_unknown(&self) -> bool {
        self.loans
            .iter()
            .any(|loan| loan.origin == BorrowOrigin::Unknown)
    }

    fn has_function_owned(&self) -> bool {
        self.loans
            .iter()
            .any(|loan| loan.origin.is_function_owned())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct MoveState {
    moved: MoveEnv,
    borrows: BorrowInfoEnv,
    provenances: FxHashMap<KeyPath, BorrowProvenance>,
    invalid_borrows: FxHashMap<KeyPath, KeyPath>,
    borrowed_roots: FxHashMap<Symbol, String>,
    shared_borrow_roots: FxHashMap<Symbol, String>,
    active_loans: Vec<ActiveLoan>,
    closure_captures: FxHashMap<KeyPath, ClosureCaptureSummary>,
}

type BorrowInfoEnv = FxHashMap<KeyPath, BorrowInfo>;

#[derive(Clone, Debug, Default)]
struct BorrowLiveness {
    live_out_by_point: FxHashMap<usize, FxHashSet<Symbol>>,
}

#[derive(Clone, Copy)]
struct StatementContext<'a> {
    point: OwnershipPoint,
    live_after: &'a FxHashSet<Symbol>,
    return_ty: Option<&'a Ty>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ActiveLoan {
    borrower: KeyPath,
    owner: KeyPath,
    kind: BorrowKind,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ClosureCaptureSummary {
    captures: Vec<ClosureCapture>,
}

impl ClosureCaptureSummary {
    fn is_empty(&self) -> bool {
        self.captures.is_empty()
    }

    fn extend(&mut self, other: ClosureCaptureSummary) {
        for capture in other.captures {
            if !self.captures.contains(&capture) {
                self.captures.push(capture);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ClosureCapture {
    id: NodeID,
    symbol: Symbol,
    ty: Ty,
    borrowed_in_parent: bool,
    mode: Option<CaptureMode>,
}

impl MoveState {
    fn invalidate_borrows_of(&mut self, owner: &KeyPath) {
        for (borrow, info) in &self.borrows {
            if info
                .owner
                .as_ref()
                .is_some_and(|borrowed_owner| borrowed_owner.overlaps(owner))
            {
                self.invalid_borrows.insert(borrow.clone(), owner.clone());
            }
        }
        for (borrow, provenance) in &self.provenances {
            if provenance.loans.iter().any(|loan| {
                loan.owner
                    .as_ref()
                    .is_some_and(|borrowed_owner| borrowed_owner.overlaps(owner))
            }) {
                self.invalid_borrows.insert(borrow.clone(), owner.clone());
            }
        }
    }

    fn restore_key_path(&mut self, key_path: &KeyPath) {
        self.moved.retain(|moved, _| !key_path.contains(moved));
        self.borrows.retain(|borrow, _| !key_path.contains(borrow));
        self.provenances
            .retain(|borrow, _| !key_path.contains(borrow));
        self.invalid_borrows
            .retain(|borrow, _| !key_path.contains(borrow));
        if key_path.fields.is_empty() {
            self.borrowed_roots.remove(&key_path.root);
            self.shared_borrow_roots.remove(&key_path.root);
        }
        self.active_loans
            .retain(|loan| !key_path.contains(&loan.borrower));
        self.closure_captures
            .retain(|path, _| !key_path.contains(path));
    }

    fn initialize_key_path(&mut self, key_path: &KeyPath) {
        self.moved.retain(|moved, _| !key_path.contains(moved));
        self.provenances
            .retain(|borrow, _| !key_path.contains(borrow));
        self.invalid_borrows
            .retain(|borrow, _| !key_path.contains(borrow));
        if key_path.fields.is_empty() {
            self.borrowed_roots.remove(&key_path.root);
            self.shared_borrow_roots.remove(&key_path.root);
        }
        self.closure_captures
            .retain(|path, _| !key_path.contains(path));
    }

    fn add_loan(&mut self, borrower: KeyPath, owner: KeyPath, kind: BorrowKind) {
        let loan = ActiveLoan {
            borrower,
            owner,
            kind,
        };
        if !self.active_loans.contains(&loan) {
            self.active_loans.push(loan);
        }
    }

    fn finish_storage(&mut self, key_path: &KeyPath) {
        self.invalidate_borrows_of(key_path);
        self.restore_key_path(key_path);
        self.active_loans
            .retain(|loan| !loan.owner.overlaps(key_path));
    }

    fn merge_from(&mut self, other: &MoveState) -> bool {
        let before = self.clone();
        self.moved.extend(other.moved.clone());
        self.borrows.extend(other.borrows.clone());
        self.provenances.extend(other.provenances.clone());
        self.invalid_borrows.extend(other.invalid_borrows.clone());
        self.borrowed_roots.extend(other.borrowed_roots.clone());
        self.shared_borrow_roots
            .extend(other.shared_borrow_roots.clone());
        for loan in &other.active_loans {
            if !self.active_loans.contains(loan) {
                self.active_loans.push(loan.clone());
            }
        }
        for (path, summary) in &other.closure_captures {
            self.closure_captures
                .entry(path.clone())
                .or_default()
                .extend(summary.clone());
        }
        *self != before
    }

    fn prune_dead_loans(&mut self, live_roots: &FxHashSet<Symbol>) {
        self.active_loans
            .retain(|loan| live_roots.contains(&loan.borrower.root));
        self.borrows
            .retain(|borrow, _| live_roots.contains(&borrow.root));
        self.provenances
            .retain(|borrow, _| live_roots.contains(&borrow.root));
        self.invalid_borrows
            .retain(|borrow, _| live_roots.contains(&borrow.root));
        self.borrowed_roots
            .retain(|borrow, _| live_roots.contains(borrow));
        self.shared_borrow_roots
            .retain(|borrow, _| live_roots.contains(borrow));
    }
}

impl OwnershipChecker<'_> {
    fn discover_borrowed_types(&mut self) {
        for symbol in self
            .types
            .catalog
            .structs
            .keys()
            .chain(self.types.catalog.enums.keys())
            .copied()
        {
            if self.symbol_has_ability(symbol, MarkerAbility::Borrowed) {
                self.output.borrowed_types.insert(symbol);
            }
        }
    }

    fn discover_owned_types(&mut self) {
        let symbols: Vec<Symbol> = self
            .types
            .catalog
            .structs
            .keys()
            .chain(self.types.catalog.enums.keys())
            .copied()
            .collect();
        for symbol in symbols {
            if self.is_borrowed_symbol(symbol) {
                continue;
            }
            if self.symbol_has_ability(symbol, MarkerAbility::Owner)
                || self.nominal_contains_owned(symbol, &[], &mut FxHashSet::default())
            {
                self.output.owned_types.insert(symbol);
            }
        }
    }

    fn discover_copy_drop_abilities(&mut self) {
        for symbol in self
            .types
            .catalog
            .structs
            .keys()
            .chain(self.types.catalog.enums.keys())
            .copied()
        {
            let ty = Ty::Nominal(symbol, nominal_params(self.types, symbol));
            if self.needs_drop_type(&ty) {
                self.output.droppable_types.insert(symbol);
                self.output.needs_drop_types.insert(ty.clone());
            }
            if self.is_copy_type(&ty) {
                self.output.copyable_types.insert(symbol);
            }
        }
    }

    fn check_top_level_globals(&mut self, asts: &IndexMap<Source, HirFile>) {
        for ast in asts.values() {
            for node in &ast.roots {
                let Node::Decl(decl) = node else { continue };
                let DeclKind::Let { lhs, .. } = &decl.kind else {
                    continue;
                };
                for (node_id, symbol) in lhs.collect_binders() {
                    let Some(scheme) = self.types.schemes.get(&symbol) else {
                        continue;
                    };
                    if !matches!(scheme.ty, Ty::Func(..)) && self.contains_borrowed_type(&scheme.ty)
                    {
                        self.error(
                            node_id,
                            OwnershipError::BorrowedGlobal {
                                name: self.render_symbol(symbol),
                                ty: scheme.ty.render_mono(),
                            },
                        );
                    }
                }
            }
        }
    }

    fn check_raw_pointer_surface(&mut self, asts: &IndexMap<Source, HirFile>) {
        if self.module_id == ModuleId::Core {
            return;
        }

        let safe_files: FxHashSet<_> = asts
            .iter()
            .filter_map(|(source, ast)| (!source_allows_unsafe(source)).then_some(ast.file_id))
            .collect();
        if safe_files.is_empty() {
            return;
        }

        let mut inline_ir = FxHashSet::default();
        for ast in asts
            .values()
            .filter(|ast| safe_files.contains(&ast.file_id))
        {
            collect_inline_ir_exprs(&ast.roots, &mut inline_ir);
        }
        for id in inline_ir {
            self.error(
                id,
                OwnershipError::UnsafeRawPointerUsage {
                    ty: "inline IR".to_string(),
                },
            );
        }

        let mut typed_exprs = vec![];
        for ast in asts
            .values()
            .filter(|ast| safe_files.contains(&ast.file_id))
        {
            walk_nodes(
                &ast.roots,
                &mut TypedExprCollector {
                    out: &mut typed_exprs,
                },
            );
        }
        let raw_nodes: Vec<_> = typed_exprs
            .into_iter()
            .filter(|(_, ty)| self.type_mentions_raw_ptr(ty))
            .map(|(id, ty)| (id, ty.render_mono()))
            .collect();
        for (id, ty) in raw_nodes {
            self.error(id, OwnershipError::UnsafeRawPointerUsage { ty });
        }
    }

    fn check_moves(&mut self, asts: &IndexMap<Source, HirFile>) {
        for ast in asts.values() {
            self.check_decl_moves_in_slice(ast.file_id, &ast.roots);
        }
    }

    fn check_decl_moves_in_slice(&mut self, file_id: FileID, nodes: &[Node]) {
        let mut body = mir::build_nodes(self.types, nodes);
        let key = BodyCacheKey::TopLevel(file_id);
        let body_id = self.record_mir_body_once(key, &body, BodyKind::TopLevel);
        self.elaborate_and_project(key, body_id, &mut body);
        let mut state = MoveState::default();
        self.check_mir_body(body_id, &body, &mut state);
        self.persist_body(key, body);
    }

    fn check_body_moves(&mut self, body: &Body) {
        for decl in &body.decls {
            let mut body = mir::build_decls(self.types, std::slice::from_ref(decl));
            let key = BodyCacheKey::Decl(decl.id);
            let body_id = self.record_mir_body_once(key, &body, BodyKind::DeclBody);
            self.elaborate_and_project(key, body_id, &mut body);
            if !self.checked_independent_bodies.insert(key) {
                self.persist_body(key, body);
                continue;
            }
            let mut state = MoveState::default();
            self.check_mir_body(body_id, &body, &mut state);
            self.persist_body(key, body);
        }
    }

    fn check_func_moves(
        &mut self,
        owner: Option<Symbol>,
        captures: &[CaptureSpec],
        params: &[Parameter],
        source_body: &Block,
        parent_state: Option<&MoveState>,
    ) {
        let mut body = mir::build_function(self.types, owner, source_body);
        let key = BodyCacheKey::Function {
            body: source_body.id,
            owner,
        };
        let body_id = self.record_mir_body_once(key, &body, BodyKind::Function);
        self.elaborate_and_project(key, body_id, &mut body);
        if parent_state.is_some() {
            self.check_closure_captures(captures, params, source_body, &body, parent_state);
        }
        if !self.checked_independent_bodies.insert(key) {
            self.persist_body(key, body);
            return;
        }
        let mut state = MoveState::default();
        self.seed_shared_borrow_params(owner, params, &mut state);
        self.check_mir_body(body_id, &body, &mut state);
        self.persist_body(key, body);
    }

    fn check_closure_captures(
        &mut self,
        capture_specs: &[CaptureSpec],
        params: &[Parameter],
        source_body: &Block,
        body: &mir::Body,
        parent_state: Option<&MoveState>,
    ) {
        let summary =
            self.closure_capture_summary(capture_specs, params, source_body, body, parent_state);
        self.check_capture_modes(&summary, !capture_specs.is_empty());
        for capture in &summary.captures {
            if capture.mode.is_none() && self.capture_is_ownership_sensitive(&capture.ty) {
                self.error(
                    capture.id,
                    OwnershipError::UnsupportedClosureCapture {
                        name: self.render_symbol(capture.symbol),
                        ty: capture.ty.render_mono(),
                    },
                );
            }
        }
    }

    fn closure_capture_summary(
        &self,
        capture_specs: &[CaptureSpec],
        params: &[Parameter],
        source_body: &Block,
        body: &mir::Body,
        parent_state: Option<&MoveState>,
    ) -> ClosureCaptureSummary {
        let explicit_modes: FxHashMap<Symbol, CaptureMode> = capture_specs
            .iter()
            .filter_map(|capture| {
                capture
                    .name
                    .symbol()
                    .ok()
                    .map(|symbol| (symbol, capture.mode))
            })
            .collect();
        let mut local_symbols: FxHashSet<Symbol> = params
            .iter()
            .filter_map(|param| param.name.symbol().ok())
            .collect();
        collect_block_binders(source_body, &mut local_symbols);
        for block in &body.blocks {
            for statement in &block.statements {
                if let mir::Statement::StorageLive { symbol, .. } = &statement.kind {
                    local_symbols.insert(*symbol);
                }
            }
        }

        let mut captures = ClosureCaptureSummary::default();
        for (symbol, (id, ty)) in self.capture_uses(body) {
            if local_symbols.contains(&symbol) || !is_local_or_param(symbol) {
                continue;
            }
            captures.captures.push(ClosureCapture {
                id,
                symbol,
                ty,
                borrowed_in_parent: parent_state
                    .is_some_and(|state| state.borrows.contains_key(&KeyPath::root(symbol))),
                mode: explicit_modes.get(&symbol).copied(),
            });
        }
        for capture in capture_specs {
            let Ok(symbol) = capture.name.symbol() else {
                continue;
            };
            if !is_local_or_param(symbol)
                || local_symbols.contains(&symbol)
                || captures
                    .captures
                    .iter()
                    .any(|existing| existing.symbol == symbol)
            {
                continue;
            }
            let Some(ty) = self.symbol_ty(symbol).cloned() else {
                continue;
            };
            captures.captures.push(ClosureCapture {
                id: source_body.id,
                symbol,
                ty,
                borrowed_in_parent: parent_state
                    .is_some_and(|state| state.borrows.contains_key(&KeyPath::root(symbol))),
                mode: Some(capture.mode),
            });
        }
        captures
    }

    fn capture_is_ownership_sensitive(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Borrow(_, inner) => {
                self.contains_borrowed_type(inner) || self.needs_drop_type(inner)
            }
            _ => self.contains_borrowed_type(ty) || self.needs_drop_type(ty),
        }
    }

    fn closure_summary_is_copyable(&self, summary: &ClosureCaptureSummary) -> bool {
        summary.captures.iter().all(|capture| match capture.mode {
            Some(CaptureMode::Copy) => {
                self.is_copy_type(&capture.ty) && !self.contains_borrowed_type(&capture.ty)
            }
            Some(CaptureMode::Move | CaptureMode::BorrowShared | CaptureMode::BorrowMut) => false,
            None => {
                !self.is_borrowed_type(&capture.ty)
                    && !self.capture_is_ownership_sensitive(&capture.ty)
            }
        })
    }

    fn key_path_stores_noncopy_closure(&self, key_path: &KeyPath, state: &MoveState) -> bool {
        state
            .closure_captures
            .get(key_path)
            .is_some_and(|summary| !self.closure_summary_is_copyable(summary))
    }

    fn capture_is_escape_sensitive(&self, capture: &ClosureCapture) -> bool {
        if let Ty::Borrow(_, inner) = &capture.ty
            && self.is_copy_local_cell_capture(capture, inner)
        {
            return false;
        }
        self.contains_borrowed_type(&capture.ty)
            || self.needs_drop_type(&capture.ty)
            || self.type_contains_param(&capture.ty)
    }

    fn is_copy_local_cell_capture(&self, capture: &ClosureCapture, inner: &Ty) -> bool {
        let symbol = capture.symbol;
        if !matches!(
            symbol,
            Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_)
        ) || capture.borrowed_in_parent
            || !self.resolved.mutated_symbols.contains(&symbol)
        {
            return false;
        }
        self.is_copy_type(inner)
            && !self.contains_borrowed_type(inner)
            && !self.needs_drop_type(inner)
            && !self.type_contains_param(inner)
    }

    fn check_capture_modes(&mut self, summary: &ClosureCaptureSummary, require_explicit: bool) {
        for capture in &summary.captures {
            let name = self.render_symbol(capture.symbol);
            let ty = capture.ty.render_mono();
            match capture.mode {
                None if require_explicit => {
                    self.error(
                        capture.id,
                        OwnershipError::ImplicitClosureCapture { name, ty },
                    );
                }
                None => {}
                Some(CaptureMode::Copy) => {
                    if !self.is_copy_type(&capture.ty) {
                        self.error(
                            capture.id,
                            OwnershipError::InvalidClosureCaptureMode {
                                name,
                                mode: capture_mode_name(CaptureMode::Copy).to_string(),
                                ty,
                                reason: "copy captures require a copyable type".to_string(),
                            },
                        );
                    }
                }
                Some(CaptureMode::Move) => {
                    if self.is_borrowed_type(&capture.ty)
                        || self.contains_borrowed_type(&capture.ty)
                    {
                        self.error(
                            capture.id,
                            OwnershipError::InvalidClosureCaptureMode {
                                name,
                                mode: capture_mode_name(CaptureMode::Move).to_string(),
                                ty,
                                reason: "move captures cannot take ownership of borrowed values"
                                    .to_string(),
                            },
                        );
                    }
                }
                Some(CaptureMode::BorrowShared | CaptureMode::BorrowMut) => {}
            }
        }
    }

    fn check_escaping_closure_summary(&mut self, summary: &ClosureCaptureSummary) {
        self.check_capture_modes(summary, false);
        for capture in &summary.captures {
            if matches!(
                capture.mode,
                Some(CaptureMode::BorrowShared | CaptureMode::BorrowMut)
            ) {
                self.error(
                    capture.id,
                    OwnershipError::EscapingClosureCapture {
                        name: self.render_symbol(capture.symbol),
                        ty: capture.ty.render_mono(),
                        reason: "borrow captures are tied to the current stack frame".to_string(),
                    },
                );
            } else if capture.mode.is_none() && self.capture_is_escape_sensitive(capture) {
                self.error(
                    capture.id,
                    OwnershipError::UnsupportedClosureCapture {
                        name: self.render_symbol(capture.symbol),
                        ty: capture.ty.render_mono(),
                    },
                );
            }
        }
    }

    fn capture_uses(&self, body: &mir::Body) -> FxHashMap<Symbol, (NodeID, Ty)> {
        let mut captures = FxHashMap::default();
        for block in &body.blocks {
            for statement in &block.statements {
                match &statement.kind {
                    mir::Statement::Read { expr } => {
                        let Some(root) = root_expr(expr) else {
                            continue;
                        };
                        let ExprKind::Variable(name) = &root.kind else {
                            continue;
                        };
                        let Ok(symbol) = name.symbol() else {
                            continue;
                        };
                        captures.entry(symbol).or_insert((root.id, root.ty.clone()));
                    }
                    mir::Statement::AssignmentRootUse { id, ty, symbol } => {
                        captures.entry(*symbol).or_insert((*id, (*ty).clone()));
                    }
                    _ => {}
                }
            }
        }
        captures
    }

    fn closure_values_capture_summary(
        &self,
        expr: &Expr,
        state: &MoveState,
    ) -> ClosureCaptureSummary {
        let mut summary = ClosureCaptureSummary::default();
        self.collect_closure_values_capture_summary(expr, state, true, &mut summary);
        summary
    }

    fn closure_literal_capture_summary(
        &self,
        expr: &Expr,
        state: &MoveState,
    ) -> ClosureCaptureSummary {
        let mut summary = ClosureCaptureSummary::default();
        self.collect_closure_values_capture_summary(expr, state, false, &mut summary);
        summary
    }

    fn collect_closure_values_capture_summary(
        &self,
        expr: &Expr,
        state: &MoveState,
        include_stored_closures: bool,
        summary: &mut ClosureCaptureSummary,
    ) {
        match &expr.kind {
            ExprKind::Func(func) => {
                let body = mir::build_block(self.types, &func.body);
                summary.extend(self.closure_capture_summary(
                    &func.captures,
                    &func.params,
                    &func.body,
                    &body,
                    Some(state),
                ));
            }
            ExprKind::Variable(name) => {
                if include_stored_closures
                    && let Ok(symbol) = name.symbol()
                    && let Some(captures) = state.closure_captures.get(&KeyPath::root(symbol))
                {
                    summary.extend(captures.clone());
                }
            }
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
                for item in items {
                    self.collect_closure_values_capture_summary(
                        item,
                        state,
                        include_stored_closures,
                        summary,
                    );
                }
            }
            ExprKind::As(inner, _) => {
                self.collect_closure_values_capture_summary(
                    inner,
                    state,
                    include_stored_closures,
                    summary,
                );
            }
            ExprKind::Block(block) => {
                if let Some(expr) = block_tail_expr(block) {
                    self.collect_closure_values_capture_summary(
                        expr,
                        state,
                        include_stored_closures,
                        summary,
                    );
                }
            }
            ExprKind::If(_, then_block, else_block) => {
                if let Some(expr) = block_tail_expr(then_block) {
                    self.collect_closure_values_capture_summary(
                        expr,
                        state,
                        include_stored_closures,
                        summary,
                    );
                }
                if let Some(expr) = block_tail_expr(else_block) {
                    self.collect_closure_values_capture_summary(
                        expr,
                        state,
                        include_stored_closures,
                        summary,
                    );
                }
            }
            ExprKind::Match(_, arms) => {
                for arm in arms {
                    if let Some(expr) = block_tail_expr(&arm.body) {
                        self.collect_closure_values_capture_summary(
                            expr,
                            state,
                            include_stored_closures,
                            summary,
                        );
                    }
                }
            }
            ExprKind::RecordLiteral { fields, spread } => {
                if let Some(spread) = spread {
                    self.collect_closure_values_capture_summary(
                        spread,
                        state,
                        include_stored_closures,
                        summary,
                    );
                }
                for field in fields {
                    self.collect_closure_values_capture_summary(
                        &field.value,
                        state,
                        include_stored_closures,
                        summary,
                    );
                }
            }
            ExprKind::Call { .. }
            | ExprKind::CallEffect { .. }
            | ExprKind::Member(..)
            | ExprKind::InlineIR(_)
            | ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_)
            | ExprKind::Constructor(_)
            | ExprKind::RowVariable(_) => {}
        }
    }

    fn check_escaping_closure_values(&mut self, expr: &Expr, state: &MoveState) {
        let summary = self.closure_values_capture_summary(expr, state);
        self.check_escaping_closure_summary(&summary);
    }

    fn apply_closure_capture_effects(
        &mut self,
        summary: &ClosureCaptureSummary,
        borrower: Option<&KeyPath>,
        point: OwnershipPoint,
        state: &mut MoveState,
    ) {
        self.check_capture_modes(summary, false);
        for capture in &summary.captures {
            match capture.mode {
                None => {}
                Some(CaptureMode::Copy) => {
                    self.check_capture_read(capture, state);
                }
                Some(CaptureMode::Move) => {
                    self.apply_capture_move(capture, state);
                }
                Some(CaptureMode::BorrowShared) => {
                    self.apply_capture_borrow(capture, BorrowKind::Shared, borrower, point, state);
                }
                Some(CaptureMode::BorrowMut) => {
                    self.apply_capture_borrow(capture, BorrowKind::Mutable, borrower, point, state);
                }
            }
        }
    }

    fn check_capture_read(&mut self, capture: &ClosureCapture, state: &mut MoveState) {
        let key_path = KeyPath::root(capture.symbol);
        self.check_key_path_use_for_id(capture.id, &capture.ty, &key_path, false, state);
    }

    fn apply_capture_move(&mut self, capture: &ClosureCapture, state: &mut MoveState) {
        let key_path = KeyPath::root(capture.symbol);
        self.check_key_path_use_for_id(capture.id, &capture.ty, &key_path, true, state);
        self.check_move_out_of_borrowed_key_path(capture.id, &key_path, state);
        self.check_move_while_borrowed(capture.id, &key_path, state);
        state
            .moved
            .insert(key_path.clone(), (capture.id, capture.ty.clone()));
        state.invalidate_borrows_of(&key_path);
    }

    fn apply_capture_borrow(
        &mut self,
        capture: &ClosureCapture,
        kind: BorrowKind,
        borrower: Option<&KeyPath>,
        point: OwnershipPoint,
        state: &mut MoveState,
    ) {
        let source = KeyPath::root(capture.symbol);
        self.check_key_path_use_for_id(capture.id, &capture.ty, &source, false, state);
        let owner = self.loan_owner_for_key_path(&source, state);
        self.check_borrow_conflicts(capture.id, &owner, kind, Some(&source), state);
        let Some(borrower) = borrower else {
            return;
        };
        let provenance = BorrowProvenance::direct(BorrowInfo::with_kind(
            self.origin_for_storage_borrow(&source, &capture.ty),
            Some(owner),
            kind,
        ));
        self.install_provenance(
            borrower.clone(),
            provenance,
            Some(capture.id),
            point,
            Some(capture.ty.clone()),
            state,
        );
    }

    fn record_origin_fact(
        &mut self,
        point: OwnershipPoint,
        node: Option<NodeID>,
        borrower: KeyPath,
        ty: Option<Ty>,
    ) -> OriginId {
        let origin = OriginId(self.output.facts.origins.len() as u32);
        self.output.facts.origins.push(OriginFact {
            id: origin,
            point,
            node,
            borrower,
            ty,
        });
        origin
    }

    fn record_borrow_fact(
        &mut self,
        origin: OriginId,
        point: OwnershipPoint,
        node: Option<NodeID>,
        borrower: KeyPath,
        owner: Option<KeyPath>,
        kind: BorrowKind,
    ) -> LoanId {
        let key = BorrowFactKey {
            point,
            node,
            borrower: borrower.clone(),
            owner: owner.clone(),
            kind,
        };
        if let Some(loan_id) = self.recorded_borrow_facts.get(&key) {
            return *loan_id;
        }
        let loan_id = LoanId(self.output.facts.borrows.len() as u32);
        self.output.facts.borrows.push(LoanFact {
            id: loan_id,
            origin,
            point,
            node,
            borrower,
            owner,
            kind,
        });
        self.recorded_borrow_facts.insert(key, loan_id);
        loan_id
    }

    fn record_mir_body_once(
        &mut self,
        key: BodyCacheKey,
        body: &mir::Body,
        kind: BodyKind,
    ) -> BodyId {
        if let Some(body_id) = self.recorded_mir_bodies.get(&key) {
            return *body_id;
        }
        let body_id = self.record_mir_body(body, kind);
        self.recorded_mir_bodies.insert(key, body_id);
        body_id
    }

    fn record_mir_body(&mut self, body: &mir::Body, kind: BodyKind) -> BodyId {
        let body_id = BodyId(self.output.facts.bodies.len() as u32);
        self.output.facts.bodies.push(OwnershipBody {
            id: body_id,
            kind,
            owner: body.owner,
        });
        for scope in &body.scopes {
            self.output.facts.scopes.push(ScopeFact {
                body: body_id,
                scope: scope.id.0 as u32,
                parent: scope.parent.map(|scope| scope.0 as u32),
            });
        }
        for (block_index, block) in body.blocks.iter().enumerate() {
            for statement in &block.statements {
                let point = OwnershipPoint {
                    body: body_id,
                    point: statement.point.0 as u32,
                };
                self.output.facts.points.push(PointFact {
                    point,
                    kind: point_kind(&statement.kind),
                    node: source_node_for_mir_statement(&statement.kind),
                });
                self.record_statement_fact(body, point, &statement.kind);
            }
            for pair in block.statements.windows(2) {
                let from = OwnershipPoint {
                    body: body_id,
                    point: pair[0].point.0 as u32,
                };
                let to = OwnershipPoint {
                    body: body_id,
                    point: pair[1].point.0 as u32,
                };
                self.output.facts.cfg_edges.push((from, to));
            }
            let Some(last) = block.statements.last() else {
                continue;
            };
            let from = OwnershipPoint {
                body: body_id,
                point: last.point.0 as u32,
            };
            for successor in terminator_successors(&block.terminator) {
                if successor.0 == block_index {
                    continue;
                }
                if let Some(first) = body.blocks[successor.0].statements.first() {
                    self.output.facts.cfg_edges.push((
                        from,
                        OwnershipPoint {
                            body: body_id,
                            point: first.point.0 as u32,
                        },
                    ));
                }
            }
        }
        body_id
    }

    fn record_statement_fact(
        &mut self,
        body: &mir::Body,
        point: OwnershipPoint,
        statement: &mir::Statement,
    ) {
        match statement {
            mir::Statement::StorageLive { symbol, .. } => {
                self.output.facts.storage_live.push(StorageFact {
                    point,
                    node: source_node_for_mir_statement(statement),
                    key_path: KeyPath::root(*symbol),
                    ty: self.symbol_ty(*symbol).cloned(),
                });
            }
            mir::Statement::StorageDead { symbol, .. } => {
                self.output.facts.storage_dead.push(StorageFact {
                    point,
                    node: source_node_for_mir_statement(statement),
                    key_path: KeyPath::root(*symbol),
                    ty: self.symbol_ty(*symbol).cloned(),
                });
            }
            mir::Statement::Assign { lhs, target, .. } => {
                if let Some(target) = target
                    .as_ref()
                    .and_then(|target| Self::key_path_from_mir(body, target))
                    .or_else(|| self.key_path(lhs))
                {
                    self.output.facts.assignments.push(AssignmentFact {
                        point,
                        node: source_node_for_mir_statement(statement),
                        ty: self.key_path_ty(&target),
                        target,
                    });
                }
            }
            mir::Statement::DropCandidate {
                target,
                key_path,
                reason,
                ..
            } => {
                let node =
                    drop_target_node(target).or_else(|| source_node_for_mir_statement(statement));
                if let Some(target) = key_path
                    .as_ref()
                    .and_then(|target| Self::key_path_from_mir(body, target))
                    .or_else(|| self.drop_target_key_path(target))
                {
                    self.output.facts.candidate_drops.push(CandidateDropFact {
                        point,
                        node,
                        ty: self.key_path_ty(&target),
                        target,
                        reason: *reason,
                    });
                }
            }
            _ => {}
        }
    }

    /// Elaborate this body's drops once (filling the node-keyed `drop_plan` + `facts.moves` the
    /// editor's hints read) and project the per-point results onto the body's own statements,
    /// which is what lowering reads off `statement.ownership`. One elaboration serves both.
    fn elaborate_and_project(&mut self, key: BodyCacheKey, body_id: BodyId, body: &mut mir::Body) {
        if self.elaborated_mir_bodies.insert(key) {
            self.elaborate_drops(body_id, body);
        }
        self.project_drops_onto_body(body_id, body);
    }

    fn project_drops_onto_body(&self, body_id: BodyId, body: &mut mir::Body) {
        for statement in body
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.statements)
        {
            let point = statement.point.0 as u32;
            statement.ownership.drop = self
                .output
                .drop_plan
                .obligations
                .iter()
                .find(|obligation| {
                    obligation.point.body == body_id && obligation.point.point == point
                })
                .map(|obligation| mir::DropElaborationResult {
                    key_path: obligation.key_path.clone(),
                    kind: obligation.kind,
                });
            statement.ownership.moves = self
                .output
                .facts
                .moves
                .iter()
                .filter(|fact| fact.point.body == body_id && fact.point.point == point)
                .map(|fact| fact.source.clone())
                .collect();
        }
    }

    /// Persist a fully built + elaborated body so lowering can reuse it instead of rebuilding
    /// the MIR. Keyed once; the first body for a key wins (later identical builds are dropped).
    fn persist_body(&mut self, key: BodyCacheKey, body: mir::Body) {
        self.output.mir_bodies.entry(key).or_insert(body);
    }

    /// Resolve each `DropCandidate` to a drop obligation and record the moves at each
    /// point, keyed by `(body_id, statement point)`. This populates `drop_plan` + `facts.moves`,
    /// consumed by the LSP ownership inlay hints/hover and, after projection onto the
    /// statements, by lowering (see [`elaborate_body_drops`]).
    fn elaborate_drops(&mut self, body_id: BodyId, body: &mut mir::Body) {
        let locals = body.locals.clone();
        let in_states = self.drop_entry_states(body, &locals);

        for (block_index, block) in body.blocks.iter_mut().enumerate() {
            let mut state = in_states
                .get(block_index)
                .and_then(Clone::clone)
                .unwrap_or_default();
            for statement in &mut block.statements {
                let point = OwnershipPoint {
                    body: body_id,
                    point: statement.point.0 as u32,
                };
                let statement_node = source_node_for_mir_statement(&statement.kind);
                match &mut statement.kind {
                    mir::Statement::DropCandidate {
                        target,
                        key_path,
                        reason,
                    } => {
                        let Some(key_path) = key_path
                            .as_ref()
                            .and_then(|target| Self::key_path_from_mir_locals(&locals, target))
                            .or_else(|| self.drop_target_key_path(target))
                        else {
                            continue;
                        };
                        let Some(ty) = self.key_path_ty_with_roots(&key_path, &state.root_tys)
                        else {
                            continue;
                        };
                        if !self.needs_drop_type(&ty) {
                            continue;
                        }
                        let kind = classify_drop(&key_path, &state);
                        self.output.drop_plan.obligations.push(DropObligation {
                            point,
                            node: drop_target_node(target).or(statement_node),
                            key_path,
                            ty,
                            kind,
                            reason: *reason,
                        });
                    }
                    _ => self.transfer_drop_statement(
                        &statement.kind,
                        &locals,
                        Some(point),
                        &mut state,
                    ),
                }
            }
        }
    }

    fn drop_entry_states(
        &mut self,
        body: &mir::Body,
        locals: &[mir::LocalDecl],
    ) -> Vec<Option<DropState>> {
        let mut in_states: Vec<Option<DropState>> = vec![None; body.blocks.len()];
        if body.blocks.is_empty() {
            return in_states;
        }
        in_states[body.entry.0] = Some(DropState::default());

        let mut worklist = VecDeque::new();
        worklist.push_back(body.entry);

        while let Some(block) = worklist.pop_front() {
            let Some(mut state) = in_states[block.0].clone() else {
                continue;
            };
            for statement in &body.blocks[block.0].statements {
                self.transfer_drop_statement(&statement.kind, locals, None, &mut state);
            }
            for successor in terminator_successors(&body.blocks[block.0].terminator) {
                let changed = match &mut in_states[successor.0] {
                    Some(existing) => existing.merge_from(&state),
                    slot @ None => {
                        *slot = Some(state.clone());
                        true
                    }
                };
                if changed {
                    worklist.push_back(successor);
                }
            }
        }

        in_states
    }

    fn transfer_drop_statement(
        &mut self,
        statement: &mir::Statement,
        locals: &[mir::LocalDecl],
        point: Option<OwnershipPoint>,
        state: &mut DropState,
    ) {
        match statement {
            mir::Statement::StorageLive { .. } => {}
            mir::Statement::Bind { lhs, rhs, .. } => {
                if let Some(rhs) = rhs {
                    self.note_drop_move(rhs, point, state);
                    self.note_capture_drop_moves(rhs, point, state);
                }
                let binders = lhs.collect_binders();
                let rhs_ty = rhs.as_ref().map(|rhs| rhs.ty.clone());
                for (id, symbol) in binders.iter().copied() {
                    if binders.len() == 1 {
                        if let Some(ty) = rhs_ty.clone() {
                            state.root_tys.insert(symbol, ty);
                        }
                    } else if let Some(ty) = self.symbol_ty(symbol).cloned() {
                        state.root_tys.insert(symbol, ty);
                    }
                    let key_path = KeyPath::root(symbol);
                    if rhs.is_some() {
                        state.initialize_key_path(key_path);
                    } else {
                        state.mark_uninitialized(key_path, id);
                    }
                }
            }
            mir::Statement::Assign {
                lhs, rhs, target, ..
            } => {
                self.note_drop_move(rhs, point, state);
                self.note_capture_drop_moves(rhs, point, state);
                if let Some(target) = target
                    .as_ref()
                    .and_then(|target| Self::key_path_from_mir_locals(locals, target))
                    .or_else(|| self.key_path(lhs))
                {
                    if target.fields.is_empty() {
                        state.root_tys.insert(target.root, lhs.ty.clone());
                    }
                    state.initialize_key_path(target);
                }
            }
            mir::Statement::Call { callee, args, .. } => {
                self.note_capture_drop_moves(callee, point, state);
                self.note_call_drop_moves(callee, args, point, state);
            }
            mir::Statement::ConsumeValue { expr, .. } => {
                self.note_drop_move(expr, point, state);
                self.note_capture_drop_moves(expr, point, state);
            }
            mir::Statement::ReturnValue { expr, .. }
            | mir::Statement::ContinueValue { expr, .. } => {
                self.note_drop_move(expr, point, state);
                self.note_capture_drop_moves(expr, point, state);
            }
            mir::Statement::StorageDead { symbol, .. } => {
                state.finish_storage(&KeyPath::root(*symbol));
            }
            mir::Statement::Read { .. }
            | mir::Statement::AssignmentRootUse { .. }
            | mir::Statement::Perform
            | mir::Statement::DropCandidate { .. }
            | mir::Statement::Function { .. }
            | mir::Statement::Handling { .. }
            | mir::Statement::DeclBody { .. }
            | mir::Statement::ScopeEnter { .. }
            | mir::Statement::ScopeExit { .. } => {}
        }
    }

    fn note_drop_move(
        &mut self,
        expr: &Expr,
        point: Option<OwnershipPoint>,
        state: &mut DropState,
    ) {
        let mut consumed = Vec::new();
        self.collect_consumed_value_exprs(expr, &mut consumed);
        for expr in consumed {
            let Some(key_path) = self.key_path(expr) else {
                continue;
            };
            let ty = Some(expr.ty.clone());
            self.note_drop_key_path_move(expr.id, &key_path, ty, point, state);
        }
    }

    fn note_drop_key_path_move(
        &mut self,
        id: NodeID,
        key_path: &KeyPath,
        ty: Option<Ty>,
        point: Option<OwnershipPoint>,
        state: &mut DropState,
    ) {
        let Some(ty) = ty else {
            return;
        };
        if !self.needs_drop_type(&ty) || !key_path.is_tracked_storage_root() {
            return;
        }
        state.note_move(key_path.clone(), id);
        if let Some(point) = point {
            self.record_move_fact(point, Some(id), key_path.clone(), ty);
        }
    }

    fn record_move_fact(
        &mut self,
        point: OwnershipPoint,
        node: Option<NodeID>,
        source: KeyPath,
        ty: Ty,
    ) {
        let key = MoveFactKey {
            point,
            node,
            source: source.clone(),
            ty: ty.clone(),
        };
        if self.recorded_move_facts.insert(key) {
            self.output.facts.moves.push(MoveFact {
                point,
                node,
                source,
                ty,
            });
        }
    }

    fn note_call_drop_moves(
        &mut self,
        callee: &Expr,
        args: &[hir::CallArg],
        point: Option<OwnershipPoint>,
        state: &mut DropState,
    ) {
        let borrowed_constructor = self.call_constructs_borrowed_value(callee);
        if let ExprKind::Member(Some(receiver), ..) = &callee.kind
            && self.stored_field_symbol(callee).is_none()
        {
            match self.member_self_param(callee) {
                Some(Ty::Borrow(..)) => {}
                _ => self.note_drop_move(receiver, point, state),
            }
            let params = self
                .member_value_params(callee)
                .or_else(|| self.call_argument_types(callee));
            for (index, arg) in args.iter().enumerate() {
                if !matches!(
                    params.as_ref().and_then(|params| params.get(index)),
                    Some(Ty::Borrow(..))
                ) && !borrowed_constructor
                {
                    self.note_drop_move(&arg.value, point, state);
                    self.note_capture_drop_moves(&arg.value, point, state);
                }
            }
        } else {
            let params = self.call_argument_types(callee);
            for (index, arg) in args.iter().enumerate() {
                if !matches!(
                    params.as_ref().and_then(|params| params.get(index)),
                    Some(Ty::Borrow(..))
                ) && !borrowed_constructor
                {
                    self.note_drop_move(&arg.value, point, state);
                    self.note_capture_drop_moves(&arg.value, point, state);
                }
            }
        }
    }

    fn note_capture_drop_moves(
        &mut self,
        expr: &Expr,
        point: Option<OwnershipPoint>,
        state: &mut DropState,
    ) {
        match &expr.kind {
            ExprKind::Func(func) => {
                for capture in &func.captures {
                    if capture.mode != CaptureMode::Move {
                        continue;
                    }
                    let Ok(symbol) = capture.name.symbol() else {
                        continue;
                    };
                    let key_path = KeyPath::root(symbol);
                    let Some(ty) = self.symbol_ty(symbol).cloned() else {
                        continue;
                    };
                    if self.needs_drop_type(&ty) && key_path.is_tracked_storage_root() {
                        state.note_move(key_path.clone(), expr.id);
                        if let Some(point) = point {
                            self.record_move_fact(point, Some(expr.id), key_path, ty);
                        }
                    }
                }
            }
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
                for item in items {
                    self.note_capture_drop_moves(item, point, state);
                }
            }
            ExprKind::As(inner, _) => {
                self.note_capture_drop_moves(inner, point, state);
            }
            ExprKind::Block(block) => {
                if let Some(expr) = block_tail_expr(block) {
                    self.note_capture_drop_moves(expr, point, state);
                }
            }
            ExprKind::If(_, then_block, else_block) => {
                if let Some(expr) = block_tail_expr(then_block) {
                    self.note_capture_drop_moves(expr, point, state);
                }
                if let Some(expr) = block_tail_expr(else_block) {
                    self.note_capture_drop_moves(expr, point, state);
                }
            }
            ExprKind::Match(_, arms) => {
                for arm in arms {
                    if let Some(expr) = block_tail_expr(&arm.body) {
                        self.note_capture_drop_moves(expr, point, state);
                    }
                }
            }
            ExprKind::RecordLiteral { fields, spread } => {
                if let Some(spread) = spread {
                    self.note_capture_drop_moves(spread, point, state);
                }
                for field in fields {
                    self.note_capture_drop_moves(&field.value, point, state);
                }
            }
            ExprKind::Call { .. }
            | ExprKind::CallEffect { .. }
            | ExprKind::Member(..)
            | ExprKind::InlineIR(_)
            | ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_)
            | ExprKind::Variable(_)
            | ExprKind::Constructor(_)
            | ExprKind::RowVariable(_) => {}
        }
    }

    fn check_mir_body(&mut self, body_id: BodyId, body: &mir::Body, state: &mut MoveState) {
        let _ = self.check_mir_body_exit_state(body_id, body, state, &FxHashSet::default());
    }

    fn check_mir_body_exit_state(
        &mut self,
        body_id: BodyId,
        body: &mir::Body,
        state: &MoveState,
        live_at_exit: &FxHashSet<Symbol>,
    ) -> MoveState {
        if body.blocks.is_empty() {
            return state.clone();
        }
        let liveness = borrow_liveness(body, live_at_exit);
        let return_ty = self.body_return_ty(body.owner);

        let mut in_states: Vec<Option<MoveState>> = vec![None; body.blocks.len()];
        in_states[body.entry.0] = Some(state.clone());
        let mut exit_state = MoveState::default();

        let mut worklist = VecDeque::new();
        worklist.push_back(body.entry);

        while let Some(block) = worklist.pop_front() {
            let Some(mut block_state) = in_states[block.0].clone() else {
                continue;
            };
            self.check_mir_block(
                body_id,
                body,
                block,
                &liveness,
                return_ty.as_ref(),
                &mut block_state,
            );

            let successors = self.successor_states(body_id, body, block, &block_state);
            if successors.is_empty() {
                exit_state.merge_from(&block_state);
            }

            for (successor, successor_state) in successors {
                let changed = match &mut in_states[successor.0] {
                    Some(existing) => existing.merge_from(&successor_state),
                    slot @ None => {
                        *slot = Some(successor_state);
                        true
                    }
                };
                if changed {
                    worklist.push_back(successor);
                }
            }
        }

        exit_state
    }

    fn check_mir_block(
        &mut self,
        body_id: BodyId,
        body: &mir::Body,
        block: mir::BlockId,
        liveness: &BorrowLiveness,
        return_ty: Option<&Ty>,
        state: &mut MoveState,
    ) {
        let basic_block = &body.blocks[block.0];
        for statement in &basic_block.statements {
            let point = OwnershipPoint {
                body: body_id,
                point: statement.point.0 as u32,
            };
            let live_after = liveness
                .live_out_by_point
                .get(&statement.point.0)
                .cloned()
                .unwrap_or_default();
            let context = StatementContext {
                point,
                live_after: &live_after,
                return_ty,
            };
            self.check_mir_statement(context, &statement.kind, state);
            state.prune_dead_loans(&live_after);
        }
    }

    fn successor_states(
        &mut self,
        body_id: BodyId,
        body: &mir::Body,
        block: mir::BlockId,
        state: &MoveState,
    ) -> Vec<(mir::BlockId, MoveState)> {
        match &body.blocks[block.0].terminator {
            mir::Terminator::Switch {
                scrutinee,
                match_arms: Some(match_arms),
                arms,
                default,
            } => {
                let mut successors = vec![];
                for (arm, successor) in match_arms.iter().zip(arms) {
                    let mut arm_state = state.clone();
                    let point = body.blocks[successor.0]
                        .statements
                        .first()
                        .map(|statement| OwnershipPoint {
                            body: body_id,
                            point: statement.point.0 as u32,
                        });
                    self.apply_pattern_provenance(scrutinee, &arm.pattern, point, &mut arm_state);
                    successors.push((*successor, arm_state));
                }
                if let Some(successor) = default {
                    successors.push((*successor, state.clone()));
                }
                successors
            }
            terminator => terminator_successors(terminator)
                .into_iter()
                .map(|successor| (successor, state.clone()))
                .collect(),
        }
    }

    fn apply_pattern_provenance(
        &mut self,
        scrutinee: &Expr,
        pattern: &hir::Pattern,
        point: Option<OwnershipPoint>,
        state: &mut MoveState,
    ) {
        let provenance = self.expr_provenance(scrutinee, state);
        if provenance.is_empty() {
            return;
        }
        for (id, symbol) in pattern.collect_binders() {
            let Some(ty) = self.symbol_ty(symbol).cloned() else {
                continue;
            };
            if !self.value_type_contains_borrow(&ty) {
                continue;
            }
            let key_path = KeyPath::root(symbol);
            let point = point.unwrap_or(OwnershipPoint {
                body: BodyId(0),
                point: 0,
            });
            self.validate_local_provenance(id, &ty, &provenance);
            self.install_provenance(
                key_path,
                provenance.clone(),
                Some(id),
                point,
                Some(ty),
                state,
            );
        }
    }

    fn body_return_ty(&self, owner: Option<Symbol>) -> Option<Ty> {
        let owner = owner?;
        let Ty::Func(_, ret, _) = &self.types.schemes.get(&owner)?.ty else {
            return None;
        };
        Some((**ret).clone())
    }

    fn check_mir_statement(
        &mut self,
        context: StatementContext<'_>,
        statement: &mir::Statement,
        state: &mut MoveState,
    ) {
        match statement {
            mir::Statement::ScopeEnter { .. }
            | mir::Statement::ScopeExit { .. }
            | mir::Statement::StorageLive { .. }
            | mir::Statement::DropCandidate { .. } => {}
            mir::Statement::StorageDead { symbol, .. } => {
                state.finish_storage(&KeyPath::root(*symbol));
            }
            mir::Statement::Read { expr } => self.check_read_expr(expr, state),
            mir::Statement::ConsumeValue { expr, .. } => {
                self.check_consumed_expr(context.point, expr, state)
            }
            mir::Statement::AssignmentRootUse { id, symbol, .. } => {
                self.check_assignment_root_use(*id, *symbol, state)
            }
            mir::Statement::Bind {
                lhs,
                type_annotation,
                rhs,
                ..
            } => self.check_binding(
                context.point,
                lhs,
                type_annotation.as_ref(),
                rhs.as_ref(),
                state,
            ),
            mir::Statement::Assign { lhs, rhs, .. } => {
                self.check_assignment(context.point, lhs, rhs, state)
            }
            mir::Statement::Call {
                callee,
                args,
                trailing_block,
                trailing_body,
            } => self.check_call(
                callee,
                args,
                trailing_block.as_ref(),
                trailing_body.as_deref(),
                context,
                state,
            ),
            mir::Statement::Perform => {}
            mir::Statement::ReturnValue { expr, .. } => {
                self.check_return_value(context.point, expr, context.return_ty, state)
            }
            mir::Statement::ContinueValue { expr, .. } => {
                self.check_consumed_expr(context.point, expr, state)
            }
            mir::Statement::Function {
                owner,
                captures_parent,
                captures,
                params,
                body,
            } => {
                let parent_state = state.clone();
                self.check_func_moves(*owner, captures, params, body, Some(&parent_state));
                if *captures_parent {
                    let function_body = mir::build_function(self.types, *owner, body);
                    let summary = self.closure_capture_summary(
                        captures,
                        params,
                        body,
                        &function_body,
                        Some(&parent_state),
                    );
                    self.apply_closure_capture_effects(&summary, None, context.point, state);
                }
            }
            mir::Statement::Handling { body, .. } => {
                let handler_body = mir::build_block(self.types, body);
                self.check_nested_mir_body(
                    BodyCacheKey::Nested(body.id),
                    &handler_body,
                    state,
                    context.live_after,
                );
            }
            mir::Statement::DeclBody { body } => self.check_body_moves(body),
        }
    }

    fn check_nested_mir_body(
        &mut self,
        key: BodyCacheKey,
        body: &mir::Body,
        state: &mut MoveState,
        live_at_exit: &FxHashSet<Symbol>,
    ) {
        if let Some(memo) = self.nested_body_memos.iter().find(|memo| {
            memo.key == key && memo.live_at_exit == *live_at_exit && memo.input == *state
        }) {
            state.merge_from(&memo.output);
            return;
        }

        let input = state.clone();
        let body_id = self.record_mir_body_once(key, body, BodyKind::Nested);
        let body_state = self.check_mir_body_exit_state(body_id, body, state, live_at_exit);
        self.nested_body_memos.push(NestedBodyMemo {
            key,
            live_at_exit: live_at_exit.clone(),
            input,
            output: body_state.clone(),
        });
        state.merge_from(&body_state);
    }

    fn check_binding(
        &mut self,
        point: OwnershipPoint,
        lhs: &hir::Pattern,
        type_annotation: Option<&crate::node_kinds::type_annotation::TypeAnnotation>,
        rhs: Option<&Expr>,
        state: &mut MoveState,
    ) {
        let direct_borrow_info =
            rhs.and_then(|rhs| self.binding_borrow_info(type_annotation, rhs, state));
        let closure_captures = rhs.map(|rhs| self.closure_values_capture_summary(rhs, state));
        let literal_captures = rhs.map(|rhs| self.closure_literal_capture_summary(rhs, state));
        let binders = lhs.collect_binders();
        let mut installed_borrowed_value = false;
        for (id, symbol) in &binders {
            let key_path = KeyPath::root(*symbol);
            if rhs.is_some() {
                state.initialize_key_path(&key_path);
            } else {
                let ty = self.symbol_ty(*symbol).cloned().unwrap_or(Ty::Error);
                state.moved.insert(key_path.clone(), (*id, ty));
            }
            if let Some(summary) = &closure_captures {
                if binders.len() == 1
                    && let Some(literal_captures) = &literal_captures
                {
                    self.apply_closure_capture_effects(
                        literal_captures,
                        Some(&key_path),
                        point,
                        state,
                    );
                }
                if summary.is_empty() {
                    state.closure_captures.remove(&key_path);
                } else {
                    state
                        .closure_captures
                        .insert(key_path.clone(), summary.clone());
                }
            } else {
                state.closure_captures.remove(&key_path);
            }
            if let Some(rhs) = rhs {
                if let Some(info) = &direct_borrow_info {
                    self.install_borrow(key_path, info.clone(), rhs.id, point, state);
                    installed_borrowed_value = true;
                    continue;
                }
                let ty = self
                    .symbol_ty(*symbol)
                    .cloned()
                    .unwrap_or_else(|| rhs.ty.clone());
                if self.value_type_contains_borrow(&ty) {
                    let provenance = self.provenance_for_expected_ty(&ty, rhs, state);
                    self.validate_local_provenance(rhs.id, &ty, &provenance);
                    self.install_provenance(
                        key_path,
                        provenance,
                        Some(rhs.id),
                        point,
                        Some(ty),
                        state,
                    );
                    installed_borrowed_value = true;
                }
            }
        }
        if !installed_borrowed_value && let Some(rhs) = rhs {
            self.consume_expr_value(rhs, state);
        }
    }

    fn check_assignment(
        &mut self,
        point: OwnershipPoint,
        lhs: &Expr,
        rhs: &Expr,
        state: &mut MoveState,
    ) {
        let closure_captures = self.closure_values_capture_summary(rhs, state);
        let literal_captures = self.closure_literal_capture_summary(rhs, state);
        if let Some((name, ty)) = self.shared_borrow_assignment_receiver(lhs, state) {
            self.error(
                lhs.id,
                OwnershipError::AssignThroughSharedBorrow { name, ty },
            );
        }
        let Some(key_path) = self.key_path(lhs) else {
            return;
        };
        let owner = if key_path.fields.is_empty()
            && state.borrows.contains_key(&KeyPath::root(key_path.root))
        {
            key_path.clone()
        } else {
            self.loan_owner_for_key_path(&key_path, state)
        };
        self.check_borrow_conflicts(lhs.id, &owner, BorrowKind::Mutable, Some(&key_path), state);
        if self.expr_is_owned(lhs) && key_path.is_tracked_storage_root() {
            self.check_move_while_borrowed(lhs.id, &key_path, state);
            state.invalidate_borrows_of(&key_path);
        }
        state.restore_key_path(&key_path);
        if closure_captures.is_empty() {
            state.closure_captures.remove(&key_path);
        } else {
            self.apply_closure_capture_effects(&literal_captures, Some(&key_path), point, state);
            state
                .closure_captures
                .insert(key_path.clone(), closure_captures);
        }
        if self.value_type_contains_borrow(&lhs.ty) {
            let provenance = self.provenance_for_expected_ty(&lhs.ty, rhs, state);
            self.validate_local_provenance(rhs.id, &lhs.ty, &provenance);
            self.install_provenance(
                key_path,
                provenance,
                Some(rhs.id),
                point,
                Some(lhs.ty.clone()),
                state,
            );
        } else {
            self.consume_expr_value(rhs, state);
        }
    }

    fn check_call(
        &mut self,
        callee: &Expr,
        args: &[hir::CallArg],
        trailing_block: Option<&Block>,
        trailing_body: Option<&mir::Body>,
        context: StatementContext<'_>,
        state: &mut MoveState,
    ) {
        if matches!(callee.kind, ExprKind::Func(_)) {
            let callee_captures = self.closure_literal_capture_summary(callee, state);
            self.apply_closure_capture_effects(&callee_captures, None, context.point, state);
        }
        if let ExprKind::Member(Some(receiver), ..) = &callee.kind
            && self.stored_field_symbol(callee).is_none()
        {
            match self.member_self_param(callee) {
                Some(Ty::Borrow(BorrowKind::Mutable, _)) => {
                    if let Some(key_path) = self.key_path(receiver) {
                        let owner = self.loan_owner_for_key_path(&key_path, state);
                        self.check_borrow_conflicts(
                            receiver.id,
                            &owner,
                            BorrowKind::Mutable,
                            Some(&key_path),
                            state,
                        );
                        state.invalidate_borrows_of(&owner);
                    }
                }
                Some(Ty::Borrow(BorrowKind::Shared, _)) => {
                    if let Some(key_path) = self.key_path(receiver) {
                        let owner = self.loan_owner_for_key_path(&key_path, state);
                        self.check_borrow_conflicts(
                            receiver.id,
                            &owner,
                            BorrowKind::Shared,
                            Some(&key_path),
                            state,
                        );
                    }
                }
                _ => self.consume_expr_value(receiver, state),
            }
            let params = self
                .member_value_params(callee)
                .or_else(|| self.call_argument_types(callee));
            self.check_argument_accesses(
                args,
                params.as_ref(),
                self.call_constructs_borrowed_value(callee),
                context.point,
                state,
            );
        } else {
            let params = self.call_argument_types(callee);
            self.check_argument_accesses(
                args,
                params.as_ref(),
                self.call_constructs_borrowed_value(callee),
                context.point,
                state,
            );
        }
        if let (Some(source_block), Some(body)) = (trailing_block, trailing_body) {
            let summary = self.closure_capture_summary(
                &[],
                &source_block.args,
                source_block,
                body,
                Some(state),
            );
            self.check_escaping_closure_summary(&summary);
        }
        if let (Some(source_block), Some(body)) = (trailing_block, trailing_body) {
            self.check_nested_mir_body(
                BodyCacheKey::Nested(source_block.id),
                body,
                state,
                context.live_after,
            );
        }
    }

    fn check_argument_accesses(
        &mut self,
        args: &[hir::CallArg],
        params: Option<&Vec<Ty>>,
        borrowed_constructor: bool,
        point: OwnershipPoint,
        state: &mut MoveState,
    ) {
        for (index, arg) in args.iter().enumerate() {
            match params.and_then(|params| params.get(index)) {
                Some(Ty::Borrow(kind, _)) => {
                    if let Some(key_path) = self.key_path(&arg.value) {
                        let owner = self.loan_owner_for_key_path(&key_path, state);
                        self.check_borrow_conflicts(
                            arg.value.id,
                            &owner,
                            *kind,
                            Some(&key_path),
                            state,
                        );
                        if *kind == BorrowKind::Mutable {
                            state.invalidate_borrows_of(&owner);
                        }
                    }
                }
                _ => {
                    self.check_escaping_closure_values(&arg.value, state);
                    let closure_captures = self.closure_literal_capture_summary(&arg.value, state);
                    self.apply_closure_capture_effects(&closure_captures, None, point, state);
                    if !borrowed_constructor {
                        self.consume_expr_value(&arg.value, state);
                    }
                }
            }
        }
    }

    fn check_read_expr(&mut self, expr: &Expr, state: &mut MoveState) {
        if let Some(key_path) = self.key_path(expr) {
            self.check_key_path_use(expr, &key_path, state);
        }
    }

    fn check_consumed_expr(&mut self, point: OwnershipPoint, expr: &Expr, state: &mut MoveState) {
        self.check_escaping_closure_values(expr, state);
        let closure_captures = self.closure_literal_capture_summary(expr, state);
        self.apply_closure_capture_effects(&closure_captures, None, point, state);
        self.consume_expr_value(expr, state);
    }

    fn check_assignment_root_use(&mut self, id: NodeID, symbol: Symbol, state: &mut MoveState) {
        let key_path = KeyPath::root(symbol);
        if let Some((moved, moved_ty)) = self.moved_key_path_for_use(&key_path, false, state) {
            self.error(
                id,
                OwnershipError::UseAfterMove {
                    name: self.render_key_path(moved),
                    ty: self.move_error_type(moved, moved_ty),
                },
            );
        } else if let Some((borrow, owner)) = self.invalid_borrow_for_use(&key_path, state) {
            self.error(
                id,
                OwnershipError::UseAfterInvalidatedBorrow {
                    name: self.render_key_path(borrow),
                    owner: self.render_key_path(owner),
                    ty: "borrowed value".to_string(),
                },
            );
        }
    }

    fn check_return_value(
        &mut self,
        point: OwnershipPoint,
        expr: &Expr,
        expected: Option<&Ty>,
        state: &mut MoveState,
    ) {
        self.check_escaping_closure_values(expr, state);
        let closure_captures = self.closure_literal_capture_summary(expr, state);
        self.apply_closure_capture_effects(&closure_captures, None, point, state);
        if !self.expr_is_copy(expr) {
            self.check_move_out_of_borrowed_value(expr.id, expr, state);
        }
        if let Some(expected) = expected
            && self.value_type_contains_borrow(expected)
        {
            let provenance = self.provenance_for_expected_ty(expected, expr, state);
            if !(self.module_id == ModuleId::Core
                && provenance.has_unknown()
                && self.expr_mentions_raw_pointer(expr))
            {
                self.validate_return_provenance(expr.id, expected, &provenance);
            }
            return;
        }
        if self.value_type_contains_borrow(&expr.ty) {
            let provenance = self.expr_provenance(expr, state);
            if !(self.module_id == ModuleId::Core
                && provenance.has_unknown()
                && self.expr_mentions_raw_pointer(expr))
            {
                self.validate_return_provenance(expr.id, &expr.ty, &provenance);
            }
            return;
        }
        self.consume_expr_value(expr, state);
    }

    fn seed_shared_borrow_params(
        &self,
        owner: Option<Symbol>,
        params: &[Parameter],
        state: &mut MoveState,
    ) {
        for param in params {
            let Ok(symbol) = param.name.symbol() else {
                continue;
            };
            if self.is_initializer_self(owner, param) {
                continue;
            }
            if let Some(ty) = param.ty.as_ref()
                && self.value_type_contains_borrow(ty)
            {
                let key_path = KeyPath::root(symbol);
                let provenance = match ty {
                    Ty::Borrow(kind, _) => BorrowProvenance::direct(BorrowInfo::with_kind(
                        BorrowOrigin::BorrowedParam,
                        None,
                        *kind,
                    )),
                    _ => {
                        BorrowProvenance::direct(BorrowInfo::new(BorrowOrigin::BorrowedParam, None))
                    }
                };
                state
                    .provenances
                    .insert(key_path.clone(), provenance.clone());
                if self.is_borrowed_type(ty)
                    && let Some(info) = provenance.first_info()
                {
                    state.borrows.insert(key_path, info);
                }
            }
            let Some((kind, ty)) = self.param_borrow_ty(param) else {
                continue;
            };
            state.borrowed_roots.insert(symbol, ty.clone());
            if kind == BorrowKind::Shared {
                state.shared_borrow_roots.insert(symbol, ty);
            }
        }
    }

    fn is_initializer_self(&self, owner: Option<Symbol>, param: &Parameter) -> bool {
        matches!(owner, Some(Symbol::Initializer(_) | Symbol::Synthesized(_)))
            && param.name.name_str() == "self"
    }

    fn mark_simple_move_source(&mut self, expr: &Expr, state: &mut MoveState) {
        if !self.expr_is_copy(expr) {
            self.check_move_out_of_borrowed_value(expr.id, expr, state);
        }
        let Some(key_path) = self.key_path(expr) else {
            return;
        };
        let moves_storage =
            self.expr_is_owned(expr) || self.key_path_stores_noncopy_closure(&key_path, state);
        if moves_storage && key_path.is_tracked_storage_root() {
            self.report_use_after_move_or_invalidated(expr.id, &expr.ty, &key_path, true, state);
            self.check_move_while_borrowed(expr.id, &key_path, state);
            state
                .moved
                .insert(key_path.clone(), (expr.id, expr.ty.clone()));
            state.invalidate_borrows_of(&key_path);
            state.closure_captures.remove(&key_path);
        }
    }

    fn consume_expr_value(&mut self, expr: &Expr, state: &mut MoveState) {
        let mut consumed = Vec::new();
        self.collect_consumed_value_exprs(expr, &mut consumed);
        for expr in consumed {
            self.mark_simple_move_source(expr, state);
        }
    }

    fn collect_consumed_value_exprs<'a>(&self, expr: &'a Expr, out: &mut Vec<&'a Expr>) {
        if self.key_path(expr).is_some() {
            out.push(expr);
            return;
        }

        match &expr.kind {
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
                for item in items {
                    self.collect_consumed_value_exprs(item, out);
                }
            }
            ExprKind::As(inner, _) => {
                self.collect_consumed_value_exprs(inner, out);
            }
            ExprKind::RecordLiteral { fields, spread } => {
                if let Some(spread) = spread {
                    self.collect_consumed_value_exprs(spread, out);
                }
                for field in fields {
                    self.collect_consumed_value_exprs(&field.value, out);
                }
            }
            ExprKind::Block(_)
            | ExprKind::If(..)
            | ExprKind::Match(..)
            | ExprKind::Call { .. }
            | ExprKind::CallEffect { .. }
            | ExprKind::InlineIR(_)
            | ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_)
            | ExprKind::Constructor(_)
            | ExprKind::Func(_)
            | ExprKind::RowVariable(_)
            | ExprKind::Member(None, ..)
            | ExprKind::Variable(_)
            | ExprKind::Member(Some(_), ..) => {}
        }
    }

    fn check_key_path_use(&mut self, expr: &Expr, key_path: &KeyPath, state: &mut MoveState) {
        self.check_key_path_use_for_id(
            expr.id,
            &expr.ty,
            key_path,
            self.expr_is_owned(expr),
            state,
        );
    }

    fn check_key_path_use_for_id(
        &mut self,
        id: NodeID,
        use_ty: &Ty,
        key_path: &KeyPath,
        use_is_owned: bool,
        state: &mut MoveState,
    ) {
        self.report_use_after_move_or_invalidated(id, use_ty, key_path, use_is_owned, state);
        // Using an owned value is a move/consume (its conflict with a live loan is reported by
        // `check_move_while_borrowed`), not the taking of a shared borrow. Only a non-owned use
        // — reading through a borrow or a copy — needs a shared loan of the owner.
        if !use_is_owned {
            let owner = self.loan_owner_for_key_path(key_path, state);
            self.check_borrow_conflicts(id, &owner, BorrowKind::Shared, Some(key_path), state);
        }
    }

    /// Reports use-after-move and use-after-invalidated-borrow for a path. Unlike
    /// `check_key_path_use_for_id`, this does not raise a shared-borrow conflict, so it is
    /// safe to use on the move path (where `check_move_while_borrowed` covers the borrow side
    /// and a move must not be described as taking a shared borrow).
    fn report_use_after_move_or_invalidated(
        &mut self,
        id: NodeID,
        use_ty: &Ty,
        key_path: &KeyPath,
        use_is_owned: bool,
        state: &MoveState,
    ) {
        if let Some((moved, moved_ty)) = self.moved_key_path_for_use(key_path, use_is_owned, state)
        {
            self.error(
                id,
                OwnershipError::UseAfterMove {
                    name: self.render_key_path(moved),
                    ty: self.move_error_type(moved, moved_ty),
                },
            );
        } else if let Some((borrow, owner)) = self.invalid_borrow_for_use(key_path, state) {
            self.error(
                id,
                OwnershipError::UseAfterInvalidatedBorrow {
                    name: self.render_key_path(borrow),
                    owner: self.render_key_path(owner),
                    ty: use_ty.render_mono(),
                },
            );
        }
    }

    /// The type to name in a use-after-move diagnostic: the moved path's structural
    /// type when it resolves, else the type recorded at the move site.
    fn move_error_type(&self, moved: &KeyPath, moved_ty: &Ty) -> String {
        self.key_path_ty(moved)
            .as_ref()
            .unwrap_or(moved_ty)
            .render_mono()
    }

    fn moved_key_path_for_use<'a>(
        &self,
        key_path: &KeyPath,
        use_is_owned: bool,
        state: &'a MoveState,
    ) -> Option<(&'a KeyPath, &'a Ty)> {
        state.moved.iter().find_map(|(moved, (_, ty))| {
            (moved.contains(key_path) || key_path.contains(moved) && use_is_owned)
                .then_some((moved, ty))
        })
    }

    fn invalid_borrow_for_use<'a>(
        &self,
        key_path: &KeyPath,
        state: &'a MoveState,
    ) -> Option<(&'a KeyPath, &'a KeyPath)> {
        state
            .invalid_borrows
            .iter()
            .find_map(|(borrow, owner)| borrow.contains(key_path).then_some((borrow, owner)))
    }

    fn key_path(&self, expr: &Expr) -> Option<KeyPath> {
        match &expr.kind {
            ExprKind::Variable(name) => name.symbol().ok().map(KeyPath::root),
            ExprKind::Member(Some(receiver), ..) => {
                let base = self.key_path(receiver)?;
                let property = self.stored_field_symbol(expr)?;
                Some(base.child(property))
            }
            _ => None,
        }
    }

    fn drop_target_key_path(&self, target: &mir::DropTarget) -> Option<KeyPath> {
        match target {
            mir::DropTarget::Symbol { symbol, .. } => Some(KeyPath::root(*symbol)),
            mir::DropTarget::Expr(expr) => self.key_path(expr),
        }
    }

    fn key_path_from_mir(body: &mir::Body, key_path: &mir::KeyPath) -> Option<KeyPath> {
        Self::key_path_from_mir_locals(&body.locals, key_path)
    }

    fn key_path_from_mir_locals(
        locals: &[mir::LocalDecl],
        key_path: &mir::KeyPath,
    ) -> Option<KeyPath> {
        let root = locals.get(key_path.root.0)?.symbol;
        let mut result = KeyPath::root(root);
        for projection in &key_path.components {
            match projection {
                mir::KeyPathComponent::Field(field) => {
                    result = result.child(*field);
                }
                mir::KeyPathComponent::TupleField(_)
                | mir::KeyPathComponent::VariantPayload { .. }
                | mir::KeyPathComponent::DerefBorrow
                | mir::KeyPathComponent::Index(_) => return None,
            }
        }
        Some(result)
    }

    fn symbol_ty(&self, symbol: Symbol) -> Option<&Ty> {
        self.types.schemes.get(&symbol).map(|scheme| &scheme.ty)
    }

    fn key_path_ty(&self, key_path: &KeyPath) -> Option<Ty> {
        self.key_path_ty_with_roots(key_path, &FxHashMap::default())
    }

    fn key_path_ty_with_roots(
        &self,
        key_path: &KeyPath,
        root_tys: &FxHashMap<Symbol, Ty>,
    ) -> Option<Ty> {
        let mut ty = root_tys
            .get(&key_path.root)
            .cloned()
            .or_else(|| self.symbol_ty(key_path.root).cloned())?;
        for field in &key_path.fields {
            ty = self.field_ty(&ty, *field)?;
        }
        Some(ty)
    }

    fn field_ty(&self, owner_ty: &Ty, field: Symbol) -> Option<Ty> {
        let Ty::Nominal(owner, args) = owner_ty else {
            return None;
        };
        let info = self.types.catalog.structs.get(owner)?;
        let substitution = type_param_subst(&info.params, args);
        info.fields.values().find_map(|(candidate, ty)| {
            (candidate == &field)
                .then(|| ty.substitute(&substitution, &Default::default(), &Default::default()))
        })
    }

    fn shared_borrow_assignment_receiver(
        &self,
        expr: &Expr,
        state: &MoveState,
    ) -> Option<(String, String)> {
        let ExprKind::Member(Some(receiver), ..) = &expr.kind else {
            return None;
        };
        if let Some(key_path) = self.key_path(receiver)
            && let Some(ty) = state.shared_borrow_roots.get(&key_path.root)
        {
            return Some((
                self.render_key_path(&KeyPath::root(key_path.root)),
                ty.clone(),
            ));
        }
        if let Ty::Borrow(BorrowKind::Shared, _) = &receiver.ty {
            let name = self
                .key_path(receiver)
                .map(|key_path| self.render_key_path(&key_path))
                .unwrap_or_else(|| "borrowed value".to_string());
            let ty = receiver.ty.render_mono();
            return Some((name, ty));
        }
        self.shared_borrow_assignment_receiver(receiver, state)
    }

    fn param_borrow_ty(&self, param: &Parameter) -> Option<(BorrowKind, String)> {
        if let Some(TypeAnnotationKind::Borrow { mutable, .. }) = param
            .type_annotation
            .as_ref()
            .map(|annotation| &annotation.kind)
        {
            return Some((
                if *mutable {
                    BorrowKind::Mutable
                } else {
                    BorrowKind::Shared
                },
                if *mutable {
                    "mutable borrow".to_string()
                } else {
                    "shared borrow".to_string()
                },
            ));
        }
        if let Some(ty) = param.ty.as_ref()
            && self.is_borrowed_type(ty)
        {
            return Some((BorrowKind::Shared, ty.render_mono()));
        }
        let annotation = param.type_annotation.as_ref()?;
        let symbol = self.borrowed_annotation_symbol(annotation)?;
        Some((BorrowKind::Shared, self.render_symbol(symbol)))
    }

    fn borrowed_annotation_symbol(
        &self,
        annotation: &crate::node_kinds::type_annotation::TypeAnnotation,
    ) -> Option<Symbol> {
        match &annotation.kind {
            TypeAnnotationKind::Nominal { name, .. } => {
                let symbol = name.symbol().ok()?;
                self.is_borrowed_symbol(symbol).then_some(symbol)
            }
            _ => None,
        }
    }

    fn binding_borrow_info(
        &mut self,
        annotation: Option<&crate::node_kinds::type_annotation::TypeAnnotation>,
        rhs: &Expr,
        state: &MoveState,
    ) -> Option<BorrowInfo> {
        let kind = self
            .annotation_borrow_kind(annotation)
            .or_else(|| self.expr_borrow_kind(rhs))?;
        let mut info = self.borrow_info(rhs, &state.borrows);
        if info.origin == BorrowOrigin::Unknown && !self.allows_unknown_local_borrow(rhs) {
            let ty = self.borrowed_value_ty(rhs);
            self.error(rhs.id, OwnershipError::UnknownBorrowProvenance { ty });
        }
        if info.owner.is_none() {
            info.owner = self.key_path(rhs);
        }
        info.kind = kind;
        Some(info)
    }

    fn annotation_borrow_kind(
        &self,
        annotation: Option<&crate::node_kinds::type_annotation::TypeAnnotation>,
    ) -> Option<BorrowKind> {
        match annotation.map(|annotation| &annotation.kind) {
            Some(TypeAnnotationKind::Borrow { mutable: true, .. }) => Some(BorrowKind::Mutable),
            Some(TypeAnnotationKind::Borrow { mutable: false, .. }) => Some(BorrowKind::Shared),
            _ => None,
        }
    }

    fn expr_borrow_kind(&self, expr: &Expr) -> Option<BorrowKind> {
        match &expr.ty {
            Ty::Borrow(kind, _) => Some(*kind),
            ty if self.is_borrowed_type(ty) => Some(BorrowKind::Shared),
            _ => None,
        }
    }

    fn borrowed_value_ty(&self, expr: &Expr) -> String {
        expr.ty.render_mono()
    }

    fn allows_unknown_local_borrow(&self, expr: &Expr) -> bool {
        let Ty::Borrow(_, inner) = &expr.ty else {
            return false;
        };
        self.is_copy_type(inner)
    }

    fn install_borrow(
        &mut self,
        borrower: KeyPath,
        info: BorrowInfo,
        id: NodeID,
        point: OwnershipPoint,
        state: &mut MoveState,
    ) {
        self.install_provenance(
            borrower.clone(),
            BorrowProvenance::direct(info.clone()),
            Some(id),
            point,
            self.key_path_ty(&borrower),
            state,
        );
        state.borrows.insert(borrower, info);
    }

    fn install_provenance(
        &mut self,
        borrower: KeyPath,
        provenance: BorrowProvenance,
        node: Option<NodeID>,
        point: OwnershipPoint,
        ty: Option<Ty>,
        state: &mut MoveState,
    ) {
        if provenance.is_empty() {
            return;
        }
        let origin = self.record_origin_fact(point, node, borrower.clone(), ty.clone());
        for loan in &provenance.loans {
            if let Some(owner) = &loan.owner {
                if let Some(id) = node {
                    self.check_borrow_conflicts(id, owner, loan.kind, None, state);
                }
                state.add_loan(borrower.clone(), owner.clone(), loan.kind);
            }
            self.record_borrow_fact(
                origin,
                point,
                node,
                borrower.clone(),
                loan.owner.clone(),
                loan.kind,
            );
        }
        if let Some(ty) = &ty
            && self.is_borrowed_type(ty)
        {
            if let Some(info) = provenance.first_info() {
                if borrower.fields.is_empty() && info.kind == BorrowKind::Shared {
                    state
                        .shared_borrow_roots
                        .insert(borrower.root, borrow_kind_name(info.kind).to_string());
                }
                state
                    .borrowed_roots
                    .insert(borrower.root, borrow_kind_name(info.kind).to_string());
                state.borrows.insert(borrower.clone(), info);
            }
        }
        state.provenances.insert(borrower.clone(), provenance);
        state.invalid_borrows.remove(&borrower);
    }

    fn loan_owner_for_key_path(&self, key_path: &KeyPath, state: &MoveState) -> KeyPath {
        let root = KeyPath::root(key_path.root);
        if let Some(owner) = state.borrows.get(&root).and_then(|info| info.owner.clone()) {
            let mut fields = owner.fields;
            fields.extend(key_path.fields.iter().copied());
            KeyPath {
                root: owner.root,
                fields,
            }
        } else {
            key_path.clone()
        }
    }

    fn check_borrow_conflicts(
        &mut self,
        id: NodeID,
        owner: &KeyPath,
        requested: BorrowKind,
        requester: Option<&KeyPath>,
        state: &MoveState,
    ) {
        let Some(existing) = state.active_loans.iter().find(|loan| {
            loan.owner.overlaps(owner)
                && !requester.is_some_and(|requester| requester.overlaps(&loan.borrower))
                && (requested == BorrowKind::Mutable || loan.kind == BorrowKind::Mutable)
        }) else {
            return;
        };
        self.error(
            id,
            OwnershipError::OverlappingBorrow {
                owner: self.render_key_path(owner),
                existing: self.render_key_path(&existing.borrower),
                existing_kind: borrow_kind_name(existing.kind).to_string(),
                requested_kind: borrow_kind_name(requested).to_string(),
            },
        );
    }

    fn check_move_while_borrowed(&mut self, id: NodeID, key_path: &KeyPath, state: &MoveState) {
        let Some(existing) = state
            .active_loans
            .iter()
            .find(|loan| loan.owner.overlaps(key_path))
        else {
            return;
        };
        self.error(
            id,
            OwnershipError::MoveWhileBorrowed {
                name: self.render_key_path(key_path),
                borrower: self.render_key_path(&existing.borrower),
            },
        );
    }

    fn check_move_out_of_borrowed_value(&mut self, id: NodeID, expr: &Expr, state: &MoveState) {
        if let Some(key_path) = self.key_path(expr) {
            self.check_move_out_of_borrowed_key_path(id, &key_path, state);
            return;
        }
        let Some(owner) = self.borrowed_member_root(expr, state) else {
            return;
        };
        let name = self
            .render_expr_path(expr)
            .unwrap_or_else(|| "owned field".to_string());
        let ty = expr.ty.render_mono();
        self.error(
            id,
            OwnershipError::MoveOutOfBorrowedValue {
                name,
                owner: self.render_key_path(&owner),
                ty,
            },
        );
    }

    fn check_move_out_of_borrowed_key_path(
        &mut self,
        id: NodeID,
        key_path: &KeyPath,
        state: &MoveState,
    ) {
        if key_path.fields.is_empty() {
            return;
        }
        let Some(owner) = self.borrowed_value_root(key_path, state) else {
            return;
        };
        let ty = self
            .key_path_ty(key_path)
            .map(|ty| ty.render_mono())
            .unwrap_or_else(|| "owned value".to_string());
        self.error(
            id,
            OwnershipError::MoveOutOfBorrowedValue {
                name: self.render_key_path(key_path),
                owner: self.render_key_path(&owner),
                ty,
            },
        );
    }

    fn borrowed_value_root(&self, key_path: &KeyPath, state: &MoveState) -> Option<KeyPath> {
        let root = KeyPath::root(key_path.root);
        if state.borrows.contains_key(&root) || state.borrowed_roots.contains_key(&root.root) {
            return Some(root);
        }
        self.symbol_ty(key_path.root)
            .is_some_and(|ty| self.is_borrowed_type(ty))
            .then_some(root)
    }

    fn borrowed_member_root(&self, expr: &Expr, state: &MoveState) -> Option<KeyPath> {
        let ExprKind::Member(Some(receiver), ..) = &expr.kind else {
            return None;
        };
        let root = root_expr(receiver)?;
        let ExprKind::Variable(name) = &root.kind else {
            return None;
        };
        let symbol = name.symbol().ok()?;
        let root = KeyPath::root(symbol);
        self.borrowed_value_root(&root, state)
    }

    fn stored_field_symbol(&self, expr: &Expr) -> Option<Symbol> {
        stored_field_symbol(self.types, expr.member_resolution.as_ref())
    }

    fn call_argument_types(&self, callee: &Expr) -> Option<Vec<Ty>> {
        let Ty::Func(params, _, _) = &callee.ty else {
            return None;
        };
        Some(params.clone())
    }

    fn member_self_param(&self, callee: &Expr) -> Option<Ty> {
        self.member_callable_params(callee)?.first().cloned()
    }

    fn member_value_params(&self, callee: &Expr) -> Option<Vec<Ty>> {
        let params = self.member_callable_params(callee)?;
        Some(params.get(1..).unwrap_or(&[]).to_vec())
    }

    fn member_callable_params(&self, callee: &Expr) -> Option<Vec<Ty>> {
        let resolution = callee.member_resolution.as_ref()?;
        match resolution {
            crate::types::output::MemberResolution::Direct(symbol) => self
                .types
                .schemes
                .get(symbol)
                .and_then(|scheme| func_params(&scheme.ty)),
            crate::types::output::MemberResolution::ViaConformance { protocol, witness } => self
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

    fn expr_is_owned(&self, expr: &Expr) -> bool {
        self.needs_drop_type(&expr.ty)
    }

    fn expr_is_copy(&self, expr: &Expr) -> bool {
        self.is_copy_type(&expr.ty)
    }

    fn expr_is_borrowed(&self, expr: &Expr) -> bool {
        self.is_borrowed_type(&expr.ty)
    }

    fn value_type_contains_borrow(&self, ty: &Ty) -> bool {
        !matches!(ty, Ty::Func(..)) && self.contains_borrowed_type(ty)
    }

    fn provenance_for_expected_ty(
        &self,
        expected: &Ty,
        expr: &Expr,
        state: &MoveState,
    ) -> BorrowProvenance {
        if !self.value_type_contains_borrow(expected) {
            return BorrowProvenance::default();
        }
        match expected {
            Ty::Borrow(kind, _) => self.direct_borrow_provenance(expr, *kind, state),
            _ => self.expr_provenance(expr, state),
        }
    }

    fn expr_provenance(&self, expr: &Expr, state: &MoveState) -> BorrowProvenance {
        if !self.value_type_contains_borrow(&expr.ty) {
            return BorrowProvenance::default();
        }
        if let Some(key_path) = self.key_path(expr) {
            if let Some(provenance) = state.provenances.get(&key_path).cloned() {
                return provenance;
            }
            if let Some(root_provenance) = state.provenances.get(&KeyPath::root(key_path.root)) {
                if !self.is_borrowed_type(&expr.ty) {
                    return root_provenance.clone();
                }
            }
            if self.is_borrowed_type(&expr.ty) {
                return BorrowProvenance::direct(self.key_path_borrow_info(
                    &key_path,
                    expr,
                    &state.borrows,
                ));
            }
            return self.abstract_nested_provenance(&key_path, &expr.ty);
        }
        match &expr.kind {
            ExprKind::LiteralString(_) if self.is_borrowed_type(&expr.ty) => {
                BorrowProvenance::direct(BorrowInfo::new(BorrowOrigin::Static, None))
            }
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
                let mut provenance = BorrowProvenance::default();
                for item in items {
                    provenance.extend(self.expr_provenance(item, state));
                }
                provenance
            }
            ExprKind::RecordLiteral { fields, spread } => {
                let mut provenance = BorrowProvenance::default();
                if let Some(spread) = spread {
                    provenance.extend(self.expr_provenance(spread, state));
                }
                for field in fields {
                    provenance.extend(self.expr_provenance(&field.value, state));
                }
                provenance
            }
            ExprKind::Call { callee, args, .. } => self.call_provenance(callee, args, state),
            ExprKind::As(inner, _) => self.expr_provenance(inner, state),
            ExprKind::Block(block) => block_tail_expr(block)
                .map(|tail| self.expr_provenance(tail, state))
                .unwrap_or_default(),
            ExprKind::If(_, then_block, else_block) => {
                let mut provenance = BorrowProvenance::default();
                if let Some(tail) = block_tail_expr(then_block) {
                    provenance.extend(self.expr_provenance(tail, state));
                }
                if let Some(tail) = block_tail_expr(else_block) {
                    provenance.extend(self.expr_provenance(tail, state));
                }
                provenance
            }
            ExprKind::Member(Some(receiver), ..)
                if matches!(receiver.kind, ExprKind::Constructor(_)) =>
            {
                BorrowProvenance::default()
            }
            ExprKind::Member(None, ..) | ExprKind::Constructor(_) => BorrowProvenance::default(),
            ExprKind::Match(_, _) => BorrowProvenance::unknown(BorrowKind::Shared),
            _ => BorrowProvenance::unknown(BorrowKind::Shared),
        }
    }

    fn direct_borrow_provenance(
        &self,
        expr: &Expr,
        kind: BorrowKind,
        state: &MoveState,
    ) -> BorrowProvenance {
        if self.is_borrowed_type(&expr.ty) {
            let existing = self.expr_provenance(expr, state);
            if !existing.is_empty() {
                return existing.with_kind(kind);
            }
        }
        if let Some(key_path) = self.key_path(expr) {
            let owner = self.loan_owner_for_key_path(&key_path, state);
            return BorrowProvenance::direct(BorrowInfo::with_kind(
                self.origin_for_storage_borrow(&key_path, &expr.ty),
                Some(owner),
                kind,
            ));
        }
        if matches!(expr.kind, ExprKind::LiteralString(_)) {
            return BorrowProvenance::direct(BorrowInfo::with_kind(
                BorrowOrigin::Static,
                None,
                kind,
            ));
        }
        BorrowProvenance::unknown(kind)
    }

    fn call_provenance(
        &self,
        callee: &Expr,
        args: &[hir::CallArg],
        state: &MoveState,
    ) -> BorrowProvenance {
        let Some(ret) = self.call_return_type(callee) else {
            return BorrowProvenance::default();
        };
        if !self.value_type_contains_borrow(&ret) {
            return BorrowProvenance::default();
        }
        let params = self.call_argument_types(callee);
        if self.callee_is_type_constructor(callee) {
            return self.constructor_provenance(args, params.as_deref(), state);
        }
        if let ExprKind::Member(Some(receiver), ..) = &callee.kind {
            let mut provenance = BorrowProvenance::default();
            if let Some(self_param) = self.member_self_param(callee) {
                provenance.extend(self.expr_provenance_for_param(receiver, &self_param, state));
            }
            let value_params = self.member_value_params(callee).or(params);
            provenance.extend(self.input_provenance(args, value_params.as_deref(), state));
            if provenance.is_empty() {
                return BorrowProvenance::unknown(BorrowKind::Shared);
            }
            return provenance;
        }
        let provenance = self.input_provenance(args, params.as_deref(), state);
        if provenance.is_empty() {
            BorrowProvenance::unknown(BorrowKind::Shared)
        } else {
            provenance
        }
    }

    fn constructor_provenance(
        &self,
        args: &[hir::CallArg],
        params: Option<&[Ty]>,
        state: &MoveState,
    ) -> BorrowProvenance {
        let Some(params) = params else {
            let mut provenance = BorrowProvenance::default();
            for arg in args {
                provenance.extend(self.expr_provenance(&arg.value, state));
            }
            return provenance;
        };
        let mut provenance = BorrowProvenance::default();
        for (arg, param) in args.iter().zip(params) {
            provenance.extend(self.argument_provenance_for_param(arg, param, state));
        }
        provenance
    }

    fn input_provenance(
        &self,
        args: &[hir::CallArg],
        params: Option<&[Ty]>,
        state: &MoveState,
    ) -> BorrowProvenance {
        let Some(params) = params else {
            return BorrowProvenance::unknown(BorrowKind::Shared);
        };
        let mut provenance = BorrowProvenance::default();
        for (arg, param) in args.iter().zip(params) {
            provenance.extend(self.argument_provenance_for_param(arg, param, state));
        }
        provenance
    }

    fn argument_provenance_for_param(
        &self,
        arg: &hir::CallArg,
        param: &Ty,
        state: &MoveState,
    ) -> BorrowProvenance {
        self.expr_provenance_for_param(&arg.value, param, state)
    }

    fn expr_provenance_for_param(
        &self,
        expr: &Expr,
        param: &Ty,
        state: &MoveState,
    ) -> BorrowProvenance {
        match param {
            Ty::Borrow(kind, _) => self.direct_borrow_provenance(expr, *kind, state),
            _ if self.value_type_contains_borrow(param) => {
                self.provenance_for_expected_ty(param, expr, state)
            }
            _ => BorrowProvenance::default(),
        }
    }

    fn call_return_type(&self, callee: &Expr) -> Option<Ty> {
        let Ty::Func(_, ret, _) = &callee.ty else {
            return None;
        };
        Some((**ret).clone())
    }

    fn callee_is_type_constructor(&self, callee: &Expr) -> bool {
        matches!(
            callee.kind,
            ExprKind::Constructor(_) | ExprKind::Member(None, ..)
        ) || matches!(
            &callee.kind,
            ExprKind::Member(Some(receiver), ..) if matches!(receiver.kind, ExprKind::Constructor(_))
        )
    }

    fn abstract_nested_provenance(&self, key_path: &KeyPath, ty: &Ty) -> BorrowProvenance {
        if !self.value_type_contains_borrow(ty) {
            return BorrowProvenance::default();
        }
        BorrowProvenance::direct(BorrowInfo::new(
            self.origin_for_nested_borrow(key_path),
            None,
        ))
    }

    fn origin_for_nested_borrow(&self, key_path: &KeyPath) -> BorrowOrigin {
        match key_path.root {
            Symbol::ParamLocal(_) => BorrowOrigin::BorrowedParam,
            Symbol::Global(_) => BorrowOrigin::Static,
            Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_) => BorrowOrigin::Unknown,
            _ => BorrowOrigin::Unknown,
        }
    }

    fn origin_for_storage_borrow(&self, key_path: &KeyPath, expr_ty: &Ty) -> BorrowOrigin {
        match key_path.root {
            Symbol::ParamLocal(_) => {
                if self
                    .symbol_ty(key_path.root)
                    .is_some_and(|ty| self.is_borrowed_type(ty))
                    || self.is_borrowed_type(expr_ty)
                {
                    BorrowOrigin::BorrowedParam
                } else {
                    BorrowOrigin::OwnedParam
                }
            }
            Symbol::Global(_) => BorrowOrigin::Static,
            Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_) => BorrowOrigin::Local,
            _ => BorrowOrigin::Unknown,
        }
    }

    fn validate_local_provenance(&mut self, id: NodeID, ty: &Ty, provenance: &BorrowProvenance) {
        if provenance.is_empty() {
            return;
        }
        if provenance.has_unknown() && !self.allows_unknown_local_borrow_ty(ty) {
            self.error(
                id,
                OwnershipError::UnknownBorrowProvenance {
                    ty: ty.render_mono(),
                },
            );
        }
    }

    fn validate_return_provenance(&mut self, id: NodeID, ty: &Ty, provenance: &BorrowProvenance) {
        if provenance.is_empty() {
            return;
        }
        if provenance.has_unknown() {
            self.error(
                id,
                OwnershipError::UnknownBorrowProvenance {
                    ty: ty.render_mono(),
                },
            );
        } else if provenance.has_function_owned() {
            self.error(
                id,
                OwnershipError::ReturningLocalBorrow {
                    ty: ty.render_mono(),
                },
            );
        }
    }

    fn allows_unknown_local_borrow_ty(&self, ty: &Ty) -> bool {
        let Ty::Borrow(_, inner) = ty else {
            return false;
        };
        self.is_copy_type(inner)
    }

    fn borrow_info(&self, expr: &Expr, env: &BorrowEnv) -> BorrowInfo {
        match &expr.kind {
            ExprKind::Variable(name) => match name.symbol() {
                Ok(symbol) => self.symbol_borrow_info(symbol, env, expr),
                Err(_) => BorrowInfo::new(BorrowOrigin::Unknown, None),
            },
            ExprKind::LiteralString(_) => BorrowInfo::new(BorrowOrigin::Static, None),
            ExprKind::Member(Some(_), ..) if let Some(owner) = self.key_path(expr) => {
                self.key_path_borrow_info(&owner, expr, env)
            }
            ExprKind::Call { callee, args, .. } => self.call_borrow_info(callee, args, env),
            _ => BorrowInfo::new(BorrowOrigin::Unknown, None),
        }
    }

    fn call_borrow_info(
        &self,
        callee: &Expr,
        args: &[hir::CallArg],
        env: &BorrowEnv,
    ) -> BorrowInfo {
        if !self.call_returns_borrowed(callee) {
            return BorrowInfo::new(BorrowOrigin::Unknown, None);
        }
        if let ExprKind::Member(Some(receiver), ..) = &callee.kind {
            return self.receiver_borrow_info(receiver, env);
        }
        if matches!(callee.kind, ExprKind::Constructor(_)) {
            return self.single_constructor_borrow_source_info(args, env);
        }
        let params = self.call_argument_types(callee);
        self.single_borrowed_input_info(args, params.as_deref(), env)
    }

    fn call_returns_borrowed(&self, callee: &Expr) -> bool {
        let Ty::Func(_, ret, _) = &callee.ty else {
            return false;
        };
        self.value_type_contains_borrow(ret)
    }

    fn call_constructs_borrowed_value(&self, callee: &Expr) -> bool {
        self.callee_is_type_constructor(callee) && self.call_returns_borrowed(callee)
    }

    fn receiver_borrow_info(&self, receiver: &Expr, env: &BorrowEnv) -> BorrowInfo {
        match &receiver.kind {
            ExprKind::Variable(name) => match name.symbol() {
                Ok(symbol) => self.borrow_info_with_default_owner(
                    self.symbol_borrow_info(symbol, env, receiver),
                    receiver,
                ),
                Err(_) => BorrowInfo::new(BorrowOrigin::Unknown, None),
            },
            ExprKind::LiteralString(_) => BorrowInfo::new(BorrowOrigin::Static, None),
            _ if let Some(owner) = self.key_path(receiver) => self.borrow_info_with_default_owner(
                self.key_path_borrow_info(&owner, receiver, env),
                receiver,
            ),
            _ if self.expr_is_borrowed(receiver) => self.borrow_info(receiver, env),
            _ => BorrowInfo::new(BorrowOrigin::Unknown, None),
        }
    }

    fn borrow_info_with_default_owner(&self, info: BorrowInfo, expr: &Expr) -> BorrowInfo {
        if info.origin.can_have_owner() {
            BorrowInfo::with_kind(
                info.origin,
                info.owner.or_else(|| self.key_path(expr)),
                BorrowKind::Shared,
            )
        } else {
            info
        }
    }

    fn single_borrowed_input_info(
        &self,
        args: &[hir::CallArg],
        params: Option<&[Ty]>,
        env: &BorrowEnv,
    ) -> BorrowInfo {
        let Some(params) = params else {
            return BorrowInfo::new(BorrowOrigin::Unknown, None);
        };
        self.single_selected_argument_borrow_info(
            args.iter()
                .zip(params)
                .filter_map(|(arg, param)| self.is_borrowed_type(param).then_some(arg)),
            env,
        )
    }

    fn single_constructor_borrow_source_info(
        &self,
        args: &[hir::CallArg],
        env: &BorrowEnv,
    ) -> BorrowInfo {
        self.single_selected_argument_borrow_info(
            args.iter()
                .filter(|arg| self.expr_is_borrowed(&arg.value) || self.expr_is_owned(&arg.value)),
            env,
        )
    }

    fn single_selected_argument_borrow_info<'expr>(
        &self,
        args: impl IntoIterator<Item = &'expr hir::CallArg>,
        env: &BorrowEnv,
    ) -> BorrowInfo {
        let mut result: Option<BorrowInfo> = None;
        for arg in args {
            let info =
                self.borrow_info_with_default_owner(self.borrow_info(&arg.value, env), &arg.value);
            if result.is_some() {
                return BorrowInfo::new(BorrowOrigin::Unknown, None);
            }
            result = Some(info);
        }
        result.unwrap_or_else(|| BorrowInfo::new(BorrowOrigin::Unknown, None))
    }

    fn key_path_borrow_info(&self, key_path: &KeyPath, expr: &Expr, env: &BorrowEnv) -> BorrowInfo {
        if let Some(info) = env.get(key_path).cloned() {
            return info;
        }
        let origin = match key_path.root {
            Symbol::ParamLocal(_) => self.param_origin(key_path.root, expr),
            Symbol::Global(_) => BorrowOrigin::Static,
            Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_) => BorrowOrigin::Local,
            _ => BorrowOrigin::Unknown,
        };
        if origin.can_have_owner()
            && (self.is_borrowed_type(&expr.ty) || self.is_owned_type(&expr.ty))
        {
            BorrowInfo::new(origin, Some(key_path.clone()))
        } else {
            BorrowInfo::new(origin, None)
        }
    }

    fn symbol_borrow_info(&self, symbol: Symbol, env: &BorrowEnv, expr: &Expr) -> BorrowInfo {
        let key_path = KeyPath::root(symbol);
        if let Some(info) = env.get(&key_path).cloned() {
            return info;
        }
        match symbol {
            Symbol::ParamLocal(_) => BorrowInfo::new(self.param_origin(symbol, expr), None),
            Symbol::Global(_) => BorrowInfo::new(BorrowOrigin::Static, None),
            Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_) => {
                if self.is_borrowed_type(&expr.ty) || self.is_owned_type(&expr.ty) {
                    BorrowInfo::new(BorrowOrigin::Local, Some(key_path))
                } else {
                    BorrowInfo::new(BorrowOrigin::Unknown, None)
                }
            }
            _ => BorrowInfo::new(BorrowOrigin::Unknown, None),
        }
    }

    fn param_origin(&self, symbol: Symbol, expr: &Expr) -> BorrowOrigin {
        let root_ty = root_expr(expr).map(|root| &root.ty);
        let symbol_ty = self.symbol_ty(symbol);
        let expr_ty = Some(&expr.ty);
        if root_ty
            .into_iter()
            .chain(symbol_ty)
            .chain(expr_ty)
            .any(|ty| self.is_borrowed_type(ty))
        {
            BorrowOrigin::BorrowedParam
        } else {
            BorrowOrigin::OwnedParam
        }
    }

    fn contains_borrowed_type(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Borrow(_, _) => true,
            Ty::Nominal(symbol, args) => {
                self.is_borrowed_symbol(*symbol)
                    || args.iter().any(|arg| self.contains_borrowed_type(arg))
            }
            Ty::Tuple(items) => items.iter().any(|item| self.contains_borrowed_type(item)),
            Ty::Record(row) => self.row_contains_borrowed(row),
            Ty::Func(params, ret, _) => {
                params
                    .iter()
                    .any(|param| self.contains_borrowed_type(param))
                    || self.contains_borrowed_type(ret)
            }
            Ty::Any { assoc, .. } => assoc
                .iter()
                .any(|(_, assoc_ty)| self.contains_borrowed_type(assoc_ty)),
            Ty::Proj(base, ..) => self.contains_borrowed_type(base),
            Ty::Var(_) | Ty::Param(_) | Ty::Error => false,
        }
    }

    fn expr_mentions_raw_pointer(&self, expr: &Expr) -> bool {
        if self.type_mentions_raw_ptr(&expr.ty) {
            return true;
        }
        match &expr.kind {
            ExprKind::InlineIR(instruction) => instruction
                .binds
                .iter()
                .any(|operand| self.expr_mentions_raw_pointer(operand)),
            ExprKind::As(inner, _) => self.expr_mentions_raw_pointer(inner),
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => items
                .iter()
                .any(|item| self.expr_mentions_raw_pointer(item)),
            ExprKind::Block(block) => {
                block_tail_expr(block).is_some_and(|tail| self.expr_mentions_raw_pointer(tail))
            }
            ExprKind::Call {
                callee,
                args,
                trailing_block,
                ..
            } => {
                self.expr_mentions_raw_pointer(callee)
                    || args
                        .iter()
                        .any(|arg| self.expr_mentions_raw_pointer(&arg.value))
                    || trailing_block
                        .as_ref()
                        .and_then(block_tail_expr)
                        .is_some_and(|tail| self.expr_mentions_raw_pointer(tail))
            }
            ExprKind::CallEffect { args, .. } => args
                .iter()
                .any(|arg| self.expr_mentions_raw_pointer(&arg.value)),
            ExprKind::Member(Some(receiver), ..) => self.expr_mentions_raw_pointer(receiver),
            ExprKind::If(_, then_block, else_block) => {
                block_tail_expr(then_block).is_some_and(|tail| self.expr_mentions_raw_pointer(tail))
                    || block_tail_expr(else_block)
                        .is_some_and(|tail| self.expr_mentions_raw_pointer(tail))
            }
            ExprKind::Match(scrutinee, arms) => {
                self.expr_mentions_raw_pointer(scrutinee)
                    || arms.iter().any(|arm| {
                        block_tail_expr(&arm.body)
                            .is_some_and(|tail| self.expr_mentions_raw_pointer(tail))
                    })
            }
            ExprKind::RecordLiteral { fields, spread } => {
                spread
                    .as_ref()
                    .is_some_and(|spread| self.expr_mentions_raw_pointer(spread))
                    || fields
                        .iter()
                        .any(|field| self.expr_mentions_raw_pointer(&field.value))
            }
            ExprKind::Func(_)
            | ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_)
            | ExprKind::Variable(_)
            | ExprKind::Constructor(_)
            | ExprKind::RowVariable(_)
            | ExprKind::Member(None, ..) => false,
        }
    }

    fn type_mentions_raw_ptr(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Nominal(symbol, args) => {
                *symbol == Symbol::RawPtr || args.iter().any(|arg| self.type_mentions_raw_ptr(arg))
            }
            Ty::Borrow(_, inner) => self.type_mentions_raw_ptr(inner),
            Ty::Tuple(items) => items.iter().any(|item| self.type_mentions_raw_ptr(item)),
            Ty::Record(row) => row
                .fields
                .iter()
                .any(|(_, field_ty)| self.type_mentions_raw_ptr(field_ty)),
            Ty::Func(params, ret, _) => {
                params.iter().any(|param| self.type_mentions_raw_ptr(param))
                    || self.type_mentions_raw_ptr(ret)
            }
            Ty::Any { assoc, .. } => assoc
                .iter()
                .any(|(_, assoc_ty)| self.type_mentions_raw_ptr(assoc_ty)),
            Ty::Proj(base, ..) => self.type_mentions_raw_ptr(base),
            Ty::Var(_) | Ty::Param(_) | Ty::Error => false,
        }
    }

    fn row_contains_borrowed(&self, row: &Row) -> bool {
        row.fields
            .iter()
            .any(|(_, field_ty)| self.contains_borrowed_type(field_ty))
    }

    fn type_contains_param(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Param(_) => true,
            Ty::Borrow(_, inner) => self.type_contains_param(inner),
            Ty::Nominal(_, args) => args.iter().any(|arg| self.type_contains_param(arg)),
            Ty::Tuple(items) => items.iter().any(|item| self.type_contains_param(item)),
            Ty::Record(row) => self.row_contains_param(row),
            Ty::Func(params, ret, _) => {
                params.iter().any(|param| self.type_contains_param(param))
                    || self.type_contains_param(ret)
            }
            Ty::Any { assoc, .. } => assoc
                .iter()
                .any(|(_, assoc_ty)| self.type_contains_param(assoc_ty)),
            Ty::Proj(base, ..) => self.type_contains_param(base),
            Ty::Var(_) | Ty::Error => false,
        }
    }

    fn row_contains_param(&self, row: &Row) -> bool {
        row.tail
            .as_ref()
            .is_some_and(|tail| matches!(tail, crate::types::ty::RowTail::Param(_)))
            || row
                .fields
                .iter()
                .any(|(_, field_ty)| self.type_contains_param(field_ty))
    }

    fn is_borrowed_type(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Borrow(..))
            || matches!(ty, Ty::Nominal(symbol, _) if self.is_borrowed_symbol(*symbol))
    }

    fn is_borrowed_symbol(&self, symbol: Symbol) -> bool {
        self.output.borrowed_types.contains(&symbol)
    }

    fn is_owned_type(&self, ty: &Ty) -> bool {
        self.needs_drop_type(ty)
    }

    fn needs_drop_type(&self, ty: &Ty) -> bool {
        self.type_contains_owned(ty, &mut FxHashSet::default())
    }

    fn type_contains_owned(&self, ty: &Ty, visiting: &mut FxHashSet<Symbol>) -> bool {
        match ty {
            Ty::Borrow(_, _) => false,
            Ty::Nominal(symbol, args) => {
                if self.is_borrowed_symbol(*symbol) {
                    false
                } else {
                    self.output.owned_types.contains(symbol)
                        || self.symbol_has_ability(*symbol, MarkerAbility::Owner)
                        || self.nominal_contains_owned(*symbol, args, visiting)
                }
            }
            Ty::Tuple(items) => items
                .iter()
                .any(|item| self.type_contains_owned(item, visiting)),
            Ty::Record(row) => row
                .fields
                .iter()
                .any(|(_, field_ty)| self.type_contains_owned(field_ty, visiting)),
            Ty::Any { .. } => true,
            Ty::Func(..) | Ty::Proj(..) | Ty::Var(_) | Ty::Param(_) | Ty::Error => false,
        }
    }

    fn nominal_contains_owned(
        &self,
        symbol: Symbol,
        args: &[Ty],
        visiting: &mut FxHashSet<Symbol>,
    ) -> bool {
        if !visiting.insert(symbol) {
            return false;
        }
        let result = self.struct_contains_owned(symbol, args, visiting)
            || self.enum_contains_owned(symbol, args, visiting);
        visiting.remove(&symbol);
        result
    }

    fn struct_contains_owned(
        &self,
        symbol: Symbol,
        args: &[Ty],
        visiting: &mut FxHashSet<Symbol>,
    ) -> bool {
        let Some(info) = self.types.catalog.structs.get(&symbol) else {
            return false;
        };
        let substitution = type_param_subst(&info.params, args);
        info.fields.values().any(|(_, field_ty)| {
            let field_ty =
                field_ty.substitute(&substitution, &Default::default(), &Default::default());
            self.type_contains_owned(&field_ty, visiting)
        })
    }

    fn enum_contains_owned(
        &self,
        symbol: Symbol,
        args: &[Ty],
        visiting: &mut FxHashSet<Symbol>,
    ) -> bool {
        let Some(info) = self.types.catalog.enums.get(&symbol) else {
            return false;
        };
        let substitution = type_param_subst(&info.params, args);
        info.variants.values().any(|variant| {
            variant.argument_types().iter().any(|payload_ty| {
                let payload_ty =
                    payload_ty.substitute(&substitution, &Default::default(), &Default::default());
                self.type_contains_owned(&payload_ty, visiting)
            })
        })
    }

    fn is_copy_type(&self, ty: &Ty) -> bool {
        self.type_is_copy(ty, &mut FxHashSet::default())
    }

    fn type_is_copy(&self, ty: &Ty, visiting: &mut FxHashSet<Symbol>) -> bool {
        match ty {
            Ty::Borrow(_, _) => true,
            Ty::Nominal(symbol, args) => {
                self.is_borrowed_symbol(*symbol)
                    || (!self.type_contains_owned(ty, &mut FxHashSet::default())
                        && self.nominal_is_copy(*symbol, args, visiting))
            }
            Ty::Tuple(items) => items.iter().all(|item| self.type_is_copy(item, visiting)),
            Ty::Record(row) => row
                .fields
                .iter()
                .all(|(_, field_ty)| self.type_is_copy(field_ty, visiting)),
            Ty::Func(..) => true,
            Ty::Any { .. } => false,
            Ty::Proj(..) | Ty::Var(_) | Ty::Param(_) | Ty::Error => false,
        }
    }

    fn nominal_is_copy(
        &self,
        symbol: Symbol,
        args: &[Ty],
        visiting: &mut FxHashSet<Symbol>,
    ) -> bool {
        if matches!(
            symbol,
            Symbol::Int | Symbol::Float | Symbol::Bool | Symbol::Void | Symbol::Never
        ) {
            return true;
        }
        if symbol == Symbol::RawPtr || symbol == Symbol::Byte {
            return true;
        }
        if !visiting.insert(symbol) {
            return true;
        }
        let result = self.struct_is_copy(symbol, args, visiting)
            || self.enum_is_copy(symbol, args, visiting);
        visiting.remove(&symbol);
        result
    }

    fn struct_is_copy(
        &self,
        symbol: Symbol,
        args: &[Ty],
        visiting: &mut FxHashSet<Symbol>,
    ) -> bool {
        let Some(info) = self.types.catalog.structs.get(&symbol) else {
            return false;
        };
        let substitution = type_param_subst(&info.params, args);
        info.fields.values().all(|(_, field_ty)| {
            let field_ty =
                field_ty.substitute(&substitution, &Default::default(), &Default::default());
            self.type_is_copy(&field_ty, visiting)
        })
    }

    fn enum_is_copy(&self, symbol: Symbol, args: &[Ty], visiting: &mut FxHashSet<Symbol>) -> bool {
        let Some(info) = self.types.catalog.enums.get(&symbol) else {
            return false;
        };
        let substitution = type_param_subst(&info.params, args);
        info.variants.values().all(|variant| {
            variant.argument_types().iter().all(|payload_ty| {
                let payload_ty =
                    payload_ty.substitute(&substitution, &Default::default(), &Default::default());
                self.type_is_copy(&payload_ty, visiting)
            })
        })
    }

    fn symbol_has_ability(&self, symbol: Symbol, ability: MarkerAbility) -> bool {
        let protocol = ability.protocol();
        if !self.types.catalog.protocols.contains_key(&protocol) {
            return false;
        }
        self.types
            .catalog
            .conformances_by_head
            .get(&symbol)
            .is_some_and(|protocols| {
                protocols.iter().any(|candidate| {
                    self.types
                        .catalog
                        .protocol_and_supers(*candidate)
                        .contains(&protocol)
                })
            })
    }

    fn symbol_name(&self, symbol: Symbol) -> Option<String> {
        self.types
            .display_names
            .get(&symbol)
            .or_else(|| self.resolved.symbol_names.get(&symbol))
            .cloned()
    }

    fn render_symbol(&self, symbol: Symbol) -> String {
        self.symbol_name(symbol)
            .unwrap_or_else(|| symbol.to_string())
    }

    fn render_key_path(&self, key_path: &KeyPath) -> String {
        let mut rendered = self.render_symbol(key_path.root);
        for field in &key_path.fields {
            rendered.push('.');
            rendered.push_str(&self.render_symbol(*field));
        }
        rendered
    }

    fn render_expr_path(&self, expr: &Expr) -> Option<String> {
        match &expr.kind {
            ExprKind::Variable(name) => name.symbol().ok().map(|symbol| self.render_symbol(symbol)),
            ExprKind::Member(Some(receiver), label) => {
                Some(format!("{}.{}", self.render_expr_path(receiver)?, label))
            }
            _ => None,
        }
    }

    fn error(&mut self, id: NodeID, kind: OwnershipError) {
        if !self.reported.insert((id, kind.clone())) {
            return;
        }
        self.diagnostics.push(AnyDiagnostic::Ownership(Diagnostic {
            id,
            severity: Severity::Error,
            kind,
        }));
    }
}

fn is_local_or_param(symbol: Symbol) -> bool {
    matches!(
        symbol,
        Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_) | Symbol::ParamLocal(_)
    )
}

fn root_expr(expr: &Expr) -> Option<&Expr> {
    match &expr.kind {
        ExprKind::Variable(_) => Some(expr),
        ExprKind::Member(Some(receiver), ..) => root_expr(receiver),
        _ => None,
    }
}

fn source_allows_unsafe(source: &Source) -> bool {
    source
        .read()
        .is_ok_and(|text| text.lines().any(|line| line.trim() == "// unsafe"))
}

fn block_tail_expr(block: &Block) -> Option<&Expr> {
    block.body.last().and_then(node_tail_expr)
}

fn node_tail_expr(node: &Node) -> Option<&Expr> {
    match node {
        Node::Expr(expr) => Some(expr),
        Node::Stmt(stmt) => match &stmt.kind {
            StmtKind::Expr(expr) => Some(expr),
            _ => None,
        },
        _ => None,
    }
}

trait SourceVisitor {
    fn expr(&mut self, _expr: &Expr) {}
    fn inline_ir(&mut self, _id: NodeID) {}
    fn variable(&mut self, _symbol: Symbol) {}
    fn binder(&mut self, _symbol: Symbol) {}
    fn capture(&mut self, _symbol: Symbol) {}
}

struct InlineIrCollector<'a> {
    out: &'a mut FxHashSet<NodeID>,
}

impl SourceVisitor for InlineIrCollector<'_> {
    fn inline_ir(&mut self, id: NodeID) {
        self.out.insert(id);
    }
}

struct BinderCollector<'a> {
    out: &'a mut FxHashSet<Symbol>,
}

impl SourceVisitor for BinderCollector<'_> {
    fn binder(&mut self, symbol: Symbol) {
        self.out.insert(symbol);
    }
}

struct TypedExprCollector<'a> {
    out: &'a mut Vec<(NodeID, Ty)>,
}

impl SourceVisitor for TypedExprCollector<'_> {
    fn expr(&mut self, expr: &Expr) {
        self.out.push((expr.id, expr.ty.clone()));
    }
}

struct RootUseCollector<'a> {
    out: &'a mut FxHashSet<Symbol>,
}

impl SourceVisitor for RootUseCollector<'_> {
    fn variable(&mut self, symbol: Symbol) {
        self.out.insert(symbol);
    }

    fn capture(&mut self, symbol: Symbol) {
        self.out.insert(symbol);
    }
}

fn walk_nodes(nodes: &[Node], visitor: &mut impl SourceVisitor) {
    for node in nodes {
        walk_node(node, visitor);
    }
}

fn walk_node(node: &Node, visitor: &mut impl SourceVisitor) {
    match node {
        Node::Decl(decl) => walk_decl(decl, visitor),
        Node::Stmt(stmt) => walk_stmt(&stmt.kind, visitor),
        Node::Expr(expr) => walk_expr(expr, visitor),
    }
}

fn walk_decl(decl: &Decl, visitor: &mut impl SourceVisitor) {
    match &decl.kind {
        DeclKind::Let { lhs, rhs, .. } => {
            walk_pattern_binders(lhs, visitor);
            if let Some(rhs) = rhs {
                walk_expr(rhs, visitor);
            }
        }
        DeclKind::Func(func) => walk_block(&func.body, visitor),
        DeclKind::Method { func, .. } => walk_block(&func.body, visitor),
        DeclKind::Init { params, body, .. } => {
            for param in params {
                walk_parameter_binder(param, visitor);
            }
            walk_block(body, visitor);
        }
        DeclKind::Struct { body, .. }
        | DeclKind::Enum { body, .. }
        | DeclKind::Protocol { body, .. }
        | DeclKind::Extend { body, .. } => {
            for decl in &body.decls {
                walk_decl(decl, visitor);
            }
        }
        DeclKind::Import(_)
        | DeclKind::Effect { .. }
        | DeclKind::Property { .. }
        | DeclKind::Associated { .. }
        | DeclKind::EnumVariant { .. }
        | DeclKind::FuncSignature(_)
        | DeclKind::MethodRequirement { .. }
        | DeclKind::TypeAlias(..) => {}
    }
}

fn walk_block(block: &Block, visitor: &mut impl SourceVisitor) {
    for arg in &block.args {
        walk_parameter_binder(arg, visitor);
    }
    walk_nodes(&block.body, visitor);
}

fn walk_stmt(stmt: &StmtKind, visitor: &mut impl SourceVisitor) {
    match stmt {
        StmtKind::Expr(expr) | StmtKind::Return(Some(expr)) | StmtKind::Continue(Some(expr)) => {
            walk_expr(expr, visitor);
        }
        StmtKind::If(condition, then_block, else_block) => {
            walk_expr(condition, visitor);
            walk_block(then_block, visitor);
            if let Some(else_block) = else_block {
                walk_block(else_block, visitor);
            }
        }
        StmtKind::Assignment(lhs, rhs) => {
            walk_expr(lhs, visitor);
            walk_expr(rhs, visitor);
        }
        StmtKind::Loop(condition, body) => {
            if let Some(condition) = condition {
                walk_expr(condition, visitor);
            }
            walk_block(body, visitor);
        }
        StmtKind::Handling { body, .. } => walk_block(body, visitor),
        StmtKind::Return(None) | StmtKind::Continue(None) | StmtKind::Break => {}
    }
}

fn walk_expr(expr: &Expr, visitor: &mut impl SourceVisitor) {
    visitor.expr(expr);
    match &expr.kind {
        ExprKind::InlineIR(_) => visitor.inline_ir(expr.id),
        ExprKind::Variable(name) => {
            if let Ok(symbol) = name.symbol() {
                visitor.variable(symbol);
            }
        }
        ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
            for item in items {
                walk_expr(item, visitor);
            }
        }
        ExprKind::As(inner, _) => walk_expr(inner, visitor),
        ExprKind::Block(block) => walk_block(block, visitor),
        ExprKind::Call {
            callee,
            args,
            trailing_block,
            ..
        } => {
            walk_expr(callee, visitor);
            for arg in args {
                walk_expr(&arg.value, visitor);
            }
            if let Some(block) = trailing_block {
                walk_block(block, visitor);
            }
        }
        ExprKind::CallEffect { args, .. } => {
            for arg in args {
                walk_expr(&arg.value, visitor);
            }
        }
        ExprKind::Member(Some(receiver), ..) => walk_expr(receiver, visitor),
        ExprKind::Func(func) => {
            for capture in &func.captures {
                if let Ok(symbol) = capture.name.symbol() {
                    visitor.capture(symbol);
                }
            }
            walk_block(&func.body, visitor);
        }
        ExprKind::If(condition, then_block, else_block) => {
            walk_expr(condition, visitor);
            walk_block(then_block, visitor);
            walk_block(else_block, visitor);
        }
        ExprKind::Match(scrutinee, arms) => {
            walk_expr(scrutinee, visitor);
            for arm in arms {
                walk_pattern_binders(&arm.pattern, visitor);
                walk_block(&arm.body, visitor);
            }
        }
        ExprKind::RecordLiteral { fields, spread } => {
            if let Some(spread) = spread {
                walk_expr(spread, visitor);
            }
            for field in fields {
                walk_expr(&field.value, visitor);
            }
        }
        ExprKind::LiteralInt(_)
        | ExprKind::LiteralFloat(_)
        | ExprKind::LiteralTrue
        | ExprKind::LiteralFalse
        | ExprKind::LiteralString(_)
        | ExprKind::Constructor(_)
        | ExprKind::RowVariable(_)
        | ExprKind::Member(None, ..) => {}
    }
}

fn walk_pattern_binders(pattern: &hir::Pattern, visitor: &mut impl SourceVisitor) {
    for (_, symbol) in pattern.collect_binders() {
        visitor.binder(symbol);
    }
}

fn walk_parameter_binder(param: &Parameter, visitor: &mut impl SourceVisitor) {
    if let Ok(symbol) = param.name.symbol() {
        visitor.binder(symbol);
    }
}

fn collect_block_binders(block: &Block, out: &mut FxHashSet<Symbol>) {
    let mut visitor = BinderCollector { out };
    walk_block(block, &mut visitor);
}

fn collect_inline_ir_exprs(nodes: &[Node], out: &mut FxHashSet<NodeID>) {
    let mut visitor = InlineIrCollector { out };
    walk_nodes(nodes, &mut visitor);
}

fn borrow_kind_name(kind: BorrowKind) -> &'static str {
    match kind {
        BorrowKind::Shared => "shared",
        BorrowKind::Mutable => "mutable",
    }
}

fn capture_mode_name(mode: CaptureMode) -> &'static str {
    match mode {
        CaptureMode::Copy => "copy",
        CaptureMode::Move => "consuming",
        CaptureMode::BorrowShared => "&",
        CaptureMode::BorrowMut => "&mut",
    }
}

fn type_param_subst(params: &[Symbol], args: &[Ty]) -> FxHashMap<Symbol, Ty> {
    params.iter().copied().zip(args.iter().cloned()).collect()
}

fn nominal_params(types: &TypeOutput, symbol: Symbol) -> Vec<Ty> {
    types
        .catalog
        .structs
        .get(&symbol)
        .map(|info| &info.params)
        .or_else(|| types.catalog.enums.get(&symbol).map(|info| &info.params))
        .into_iter()
        .flatten()
        .copied()
        .map(Ty::Param)
        .collect()
}

fn func_params(ty: &Ty) -> Option<Vec<Ty>> {
    let Ty::Func(params, _, _) = ty else {
        return None;
    };
    Some(params.clone())
}

fn source_node_for_mir_statement(statement: &mir::Statement) -> Option<NodeID> {
    match statement {
        mir::Statement::ScopeEnter { .. } | mir::Statement::ScopeExit { .. } => None,
        mir::Statement::StorageLive { id, .. }
        | mir::Statement::StorageDead { id, .. }
        | mir::Statement::AssignmentRootUse { id, .. } => Some(*id),
        mir::Statement::Read { expr }
        | mir::Statement::ConsumeValue { expr, .. }
        | mir::Statement::ReturnValue { expr, .. }
        | mir::Statement::ContinueValue { expr, .. } => Some(expr.id),
        mir::Statement::Bind {
            lhs,
            type_annotation,
            rhs,
            ..
        } => rhs
            .as_ref()
            .map(|expr| expr.id)
            .or_else(|| type_annotation.as_ref().map(|annotation| annotation.id))
            .or(Some(lhs.id)),
        mir::Statement::Assign { lhs, .. } => Some(lhs.id),
        mir::Statement::DropCandidate { target, .. } => drop_target_node(target),
        mir::Statement::Call { callee, .. } => Some(callee.id),
        mir::Statement::Perform => None,
        mir::Statement::Function { body, .. } => Some(body.id),
        mir::Statement::Handling { stmt, .. } => Some(stmt.id),
        mir::Statement::DeclBody { body } => Some(body.id),
    }
}

fn drop_target_node(target: &mir::DropTarget) -> Option<NodeID> {
    match target {
        mir::DropTarget::Symbol { id, .. } => Some(*id),
        mir::DropTarget::Expr(expr) => Some(expr.id),
    }
}

fn point_kind(statement: &mir::Statement) -> PointKind {
    match statement {
        mir::Statement::ScopeEnter { .. } => PointKind::ScopeEnter,
        mir::Statement::ScopeExit { .. } => PointKind::ScopeExit,
        mir::Statement::StorageLive { .. } => PointKind::StorageLive,
        mir::Statement::StorageDead { .. } => PointKind::StorageDead,
        mir::Statement::Read { .. } => PointKind::Read,
        mir::Statement::ConsumeValue { .. } => PointKind::ConsumeValue,
        mir::Statement::AssignmentRootUse { .. } => PointKind::AssignmentRootUse,
        mir::Statement::Bind { .. } => PointKind::Bind,
        mir::Statement::Assign { .. } => PointKind::Assign,
        mir::Statement::DropCandidate { .. } => PointKind::DropCandidate,
        mir::Statement::Call { .. } => PointKind::Call,
        mir::Statement::Perform => PointKind::Perform,
        mir::Statement::ReturnValue { .. } => PointKind::ReturnValue,
        mir::Statement::ContinueValue { .. } => PointKind::ContinueValue,
        mir::Statement::Function { .. } => PointKind::Function,
        mir::Statement::Handling { .. } => PointKind::Handling,
        mir::Statement::DeclBody { .. } => PointKind::DeclBody,
    }
}

fn terminator_successors(terminator: &mir::Terminator) -> Vec<mir::BlockId> {
    match terminator {
        mir::Terminator::Unset
        | mir::Terminator::Return
        | mir::Terminator::ReturnVoid
        | mir::Terminator::Break
        | mir::Terminator::Continue => vec![],
        mir::Terminator::Jump(target) => vec![*target],
        mir::Terminator::Branch {
            then_block,
            else_block,
            ..
        } => vec![*then_block, *else_block],
        mir::Terminator::Switch { arms, default, .. } => {
            let mut successors = arms.clone();
            successors.extend(default.iter().copied());
            successors
        }
        mir::Terminator::Loop {
            body_block,
            exit_block,
            ..
        } => vec![*body_block, *exit_block],
    }
}

#[derive(Default)]
struct BorrowUseDef {
    uses: FxHashSet<Symbol>,
    defs: FxHashSet<Symbol>,
}

fn borrow_liveness(body: &mir::Body, live_at_exit: &FxHashSet<Symbol>) -> BorrowLiveness {
    let block_transfers: Vec<_> = body
        .blocks
        .iter()
        .map(|block| {
            let mut transfer = BorrowUseDef::default();
            let mut defined = FxHashSet::default();
            for statement in &block.statements {
                let statement_transfer = statement_borrow_use_def(&statement.kind);
                for symbol in statement_transfer.uses {
                    if !defined.contains(&symbol) {
                        transfer.uses.insert(symbol);
                    }
                }
                for symbol in statement_transfer.defs {
                    defined.insert(symbol);
                    transfer.defs.insert(symbol);
                }
            }
            transfer
        })
        .collect();

    let mut live_in = vec![FxHashSet::default(); body.blocks.len()];
    let mut live_out = vec![FxHashSet::default(); body.blocks.len()];

    loop {
        let mut changed = false;
        for block_index in (0..body.blocks.len()).rev() {
            let successors = terminator_successors(&body.blocks[block_index].terminator);
            let mut next_out = FxHashSet::default();
            if successors.is_empty() {
                next_out.extend(live_at_exit.iter().copied());
            } else {
                for successor in successors {
                    next_out.extend(live_in[successor.0].iter().copied());
                }
            }

            let mut next_in = block_transfers[block_index].uses.clone();
            for symbol in &next_out {
                if !block_transfers[block_index].defs.contains(symbol) {
                    next_in.insert(*symbol);
                }
            }

            if live_in[block_index] != next_in || live_out[block_index] != next_out {
                live_in[block_index] = next_in;
                live_out[block_index] = next_out;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut live_out_by_point = FxHashMap::default();
    for (block_index, block) in body.blocks.iter().enumerate() {
        let mut live = live_out[block_index].clone();
        for statement in block.statements.iter().rev() {
            live_out_by_point.insert(statement.point.0, live.clone());
            let transfer = statement_borrow_use_def(&statement.kind);
            for symbol in transfer.defs {
                live.remove(&symbol);
            }
            live.extend(transfer.uses);
        }
    }

    BorrowLiveness { live_out_by_point }
}

fn statement_borrow_use_def(statement: &mir::Statement) -> BorrowUseDef {
    let mut transfer = BorrowUseDef::default();
    match statement {
        mir::Statement::Read { expr }
        | mir::Statement::ConsumeValue { expr, .. }
        | mir::Statement::ReturnValue { expr, .. }
        | mir::Statement::ContinueValue { expr, .. } => {
            collect_expr_root_uses(expr, &mut transfer.uses);
        }
        mir::Statement::AssignmentRootUse { symbol, .. } => {
            transfer.uses.insert(*symbol);
        }
        mir::Statement::Bind { lhs, rhs, .. } => {
            if let Some(rhs) = rhs {
                collect_expr_root_uses(rhs, &mut transfer.uses);
            }
            for (_, symbol) in lhs.collect_binders() {
                transfer.defs.insert(symbol);
            }
        }
        mir::Statement::Assign {
            lhs, rhs, target, ..
        } => {
            collect_expr_root_uses(rhs, &mut transfer.uses);
            if let Some(symbol) = assignment_root_def(lhs, target.as_ref()) {
                transfer.defs.insert(symbol);
            }
        }
        mir::Statement::Call {
            callee,
            args,
            trailing_block,
            ..
        } => {
            collect_expr_root_uses(callee, &mut transfer.uses);
            for arg in args {
                collect_expr_root_uses(&arg.value, &mut transfer.uses);
            }
            if let Some(block) = trailing_block {
                collect_block_root_uses(block, &mut transfer.uses);
            }
        }
        mir::Statement::Function { captures, body, .. } => {
            for capture in captures {
                if let Ok(symbol) = capture.name.symbol() {
                    transfer.uses.insert(symbol);
                }
            }
            collect_block_root_uses(body, &mut transfer.uses);
        }
        mir::Statement::Handling { body, .. } => {
            collect_block_root_uses(body, &mut transfer.uses);
        }
        mir::Statement::StorageDead { symbol, .. } => {
            transfer.defs.insert(*symbol);
        }
        mir::Statement::ScopeEnter { .. }
        | mir::Statement::ScopeExit { .. }
        | mir::Statement::StorageLive { .. }
        | mir::Statement::DropCandidate { .. }
        | mir::Statement::Perform
        | mir::Statement::DeclBody { .. } => {}
    }
    transfer
}

fn assignment_root_def(lhs: &Expr, target: Option<&mir::KeyPath>) -> Option<Symbol> {
    if let Some(target) = target
        && !target.components.is_empty()
    {
        return None;
    }
    match &lhs.kind {
        ExprKind::Variable(name) => name.symbol().ok(),
        _ => None,
    }
}

fn collect_block_root_uses(block: &Block, out: &mut FxHashSet<Symbol>) {
    let mut visitor = RootUseCollector { out };
    walk_block(block, &mut visitor);
}

fn collect_expr_root_uses(expr: &Expr, out: &mut FxHashSet<Symbol>) {
    let mut visitor = RootUseCollector { out };
    walk_expr(expr, &mut visitor);
}

fn classify_drop(key_path: &KeyPath, state: &DropState) -> mir::DropElaboration {
    if state.moved_all.keys().any(|moved| moved == key_path) {
        return mir::DropElaboration::Dead;
    }
    if state
        .moved_any
        .keys()
        .any(|moved| key_path.contains(moved) && moved != key_path)
    {
        return mir::DropElaboration::Open;
    }
    if state
        .initialized_all
        .iter()
        .any(|live| live.contains(key_path))
        && !state.moved_any.keys().any(|moved| moved == key_path)
    {
        mir::DropElaboration::Static
    } else if state
        .initialized_any
        .iter()
        .any(|live| live.contains(key_path))
    {
        mir::DropElaboration::Conditional
    } else {
        mir::DropElaboration::Dead
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        compiling::driver::{Driver, DriverConfig, Source},
        diagnostic::AnyDiagnostic,
        mir::{DropElaboration, DropReason},
        name_resolution::symbol::Symbol,
        ownership::{BodyCacheKey, BodyKind, OwnershipOutput, PointKind},
    };
    use rustc_hash::{FxHashMap, FxHashSet};

    fn ownership_errors(source: &str) -> Vec<String> {
        diagnostics(source)
            .into_iter()
            .filter(|(kind, _)| *kind == "ownership")
            .map(|(_, message)| message)
            .collect()
    }

    fn diagnostics(source: &str) -> Vec<(&'static str, String)> {
        let typed = Driver::new(
            vec![Source::from(source)],
            DriverConfig::new("OwnershipTest"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
        typed
            .phase
            .diagnostics
            .iter()
            .map(|diagnostic| match diagnostic {
                AnyDiagnostic::Ownership(diagnostic) => ("ownership", diagnostic.kind.to_string()),
                _ => ("other", diagnostic.to_string()),
            })
            .collect()
    }

    fn ownership_output(source: &str) -> (OwnershipOutput, FxHashMap<Symbol, String>) {
        let typed = Driver::new(
            vec![Source::from(source)],
            DriverConfig::new("OwnershipTest"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
        assert!(
            !typed.has_errors(),
            "unexpected diagnostics: {:?}",
            typed.diagnostics()
        );
        // The ownership pass elaborated the drop/move facts (`drop_plan` + `facts.moves`) once,
        // for both the editor and lowering — no second walk needed.
        (typed.phase.ownership, typed.phase.types.display_names)
    }

    #[test]
    fn ownership_pass_elaborates_and_persists_each_body_once() {
        // The MIR is built and its drops elaborated exactly once, in the ownership pass: the
        // node-keyed facts the editor reads (`drop_plan` + `facts.moves`) and the per-statement
        // results lowering reads (`statement.ownership`) come from that single elaboration, and
        // the elaborated body is persisted in `mir_bodies` so lowering reuses it instead of
        // rebuilding the MIR.
        let source = "
            func make() -> Int {
                let s = \"hello\" + \" world\"
                let pair = (s, 1)
                0
            }
            ";
        let typed = Driver::new(
            vec![Source::from(source)],
            DriverConfig::new("OwnershipTest"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
        assert!(
            !typed.has_errors(),
            "unexpected diagnostics: {:?}",
            typed.diagnostics()
        );

        let ownership = &typed.phase.ownership;
        assert!(
            !ownership.drop_plan.obligations.is_empty(),
            "the ownership pass elaborates drops for the editor's hints"
        );
        assert!(
            !ownership.facts.moves.is_empty(),
            "the ownership pass records move facts for the editor's hints"
        );

        // The function body is persisted, and its drop result is projected onto a statement so
        // lowering reads it off the MIR rather than re-elaborating.
        let function_body = ownership
            .mir_bodies
            .iter()
            .find(|(key, _)| matches!(key, BodyCacheKey::Function { .. }))
            .map(|(_, body)| body)
            .expect("the function body is persisted for lowering to reuse");
        let has_projected_drop = function_body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .any(|statement| statement.ownership.drop.is_some());
        assert!(
            has_projected_drop,
            "the elaborated drop is projected onto the persisted body's statements"
        );
    }

    #[test]
    fn allows_borrowed_field_in_struct_type() {
        let errors = ownership_errors(
            "
            struct View {
                let path: Substring
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn allows_borrowed_payload_in_enum_type() {
        let errors = ownership_errors(
            "
            enum View {
                case path(Substring)
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn rejects_borrowed_global() {
        let errors = ownership_errors("let path = \"hello\".slice(0, 1)");
        assert!(
            errors
                .iter()
                .any(|error| error.contains("cannot be stored in global 'path'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_raw_pointer_usage_in_safe_source() {
        let errors = ownership_errors(
            "
            func bad() -> RawPtr {
                @_ir(1) { %? = alloc Byte $0 }
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Raw pointer type RawPtr")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_raw_core_function_in_safe_source() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let ptr = _alloc<Byte>(1)
                0
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Raw pointer type")),
            "{errors:?}"
        );
    }

    #[test]
    fn allows_raw_pointer_usage_in_unsafe_source() {
        let errors = ownership_errors(
            "// unsafe
            func bad() -> RawPtr {
                @_ir(1) { %? = alloc Byte $0 }
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn rejects_returning_substring_of_local_owned_value() {
        let errors = ownership_errors(
            "
            func bad() -> Substring {
                let s = \"hello\" + \" world\"
                s.slice(0, 1)
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("owned by this function")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_returning_substring_of_owned_parameter() {
        let errors = ownership_errors(
            "
            func first(s: String) -> Substring {
                s.slice(0, 1)
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("owned by this function")),
            "{errors:?}"
        );
    }

    #[test]
    fn allows_returning_substring_of_borrowed_parameter() {
        let errors = ownership_errors(
            "
            func first(s: &String) -> Substring {
                s.slice(0, 1)
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn ordinary_borrowed_return_tracks_single_borrowed_argument_owner() {
        let errors = ownership_errors(
            "
            func first(s: &String) -> Substring {
                s.slice(0, 1)
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let sub = first(s)
                let moved = s
                sub.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of borrowed value 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn ordinary_borrowed_return_from_owned_local_cannot_escape() {
        let errors = ownership_errors(
            "
            func first(s: &String) -> Substring {
                s.slice(0, 1)
            }

            func bad() -> Substring {
                let s = \"hello\" + \" world\"
                first(s)
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("owned by this function")),
            "{errors:?}"
        );
    }

    #[test]
    fn ordinary_borrowed_return_can_escape_borrowed_parameter() {
        let errors = ownership_errors(
            "
            func first(s: &String) -> Substring {
                s.slice(0, 1)
            }

            func ok(s: &String) -> Substring {
                first(s)
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn ambiguous_borrowed_return_provenance_is_rejected() {
        let errors = ownership_errors(
            "
            func choose(a: &String, b: &String) -> Substring {
                a.slice(0, 1)
            }

            func bad() -> Int {
                let a = \"hello\" + \" world\"
                let b = \"goodbye\" + \" world\"
                let sub = choose(a, b)
                sub.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("borrow provenance is unknown")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_returning_tuple_containing_local_borrow() {
        let errors = ownership_errors(
            "
            func bad() -> (Substring, Int) {
                let s = \"hello\" + \" world\"
                (s.slice(0, 1), 1)
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("owned by this function")),
            "{errors:?}"
        );
    }

    #[test]
    fn record_containing_borrow_tracks_owner_invalidation() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let record = { sub: s.slice(0, 1) }
                let moved = s
                record.sub.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot move 's' while it is borrowed as 'record'")),
            "{errors:?}"
        );
    }

    #[test]
    fn generic_container_containing_borrow_tracks_owner_invalidation() {
        let errors = ownership_errors(
            "
            enum Maybe<T> {
                case some(T)
                case none
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let maybe = Maybe.some(s.slice(0, 1))
                let moved = s
                match maybe {
                    .some(sub) -> sub.length,
                    .none -> 0
                }
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of borrowed value 'maybe'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_returning_owned_generic_container_containing_borrow() {
        let errors = ownership_errors(
            "
            enum Maybe<T> {
                case some(T)
                case none
            }

            func bad() -> Maybe<Substring> {
                let s = \"hello\" + \" world\"
                Maybe.some(s.slice(0, 1))
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("owned by this function")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_returning_owned_field_from_shared_borrow() {
        let errors = ownership_errors(
            "
            struct Person {
                let name: String
            }

            func bad(person: &Person) -> String {
                person.name
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("out of borrowed value 'person'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_binding_owned_field_from_shared_borrow() {
        let errors = ownership_errors(
            "
            struct Person {
                let name: String
            }

            func bad(person: &Person) -> Int {
                let name = person.name
                name.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("out of borrowed value 'person'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_passing_owned_field_from_shared_borrow_by_value() {
        let errors = ownership_errors(
            "
            struct Person {
                let name: String
            }

            func take(name: String) -> Int {
                name.length
            }

            func bad(person: &Person) -> Int {
                take(person.name)
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("out of borrowed value 'person'")),
            "{errors:?}"
        );
    }

    #[test]
    fn allows_copy_field_read_from_shared_borrow() {
        let errors = ownership_errors(
            "
            struct Person {
                let age: Int
            }

            func ok(person: &Person) -> Int {
                person.age
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn rejects_owned_field_extraction_from_borrowed_nominal() {
        let source = "
            func bad(sub: Substring) -> Int {
                let storage = sub.storage
                0
            }
            ";
        let errors = ownership_errors(source);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("out of borrowed value 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_use_after_simple_owned_move() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let t = s
                s.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn allows_copy_value_reuse_after_assignment() {
        let errors = ownership_errors(
            "
            func ok() -> Int {
                let x = 1
                let y = x
                x + y
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn allows_reassignment_after_owned_move() {
        let errors = ownership_errors(
            "
            func ok() -> Int {
                let s = \"hello\" + \" world\"
                let t = s
                s = \"new\" + \" value\"
                s.length
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn rejects_borrow_use_after_owner_move() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let sub = s.slice(0, 1)
                let moved = s
                sub.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of borrowed value 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_borrow_use_after_owner_reassignment() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let sub = s.slice(0, 1)
                s = \"new\" + \" value\"
                sub.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of borrowed value 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_reassigned_borrow_use_after_owner_move() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let sub = s.slice(0, 1)
                sub = s.slice(1, 1)
                let moved = s
                sub.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of borrowed value 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn allows_owner_move_after_borrow_last_use() {
        let errors = ownership_errors(
            "
            func ok() -> Int {
                let s = \"hello\" + \" world\"
                let sub = s.slice(0, 1)
                let n = sub.length
                let moved = s
                n
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn rejects_owner_move_while_borrow_has_later_use() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let sub = s.slice(0, 1)
                let moved = s
                sub.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot move 's' while it is borrowed as 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn move_while_mutably_borrowed_does_not_report_spurious_shared_borrow() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let borrow: &mut String = s
                let moved = s
                borrow.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot move 's' while it is borrowed as 'borrow'")),
            "{errors:?}"
        );
        assert!(
            !errors
                .iter()
                .any(|error| error.contains("Cannot take shared borrow")),
            "moving a value should not be reported as taking a shared borrow: {errors:?}"
        );
    }

    #[test]
    fn borrowed_call_argument_does_not_move_owned_value() {
        let errors = ownership_errors(
            "
            func borrow(s: &String) -> Int {
                s.length
            }

            func ok() -> Int {
                let s = \"hello\" + \" world\"
                let n = borrow(s)
                s.length + n
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn by_value_call_argument_moves_owned_value() {
        let errors = ownership_errors(
            "
            func take(s: String) -> Int {
                s.length
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let n = take(s)
                s.length + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn tuple_literal_moves_owned_element() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let pair = (s, 1)
                s.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn array_literal_moves_owned_element() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let array = [s]
                s.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn record_literal_moves_owned_field_value() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let record = { value: s }
                s.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn repeated_owned_call_operand_is_rejected() {
        let errors = ownership_errors(
            "
            func take(a: String, b: String) -> Int {
                a.length + b.length
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                take(s, s)
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn repeated_owned_tuple_operand_is_rejected() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let pair = (s, s)
                0
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn aggregate_move_makes_source_scope_drop_dead() {
        let (output, names) = ownership_output(
            "
            func make() -> Int {
                let s = \"hello\" + \" world\"
                let pair = (s, 1)
                0
            }
            ",
        );
        let s_obligations: Vec<_> = output
            .drop_plan
            .obligations
            .iter()
            .filter(|obligation| {
                names
                    .get(&obligation.key_path.root)
                    .is_some_and(|name| name == "s")
                    && obligation.reason == DropReason::ScopeExit
            })
            .collect();
        assert!(
            s_obligations
                .iter()
                .any(|obligation| obligation.kind == DropElaboration::Dead),
            "expected the moved aggregate source s to have a dead scope drop, got {s_obligations:?}"
        );
    }

    #[test]
    fn elaborate_body_drops_projects_results_onto_statements() {
        // Lowering reads drop/move handling off `statement.ownership`, which
        // `elaborate_body_drops` projects by running the borrow checker's elaboration on
        // lowering's own body. The projection must land the same results the borrow checker
        // records in `drop_plan`/`facts.moves`: `s` is moved into the tuple, so its scope
        // drop is dead and a move of `s` is recorded.
        let source = "
            func make() -> Int {
                let s = \"hello\" + \" world\"
                let pair = (s, 1)
                0
            }
            ";
        let typed = Driver::new(
            vec![Source::from(source)],
            DriverConfig::new("OwnershipTest"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
        assert!(
            !typed.has_errors(),
            "unexpected diagnostics: {:?}",
            typed.diagnostics()
        );

        let types = &typed.phase.types;
        let names = &types.display_names;
        let s = names
            .iter()
            .find_map(|(symbol, name)| (name == "s").then_some(*symbol))
            .expect("s symbol");
        let func = typed
            .phase
            .hir
            .values()
            .flat_map(|file| &file.roots)
            .find_map(|node| match node {
                crate::hir::Node::Decl(decl) => match &decl.kind {
                    crate::hir::DeclKind::Func(func) => Some(func),
                    crate::hir::DeclKind::Let { rhs: Some(rhs), .. } => match &rhs.kind {
                        crate::hir::ExprKind::Func(func) => Some(func),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            })
            .expect("func make in roots");

        let mut body = crate::mir::build_function(types, func.name.symbol().ok(), &func.body);
        crate::ownership::elaborate_body_drops(
            types,
            &typed.phase.resolved_names,
            &typed.phase.ownership,
            &mut body,
        );

        let statements = || body.blocks.iter().flat_map(|block| &block.statements);
        assert!(
            statements()
                .filter_map(|statement| statement.ownership.drop.as_ref())
                .any(|drop| drop.key_path.root == s && drop.kind == DropElaboration::Dead),
            "expected the projected statements to carry a dead scope drop for s"
        );
        assert!(
            statements()
                .flat_map(|statement| &statement.ownership.moves)
                .any(|source| source.root == s),
            "expected the projected statements to carry a move of s"
        );
    }

    #[test]
    fn match_arm_move_then_use_is_rejected() {
        let errors = ownership_errors(
            "
            enum E {
                case a
                case b
            }

            func bad(e: E) -> Int {
                let s = \"hello\" + \" world\"
                match e {
                    .a -> {
                        let moved = s
                        s.length
                    },
                    .b -> 0
                }
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn match_arm_move_does_not_poison_sibling_arm() {
        let errors = ownership_errors(
            "
            enum E {
                case a
                case b
            }

            func ok(e: E) -> Int {
                let s = \"hello\" + \" world\"
                match e {
                    .a -> {
                        let moved = s
                        1
                    },
                    .b -> s.length
                }
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn rejects_use_after_struct_with_owned_field_move() {
        let errors = ownership_errors(
            "
            struct Person {
                let name: String
            }

            func bad() -> Int {
                let person = Person(name: \"Pat\")
                let moved = person
                person.name.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 'person'")),
            "{errors:?}"
        );
    }

    #[test]
    fn allows_sibling_field_after_owned_field_move() {
        let errors = ownership_errors(
            "
            struct Person {
                let name: String
                let age: Int
            }

            func ok() -> Int {
                let person = Person(name: \"Pat\", age: 41)
                let name = person.name
                person.age
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn rejects_whole_struct_use_after_owned_field_move() {
        let errors = ownership_errors(
            "
            struct Person {
                let name: String
                let age: Int
            }

            func bad() -> Int {
                let person = Person(name: \"Pat\", age: 41)
                let name = person.name
                let moved = person
                moved.age
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 'person.name'")),
            "{errors:?}"
        );
    }

    #[test]
    fn field_assignment_restores_moved_field() {
        let errors = ownership_errors(
            "
            struct Person {
                let name: String
                let age: Int
            }

            func ok() -> Int {
                let person = Person(name: \"Pat\", age: 41)
                let name = person.name
                person.name = \"Sue\"
                person.name.length + person.age
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn constructor_argument_moves_owned_value() {
        let errors = ownership_errors(
            "
            struct Box {
                let value: String
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let box = Box(value: s)
                s.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn default_method_receiver_does_not_move_owned_receiver() {
        let errors = ownership_errors(
            "
            struct Box {
                let value: String

                func len() -> Int {
                    self.value.length
                }
            }

            func ok() -> Int {
                let box = Box(value: \"hello\")
                let n = box.len()
                box.value.length + n
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn explicit_consuming_method_receiver_moves_owned_receiver() {
        let errors = ownership_errors(
            "
            struct Box {
                let value: String

                consuming func consume() -> Int {
                    self.value.length
                }
            }

            func bad() -> Int {
                let box = Box(value: \"hello\")
                let n = box.consume()
                box.value.length + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 'box'")),
            "{errors:?}"
        );
    }

    #[test]
    fn explicit_consuming_method_receiver_moves_owned_field_receiver() {
        let errors = ownership_errors(
            "
            struct Name {
                let value: String

                consuming func consume() -> Int {
                    self.value.length
                }
            }

            struct Person {
                let name: Name
                let age: Int
            }

            func bad() -> Int {
                let person = Person(name: Name(value: \"Pat\"), age: 41)
                let n = person.name.consume()
                person.name.value.length + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 'person.name'")),
            "{errors:?}"
        );
    }

    #[test]
    fn by_value_method_argument_moves_owned_value() {
        let errors = ownership_errors(
            "
            struct Sink {
                func take(value: String) -> Int {
                    value.length
                }
            }

            func bad() -> Int {
                let sink = Sink()
                let s = \"hello\" + \" world\"
                let n = sink.take(s)
                s.length + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn borrowed_method_argument_does_not_move_owned_value() {
        let errors = ownership_errors(
            "
            struct Sink {
                func borrow(value: &String) -> Int {
                    value.length
                }
            }

            func ok() -> Int {
                let sink = Sink()
                let s = \"hello\" + \" world\"
                let n = sink.borrow(s)
                s.length + n
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn mutable_method_receiver_invalidates_borrows_of_receiver() {
        let errors = ownership_errors(
            "
            struct Box {
                let value: String

                mut func touch() -> Int {
                    self.value.length
                }
            }

            func bad() -> Int {
                let box = Box(value: \"hello\")
                let sub = box.value.slice(0, 1)
                let n = box.touch()
                sub.length + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of borrowed value 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn shared_method_receiver_cannot_assign_self_field() {
        let diagnostics = diagnostics(
            "
            struct Counter {
                let n: Int

                func bump() -> () {
                    self.n = self.n + 1
                    ()
                }
            }
            ",
        );
        assert!(
            !diagnostics.is_empty(),
            "expected plain method self-field assignment to be rejected"
        );
    }

    #[test]
    fn mut_method_receiver_can_assign_self_field() {
        let diagnostics = diagnostics(
            "
            struct Counter {
                let n: Int

                mut func bump() -> () {
                    self.n = self.n + 1
                    ()
                }
            }
            ",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn allows_reuse_after_copy_struct_assignment() {
        let errors = ownership_errors(
            "
            struct Point {
                let x: Int
            }

            func ok() -> Int {
                let point = Point(x: 1)
                let copy = point
                point.x + copy.x
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn rejects_use_after_generic_struct_instantiated_with_owned_field_move() {
        let errors = ownership_errors(
            "
            struct Box<Item> {
                let value: Item
            }

            func bad() -> Int {
                let box = Box(value: \"hello\")
                let moved = box
                box.value.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 'box'")),
            "{errors:?}"
        );
    }

    #[test]
    fn allows_reuse_after_generic_struct_instantiated_with_copy_field_assignment() {
        let errors = ownership_errors(
            "
            struct Box<Item> {
                let value: Item
            }

            func ok() -> Int {
                let box = Box(value: 1)
                let copy = box
                box.value + copy.value
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn shared_borrow_ends_at_last_use_before_mutation() {
        let errors = ownership_errors(
            "
            struct Box {
                let value: String

                mut func touch() -> Int {
                    self.value.length
                }
            }

            func ok() -> Int {
                let box = Box(value: \"hello\" + \" world\")
                let sub = box.value.slice(0, 1)
                let n = sub.length
                box.touch() + n
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn live_shared_borrow_blocks_later_mutation() {
        let errors = ownership_errors(
            "
            struct Box {
                let value: String

                mut func touch() -> Int {
                    self.value.length
                }
            }

            func bad() -> Int {
                let box = Box(value: \"hello\" + \" world\")
                let sub = box.value.slice(0, 1)
                let n = box.touch()
                sub.length + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("already shared borrowed as 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_read_while_mutable_borrow_is_live() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let borrow: &mut String = s
                let n = s.length
                borrow.length + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("already mutable borrowed as 'borrow'")),
            "{errors:?}"
        );
    }

    #[test]
    fn mutable_borrow_ends_at_last_use_before_read() {
        let errors = ownership_errors(
            "
            func ok() -> Int {
                let s = \"hello\" + \" world\"
                let borrow: &mut String = s
                let n = borrow.length
                s.length + n
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn loop_carried_mutable_borrow_lives_until_storage_dead() {
        let errors = ownership_errors(
            "
            func observe(s: &String) -> Int {
                s.length
            }

            func mutate(s: &mut String) -> Int {
                s.length
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let r: &mut String = s
                let i = 0
                loop i < 2 {
                    let n = observe(r)
                    let m = mutate(s)
                    i = i + 1
                }
                0
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("already mutable borrowed as 'r'")),
            "{errors:?}"
        );
    }

    #[test]
    fn per_iteration_mutable_borrow_can_end_before_mutation() {
        let errors = ownership_errors(
            "
            func observe(s: &String) -> Int {
                s.length
            }

            func mutate(s: &mut String) -> Int {
                s.length
            }

            func ok() -> Int {
                let s = \"hello\" + \" world\"
                let i = 0
                loop i < 2 {
                    let r: &mut String = s
                    let n = observe(r)
                    let m = mutate(s)
                    i = i + 1
                }
                0
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn mutable_call_argument_invalidates_shared_borrow() {
        let errors = ownership_errors(
            "
            func mutate(s: &mut String) -> Int {
                s.length
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let sub = s.slice(0, 1)
                let n = mutate(s)
                sub.length + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of borrowed value 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn nested_function_capture_move_propagates_to_parent() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                func inner [consuming s]() -> Int {
                    s.length
                }
                s.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn handler_body_move_propagates_to_parent() {
        let errors = ownership_errors(
            "
            effect 'ask() -> Int

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                @handle 'ask {
                    let moved = s
                    continue 0
                }
                s.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn trailing_block_body_move_propagates_to_parent() {
        let errors = ownership_errors(
            "
            func run(block: () -> Int) -> Int {
                block()
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let n = run() {
                    let moved = s
                    0
                }
                s.length + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_loop_carried_move_reuse() {
        let errors = ownership_errors(
            "
            func take(s: String) -> Int {
                s.length
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let i = 0
                loop i < 2 {
                    let n = take(s)
                    i = i + 1
                }
                0
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_owned_value_capture_without_capture_mode() {
        let errors = ownership_errors(
            "
            func bad() -> () -> Int {
                let s = \"hello\" + \" world\"
                return func() -> Int { s.length }
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot capture ownership-sensitive value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_borrowed_value_capture_without_capture_mode() {
        let errors = ownership_errors(
            "
            func bad() -> () -> Int {
                let s = \"hello\" + \" world\"
                let sub = s.slice(0, 1)
                return func() -> Int { sub.length }
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot capture ownership-sensitive value 'sub'")),
            "{errors:?}"
        );
    }

    #[test]
    fn explicit_consuming_capture_moves_parent_value() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let f = func [consuming s]() -> Int { s.length }
                s.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn explicit_consuming_capture_can_escape() {
        let errors = ownership_errors(
            "
            func ok() -> () -> Int {
                let s = \"hello\" + \" world\"
                return func [consuming s]() -> Int { s.length }
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn owning_closure_value_copy_moves_source() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let f = func [consuming s]() -> Int { s.length }
                let g = f
                f() + g()
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 'f'")),
            "{errors:?}"
        );
    }

    #[test]
    fn capture_free_function_values_remain_copyable() {
        let errors = ownership_errors(
            "
            func ok() -> Int {
                let f = func() -> Int { 1 }
                let g = f
                f() + g()
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn explicit_copy_capture_requires_copy_type() {
        let errors = ownership_errors(
            "
            func bad() -> () -> Int {
                let s = \"hello\" + \" world\"
                return func [copy s]() -> Int { s.length }
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("copy captures require a copyable type")),
            "{errors:?}"
        );
    }

    #[test]
    fn unused_explicit_borrow_capture_can_end_before_owner_move() {
        let errors = ownership_errors(
            "
            func ok() -> String {
                let s = \"hello\" + \" world\"
                let f = func [&s]() -> Int { s.length }
                return s
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn explicit_borrow_capture_blocks_owner_move_until_closure_last_use() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let f = func [&s]() -> Int { s.length }
                let moved = s
                f()
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot move 's' while it is borrowed as 'f'")),
            "{errors:?}"
        );
    }

    #[test]
    fn unused_explicit_mut_borrow_capture_can_end_before_read() {
        let errors = ownership_errors(
            "
            func ok() -> Int {
                let s = \"hello\" + \" world\"
                let f = func [&mut s]() -> Int { s.length }
                s.length
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn explicit_mut_borrow_capture_blocks_reads_until_closure_last_use() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let f = func [&mut s]() -> Int { s.length }
                let n = s.length
                f() + n
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("already mutable borrowed as 'f'")),
            "{errors:?}"
        );
    }

    #[test]
    fn explicit_borrow_capture_cannot_escape() {
        let errors = ownership_errors(
            "
            func bad() -> () -> Int {
                let s = \"hello\" + \" world\"
                return func [&s]() -> Int { s.length }
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("borrow captures are tied to the current stack frame")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_escaping_generic_capture_returned_through_local() {
        let errors = ownership_errors(
            "
            func bad<Value>(value: Value) -> () -> Value {
                let f = func() -> Value { value }
                return f
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot capture ownership-sensitive value 'value'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_escaping_generic_capture_passed_as_argument() {
        let errors = ownership_errors(
            "
            func accept<Value>(f: () -> Value) -> Int { 0 }

            func bad<Value>(value: Value) -> Int {
                accept(func() -> Value { value })
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot capture ownership-sensitive value 'value'")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_escaping_borrow_capture_even_when_referent_is_copy() {
        let errors = ownership_errors(
            "
            func bad(value: &Int) -> () -> &Int {
                return func() -> &Int { value }
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot capture ownership-sensitive value 'value'")),
            "{errors:?}"
        );
    }

    #[test]
    fn allows_nonescaping_generic_closure_capture() {
        let errors = ownership_errors(
            "
            func ok<Value>(value: Value) -> Value {
                let f = func() -> Value { value }
                f()
            }
            ",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn rejects_use_before_initializer() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s: String
                s.length
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Use of moved value 's'")),
            "{errors:?}"
        );
    }

    #[test]
    fn derives_copy_drop_and_resource_abilities() {
        let (output, names) = ownership_output(
            "
            struct Point {
                let x: Int
            }

            struct Owner {
                let name: String
            }
            ",
        );
        assert!(
            output
                .copyable_types
                .iter()
                .any(|symbol| names.get(symbol).is_some_and(|name| name == "Point")),
            "expected Point to be structurally copyable: {:?}",
            output.copyable_types
        );
        assert!(
            output
                .droppable_types
                .iter()
                .any(|symbol| names.get(symbol).is_some_and(|name| name == "Owner")),
            "expected Owner to require drop: {:?}",
            output.droppable_types
        );
    }

    #[test]
    fn borrowed_nominals_do_not_require_drop_even_with_owned_fields() {
        let (output, names) = ownership_output("func noop() -> Int { 1 }");
        let substring = names
            .iter()
            .find_map(|(symbol, name)| (name == "Substring").then_some(*symbol))
            .expect("Substring is in core");
        assert!(
            output.borrowed_types.contains(&substring),
            "expected Substring to be classified as borrowed"
        );
        assert!(
            !output.droppable_types.contains(&substring),
            "borrowed Substring must not require drop"
        );
    }

    #[test]
    fn string_is_droppable_and_not_copyable() {
        let (output, names) = ownership_output("func noop() -> Int { 1 }");
        let string = names
            .iter()
            .find_map(|(symbol, name)| (name == "String").then_some(*symbol))
            .expect("String is in core");
        assert!(
            output.droppable_types.contains(&string),
            "String must require drop so owned storage is freed"
        );
        assert!(
            !output.copyable_types.contains(&string),
            "String must not be copyable; copying would duplicate ownership of storage"
        );
    }

    #[test]
    fn ownership_facts_record_storage_and_static_scope_drop() {
        let (output, names) = ownership_output(
            "
            func make() -> Int {
                let s = \"hello\" + \" world\"
                1
            }
            ",
        );
        let make = names
            .iter()
            .find_map(|(symbol, name)| (name == "make").then_some(*symbol))
            .expect("make symbol");
        assert!(
            output
                .facts
                .bodies
                .iter()
                .any(|body| body.owner == Some(make)),
            "expected function MIR body to record owner: {:?}",
            output.facts.bodies
        );
        assert!(
            output
                .facts
                .points
                .iter()
                .any(|point| point.kind == PointKind::StorageLive),
            "expected StorageLive points"
        );
        assert!(
            output
                .facts
                .candidate_drops
                .iter()
                .any(|candidate| candidate.reason == DropReason::ScopeExit
                    && names
                        .get(&candidate.target.root)
                        .is_some_and(|name| name == "s")),
            "expected a scope-exit drop candidate for s"
        );
        let s_obligations: Vec<_> = output
            .drop_plan
            .obligations
            .iter()
            .filter(|obligation| {
                names
                    .get(&obligation.key_path.root)
                    .is_some_and(|name| name == "s")
            })
            .collect();
        assert!(
            s_obligations
                .iter()
                .any(|obligation| obligation.kind == DropElaboration::Static),
            "expected a static drop obligation for s, got {s_obligations:?}"
        );
    }

    #[test]
    fn ownership_facts_record_nested_checked_bodies() {
        let (output, _) = ownership_output(
            "
            func run(block: () -> Int) -> Int {
                block()
            }

            func make() -> Int {
                run() {
                    let s = \"hello\" + \" world\"
                    s.length
                }
            }
            ",
        );
        assert!(
            output
                .facts
                .bodies
                .iter()
                .any(|body| body.kind == BodyKind::Nested),
            "expected trailing block MIR to be recorded as a nested body: {:?}",
            output.facts.bodies
        );
    }

    #[test]
    fn ownership_facts_do_not_duplicate_nested_bodies_in_loop_fixpoint() {
        let (output, _) = ownership_output(
            "
            func run(block: () -> Int) -> Int {
                block()
            }

            func make() -> Int {
                let i = 0
                loop i < 2 {
                    let n = run() { 1 }
                    i = i + 1
                }
                0
            }
            ",
        );
        let nested_count = output
            .facts
            .bodies
            .iter()
            .filter(|body| body.kind == BodyKind::Nested)
            .count();
        assert_eq!(
            nested_count, 1,
            "expected one recorded nested body, got {:?}",
            output.facts.bodies
        );
    }

    #[test]
    fn ownership_facts_do_not_duplicate_loop_borrow_facts() {
        let (output, _) = ownership_output(
            "
            func make() -> Int {
                let s = \"hello\" + \" world\"
                let i = 0
                loop i < 2 {
                    let borrow: &String = s
                    let n = borrow.length
                    i = i + 1
                }
                s.length
            }
            ",
        );
        let mut seen = FxHashSet::default();
        for loan in &output.facts.borrows {
            assert!(
                seen.insert((
                    loan.point,
                    loan.node,
                    loan.borrower.clone(),
                    loan.owner.clone(),
                    loan.kind,
                )),
                "duplicate borrow fact: {loan:?}"
            );
        }
    }

    #[test]
    fn branch_move_makes_scope_drop_conditional() {
        let (output, names) = ownership_output(
            "
            func maybe(flag: Bool) -> Int {
                let s = \"hi\" + \"!\"
                if flag {
                    let t = s
                    1
                } else {
                    2
                }
                0
            }
            ",
        );
        let s_obligations: Vec<_> = output
            .drop_plan
            .obligations
            .iter()
            .filter(|obligation| {
                names
                    .get(&obligation.key_path.root)
                    .is_some_and(|name| name == "s")
            })
            .collect();
        assert!(
            s_obligations
                .iter()
                .any(|obligation| obligation.kind == DropElaboration::Conditional),
            "expected a conditional drop obligation for s, got {s_obligations:?}"
        );
        assert!(
            !s_obligations
                .iter()
                .any(|obligation| obligation.kind == DropElaboration::Dead),
            "branch-local move must not make every s drop dead: {s_obligations:?}"
        );
    }

    #[test]
    fn user_protocol_named_owner_is_not_a_marker_ability() {
        let (output, names) = ownership_output(
            "// no-core
            protocol Owner {}
            struct Box {
                let value: Int
            }
            extend Box: Owner {}
            ",
        );
        assert!(
            !output
                .owned_types
                .iter()
                .any(|symbol| names.get(symbol).is_some_and(|name| name == "Box")),
            "user protocol Owner must not mark Box as owned: {:?}",
            output.owned_types
        );
    }
}
