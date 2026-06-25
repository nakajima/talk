use std::{collections::VecDeque, error::Error, fmt::Display};

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    ast::{AST, NameResolved},
    compiling::{driver::Source, module::ModuleId},
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    mir,
    name_resolution::{
        name_resolver::ResolvedNames,
        symbol::{Symbol, set_symbol_names},
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        body::Body,
        decl::DeclKind,
        expr::{Expr, ExprKind},
        func::{CaptureMode, CaptureSpec},
        parameter::Parameter,
        stmt::StmtKind,
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
}

impl OwnershipOutput {
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
}

#[derive(Clone, Debug)]
pub struct PointFact {
    pub point: OwnershipPoint,
    pub kind: PointKind,
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
    pub key_path: KeyPath,
    pub ty: Option<Ty>,
}

#[derive(Clone, Debug)]
pub struct MoveFact {
    pub point: OwnershipPoint,
    pub source: KeyPath,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub struct LoanFact {
    pub id: LoanId,
    pub origin: OriginId,
    pub point: Option<OwnershipPoint>,
    pub borrower: KeyPath,
    pub owner: Option<KeyPath>,
    pub kind: BorrowKind,
}

#[derive(Clone, Debug)]
pub struct InvalidationFact {
    pub point: Option<OwnershipPoint>,
    pub loan: Option<LoanId>,
    pub owner: KeyPath,
}

#[derive(Clone, Debug)]
pub struct AssignmentFact {
    pub point: OwnershipPoint,
    pub target: KeyPath,
    pub ty: Option<Ty>,
}

#[derive(Clone, Debug)]
pub struct CandidateDropFact {
    pub point: OwnershipPoint,
    pub target: KeyPath,
    pub ty: Option<Ty>,
    pub reason: DropReason,
}

#[derive(Clone, Debug, Default)]
pub struct DropPlan {
    pub obligations: Vec<DropObligation>,
}

#[derive(Clone, Debug)]
pub struct DropObligation {
    pub point: OwnershipPoint,
    pub key_path: KeyPath,
    pub ty: Ty,
    pub kind: DropKind,
    pub reason: DropReason,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DropKind {
    Static,
    Dead,
    Conditional,
    Open,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DropReason {
    ScopeExit,
    AssignmentReplace,
    EarlyExit,
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

pub fn check_ownership(
    asts: &IndexMap<Source, AST<NameResolved>>,
    types: &TypeOutput,
    resolved: &ResolvedNames,
    _module_id: ModuleId,
) -> (OwnershipOutput, Vec<AnyDiagnostic>) {
    let _names = set_symbol_names(types.display_names.clone());
    let mut checker = OwnershipChecker {
        types,
        resolved,
        module_id: _module_id,
        diagnostics: vec![],
        reported: FxHashSet::default(),
        output: OwnershipOutput::default(),
    };
    checker.discover_borrowed_types();
    checker.discover_owned_types();
    checker.discover_copy_drop_abilities();
    checker.check_struct_fields();
    checker.check_enum_payloads();
    checker.check_top_level_globals(asts);
    checker.check_raw_pointer_surface(asts);
    checker.check_moves(asts);
    (checker.output, checker.diagnostics)
}

struct OwnershipChecker<'a> {
    types: &'a TypeOutput,
    resolved: &'a ResolvedNames,
    module_id: ModuleId,
    diagnostics: Vec<AnyDiagnostic>,
    reported: FxHashSet<(NodeID, OwnershipError)>,
    output: OwnershipOutput,
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
type MoveEnv = FxHashMap<KeyPath, NodeID>;

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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct MoveState {
    moved: MoveEnv,
    borrows: BorrowInfoEnv,
    invalid_borrows: FxHashMap<KeyPath, KeyPath>,
    borrowed_roots: FxHashMap<Symbol, String>,
    shared_borrow_roots: FxHashMap<Symbol, String>,
    active_loans: Vec<ActiveLoan>,
    use_counts: FxHashMap<Symbol, usize>,
    closure_captures: FxHashMap<KeyPath, ClosureCaptureSummary>,
}

type BorrowInfoEnv = FxHashMap<KeyPath, BorrowInfo>;

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
    fn with_use_counts(use_counts: FxHashMap<Symbol, usize>) -> Self {
        Self {
            use_counts,
            ..Default::default()
        }
    }

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
    }

    fn restore_key_path(&mut self, key_path: &KeyPath) {
        self.moved.retain(|moved, _| !key_path.contains(moved));
        self.borrows.retain(|borrow, _| !key_path.contains(borrow));
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
        self.active_loans.push(ActiveLoan {
            borrower,
            owner,
            kind,
        });
    }

    fn release_loan_for_borrower(&mut self, borrower: &KeyPath) {
        self.active_loans
            .retain(|loan| !borrower.contains(&loan.borrower));
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
        self.invalid_borrows.extend(other.invalid_borrows.clone());
        self.borrowed_roots.extend(other.borrowed_roots.clone());
        self.shared_borrow_roots
            .extend(other.shared_borrow_roots.clone());
        for loan in &other.active_loans {
            if !self.active_loans.contains(loan) {
                self.active_loans.push(loan.clone());
            }
        }
        for (symbol, count) in &other.use_counts {
            let entry = self.use_counts.entry(*symbol).or_insert(0);
            *entry = (*entry).max(*count);
        }
        for (path, summary) in &other.closure_captures {
            self.closure_captures
                .entry(path.clone())
                .or_default()
                .extend(summary.clone());
        }
        *self != before
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

    fn check_struct_fields(&mut self) {
        for (owner, info) in &self.types.catalog.structs {
            if self.is_borrowed_symbol(*owner) {
                continue;
            }
            let owner_name = self.render_symbol(*owner);
            for (field, (property, ty)) in &info.fields {
                if self.contains_borrowed_type(ty) {
                    let id = self
                        .resolved
                        .symbols_to_node
                        .get(property)
                        .copied()
                        .unwrap_or(NodeID(FileID(0), 0));
                    self.error(
                        id,
                        OwnershipError::BorrowedField {
                            owner: owner_name.clone(),
                            field: field.clone(),
                            ty: ty.render_mono(),
                        },
                    );
                }
            }
        }
    }

    fn check_enum_payloads(&mut self) {
        for (owner, info) in &self.types.catalog.enums {
            if self.is_borrowed_symbol(*owner) {
                continue;
            }
            let owner_name = self.render_symbol(*owner);
            for (variant_name, variant) in &info.variants {
                for ty in variant.argument_types() {
                    if self.contains_borrowed_type(ty) {
                        let id = self
                            .resolved
                            .symbols_to_node
                            .get(&variant.symbol)
                            .copied()
                            .unwrap_or(NodeID(FileID(0), 0));
                        self.error(
                            id,
                            OwnershipError::BorrowedEnumPayload {
                                owner: owner_name.clone(),
                                variant: variant_name.clone(),
                                ty: ty.render_mono(),
                            },
                        );
                    }
                }
            }
        }
    }

    fn check_top_level_globals(&mut self, asts: &IndexMap<Source, AST<NameResolved>>) {
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

    fn check_raw_pointer_surface(&mut self, asts: &IndexMap<Source, AST<NameResolved>>) {
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

        let raw_nodes: Vec<_> = self
            .types
            .node_types
            .iter()
            .filter_map(|(id, ty)| {
                (safe_files.contains(&id.0) && self.type_mentions_raw_ptr(ty))
                    .then_some((*id, ty.render_mono()))
            })
            .collect();
        for (id, ty) in raw_nodes {
            self.error(id, OwnershipError::UnsafeRawPointerUsage { ty });
        }
    }

    fn check_moves(&mut self, asts: &IndexMap<Source, AST<NameResolved>>) {
        for ast in asts.values() {
            self.check_decl_moves_in_slice(&ast.roots);
        }
    }

    fn check_decl_moves_in_slice(&mut self, nodes: &[Node]) {
        let mut body = mir::build_nodes(self.types, nodes);
        let body_id = self.record_mir_body(&body, BodyKind::TopLevel);
        self.elaborate_drops(body_id, &mut body);
        let mut state = MoveState::with_use_counts(mir::use_counts_ref(&body));
        self.check_mir_body(&body, &mut state);
    }

    fn check_body_moves(&mut self, body: &Body) {
        for decl in &body.decls {
            let mut body = mir::build_decls(self.types, std::slice::from_ref(decl));
            let body_id = self.record_mir_body(&body, BodyKind::DeclBody);
            self.elaborate_drops(body_id, &mut body);
            let mut state = MoveState::with_use_counts(mir::use_counts_ref(&body));
            self.check_mir_body(&body, &mut state);
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
        let body_id = self.record_mir_body(&body, BodyKind::Function);
        self.elaborate_drops(body_id, &mut body);
        if parent_state.is_some() {
            self.check_closure_captures(captures, params, source_body, &body, parent_state);
        }
        let mut state = MoveState::with_use_counts(mir::use_counts_ref(&body));
        self.seed_shared_borrow_params(params, &mut state);
        self.check_mir_body(&body, &mut state);
    }

    fn check_closure_captures(
        &mut self,
        capture_specs: &[CaptureSpec],
        params: &[Parameter],
        source_body: &Block,
        body: &mir::Body<'_>,
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
        body: &mir::Body<'_>,
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

    fn capture_uses(&self, body: &mir::Body<'_>) -> FxHashMap<Symbol, (NodeID, Ty)> {
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
                        if let Some(ty) = self.types.node_types.get(&root.id).cloned() {
                            captures.entry(symbol).or_insert((root.id, ty));
                        }
                    }
                    mir::Statement::AssignmentRootUse { id, symbol } => {
                        if let Some(ty) = self.types.node_types.get(id).cloned() {
                            captures.entry(*symbol).or_insert((*id, ty));
                        }
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
            ExprKind::Unary(_, inner) | ExprKind::As(inner, _) => {
                self.collect_closure_values_capture_summary(
                    inner,
                    state,
                    include_stored_closures,
                    summary,
                );
            }
            ExprKind::Binary(lhs, _, rhs) => {
                self.collect_closure_values_capture_summary(
                    lhs,
                    state,
                    include_stored_closures,
                    summary,
                );
                self.collect_closure_values_capture_summary(
                    rhs,
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
            | ExprKind::Incomplete(_)
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
                    self.apply_capture_borrow(capture, BorrowKind::Shared, borrower, state);
                }
                Some(CaptureMode::BorrowMut) => {
                    self.apply_capture_borrow(capture, BorrowKind::Mutable, borrower, state);
                }
            }
        }
    }

    fn check_capture_read(&mut self, capture: &ClosureCapture, state: &mut MoveState) {
        let key_path = KeyPath::root(capture.symbol);
        self.check_key_path_use_for_id(capture.id, &key_path, false, state);
    }

    fn apply_capture_move(&mut self, capture: &ClosureCapture, state: &mut MoveState) {
        let key_path = KeyPath::root(capture.symbol);
        self.check_key_path_use_for_id(capture.id, &key_path, true, state);
        self.check_move_out_of_borrowed_key_path(capture.id, &key_path, state);
        self.check_move_while_borrowed(capture.id, &key_path, state);
        state.moved.insert(key_path.clone(), capture.id);
        state.invalidate_borrows_of(&key_path);
    }

    fn apply_capture_borrow(
        &mut self,
        capture: &ClosureCapture,
        kind: BorrowKind,
        borrower: Option<&KeyPath>,
        state: &mut MoveState,
    ) {
        let source = KeyPath::root(capture.symbol);
        self.check_key_path_use_for_id(capture.id, &source, false, state);
        let owner = self.loan_owner_for_key_path(&source, state);
        self.check_borrow_conflicts(capture.id, &owner, kind, Some(&source), state);
        let Some(borrower) = borrower else {
            return;
        };
        let loan_id = LoanId(self.output.facts.borrows.len() as u32);
        let origin_id = OriginId(self.output.facts.borrows.len() as u32);
        self.output.facts.borrows.push(LoanFact {
            id: loan_id,
            origin: origin_id,
            point: None,
            borrower: borrower.clone(),
            owner: Some(owner.clone()),
            kind,
        });
        state.add_loan(borrower.clone(), owner, kind);
    }

    fn record_mir_body(&mut self, body: &mir::Body<'_>, kind: BodyKind) -> BodyId {
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
        body: &mir::Body<'_>,
        point: OwnershipPoint,
        statement: &mir::Statement<'_>,
    ) {
        match statement {
            mir::Statement::StorageLive { symbol, .. } => {
                self.output.facts.storage_live.push(StorageFact {
                    point,
                    key_path: KeyPath::root(*symbol),
                    ty: self.symbol_ty(*symbol).cloned(),
                });
            }
            mir::Statement::StorageDead { symbol, .. } => {
                self.output.facts.storage_dead.push(StorageFact {
                    point,
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
                if let Some(target) = key_path
                    .as_ref()
                    .and_then(|target| Self::key_path_from_mir(body, target))
                    .or_else(|| self.drop_target_key_path(target))
                {
                    self.output.facts.candidate_drops.push(CandidateDropFact {
                        point,
                        ty: self.key_path_ty(&target),
                        target,
                        reason: map_drop_reason(*reason),
                    });
                }
            }
            _ => {}
        }
    }

    fn elaborate_drops(&mut self, body_id: BodyId, body: &mut mir::Body<'_>) {
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
                match &mut statement.kind {
                    mir::Statement::DropCandidate {
                        target,
                        key_path,
                        elaboration,
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
                        *elaboration = Some(mir_drop_elaboration(kind));
                        self.output.drop_plan.obligations.push(DropObligation {
                            point,
                            key_path,
                            ty,
                            kind,
                            reason: map_drop_reason(*reason),
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
        body: &mir::Body<'_>,
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
        statement: &mir::Statement<'_>,
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
                let rhs_ty = rhs.and_then(|rhs| self.types.node_types.get(&rhs.id).cloned());
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
                    if target.fields.is_empty()
                        && let Some(ty) = self.types.node_types.get(&lhs.id).cloned()
                    {
                        state.root_tys.insert(target.root, ty);
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
        let Some(key_path) = self.key_path(expr) else {
            return;
        };
        let Some(ty) = self.types.node_types.get(&expr.id).cloned() else {
            return;
        };
        if self.needs_drop_type(&ty) && key_path.is_tracked_storage_root() {
            state.note_move(key_path.clone(), expr.id);
            if let Some(point) = point {
                self.output.facts.moves.push(MoveFact {
                    point,
                    source: key_path,
                    ty,
                });
            }
        }
    }

    fn note_call_drop_moves(
        &mut self,
        callee: &Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
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
                            self.output.facts.moves.push(MoveFact {
                                point,
                                source: key_path,
                                ty,
                            });
                        }
                    }
                }
            }
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
                for item in items {
                    self.note_capture_drop_moves(item, point, state);
                }
            }
            ExprKind::Unary(_, inner) | ExprKind::As(inner, _) => {
                self.note_capture_drop_moves(inner, point, state);
            }
            ExprKind::Binary(lhs, _, rhs) => {
                self.note_capture_drop_moves(lhs, point, state);
                self.note_capture_drop_moves(rhs, point, state);
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
            | ExprKind::Incomplete(_)
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

    fn check_mir_body(&mut self, body: &mir::Body<'_>, state: &mut MoveState) {
        if body.blocks.is_empty() {
            return;
        }

        let mut in_states: Vec<Option<MoveState>> = vec![None; body.blocks.len()];
        in_states[body.entry.0] = Some(state.clone());

        let mut worklist = VecDeque::new();
        worklist.push_back(body.entry);

        while let Some(block) = worklist.pop_front() {
            let Some(mut block_state) = in_states[block.0].clone() else {
                continue;
            };
            self.check_mir_block(body, block, &mut block_state);

            for successor in terminator_successors(&body.blocks[block.0].terminator) {
                let changed = match &mut in_states[successor.0] {
                    Some(existing) => existing.merge_from(&block_state),
                    slot @ None => {
                        *slot = Some(block_state.clone());
                        true
                    }
                };
                if changed {
                    worklist.push_back(successor);
                }
            }
        }
    }

    fn check_mir_block(
        &mut self,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        state: &mut MoveState,
    ) {
        let basic_block = &body.blocks[block.0];
        for statement in &basic_block.statements {
            self.check_mir_statement(&statement.kind, state);
        }
    }

    fn check_mir_statement(&mut self, statement: &mir::Statement<'_>, state: &mut MoveState) {
        match statement {
            mir::Statement::ScopeEnter { .. }
            | mir::Statement::ScopeExit { .. }
            | mir::Statement::StorageLive { .. }
            | mir::Statement::DropCandidate { .. } => {}
            mir::Statement::StorageDead { symbol, .. } => {
                state.finish_storage(&KeyPath::root(*symbol));
            }
            mir::Statement::Read { expr } => self.check_read_expr(expr, state),
            mir::Statement::ConsumeValue { expr, .. } => self.check_consumed_expr(expr, state),
            mir::Statement::AssignmentRootUse { id, symbol } => {
                self.check_assignment_root_use(*id, *symbol, state)
            }
            mir::Statement::Bind {
                lhs,
                type_annotation,
                rhs,
                ..
            } => self.check_binding(lhs, *type_annotation, *rhs, state),
            mir::Statement::Assign { lhs, rhs, .. } => self.check_assignment(lhs, rhs, state),
            mir::Statement::Call {
                callee,
                args,
                trailing_block,
                trailing_body,
            } => self.check_call(
                callee,
                args,
                *trailing_block,
                trailing_body.as_deref(),
                state,
            ),
            mir::Statement::Perform => {}
            mir::Statement::ReturnValue { expr, .. } => self.check_return_value(expr, state),
            mir::Statement::ContinueValue { expr, .. } => self.check_consumed_expr(expr, state),
            mir::Statement::Function {
                owner,
                captures,
                params,
                body,
            } => self.check_func_moves(*owner, captures, params, body, Some(state)),
            mir::Statement::Handling { body, .. } => {
                let mut body_state = state.clone();
                let handler_body = mir::build_block(self.types, body);
                self.check_mir_body(&handler_body, &mut body_state);
            }
            mir::Statement::DeclBody { body } => self.check_body_moves(body),
        }
    }

    fn check_binding(
        &mut self,
        lhs: &crate::node_kinds::pattern::Pattern,
        type_annotation: Option<&crate::node_kinds::type_annotation::TypeAnnotation>,
        rhs: Option<&Expr>,
        state: &mut MoveState,
    ) {
        if let Some(rhs) = rhs {
            self.check_untracked_borrowed_aggregate(rhs);
        }
        let borrow_info = rhs.and_then(|rhs| self.binding_borrow_info(type_annotation, rhs, state));
        let closure_captures = rhs.map(|rhs| self.closure_values_capture_summary(rhs, state));
        let literal_captures = rhs.map(|rhs| self.closure_literal_capture_summary(rhs, state));
        let binders = lhs.collect_binders();
        for (id, symbol) in &binders {
            let key_path = KeyPath::root(*symbol);
            if rhs.is_some() {
                state.initialize_key_path(&key_path);
            } else {
                state.moved.insert(key_path.clone(), *id);
            }
            if let Some(summary) = &closure_captures {
                if binders.len() == 1
                    && let Some(literal_captures) = &literal_captures
                {
                    self.apply_closure_capture_effects(literal_captures, Some(&key_path), state);
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
            if let Some(info) = &borrow_info {
                let rhs = rhs.expect("borrow info requires rhs");
                self.install_borrow(key_path, info.clone(), rhs.id, state);
            }
        }
        if let Some(rhs) = rhs {
            self.mark_simple_move_source(rhs, state);
        }
    }

    fn check_assignment(&mut self, lhs: &Expr, rhs: &Expr, state: &mut MoveState) {
        self.check_untracked_borrowed_aggregate(rhs);
        let rhs_borrow = self.binding_borrow_info(None, rhs, state);
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
            self.apply_closure_capture_effects(&literal_captures, Some(&key_path), state);
            state
                .closure_captures
                .insert(key_path.clone(), closure_captures);
        }
        if let Some(info) = rhs_borrow {
            self.install_borrow(key_path, info, rhs.id, state);
        }
        self.mark_simple_move_source(rhs, state);
    }

    fn check_call(
        &mut self,
        callee: &Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
        trailing_block: Option<&Block>,
        trailing_body: Option<&mir::Body<'_>>,
        state: &mut MoveState,
    ) {
        if matches!(callee.kind, ExprKind::Func(_)) {
            let callee_captures = self.closure_literal_capture_summary(callee, state);
            self.apply_closure_capture_effects(&callee_captures, None, state);
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
                _ => self.mark_simple_move_source(receiver, state),
            }
            let params = self
                .member_value_params(callee)
                .or_else(|| self.call_argument_types(callee));
            self.check_argument_accesses(
                args,
                params.as_ref(),
                self.call_constructs_borrowed_value(callee),
                state,
            );
        } else {
            let params = self.call_argument_types(callee);
            self.check_argument_accesses(
                args,
                params.as_ref(),
                self.call_constructs_borrowed_value(callee),
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
        if let Some(body) = trailing_body {
            let mut body_state = state.clone();
            self.check_mir_body(body, &mut body_state);
        }
    }

    fn check_argument_accesses(
        &mut self,
        args: &[crate::node_kinds::call_arg::CallArg],
        params: Option<&Vec<Ty>>,
        borrowed_constructor: bool,
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
                    }
                }
                _ => {
                    self.check_escaping_closure_values(&arg.value, state);
                    let closure_captures = self.closure_literal_capture_summary(&arg.value, state);
                    self.apply_closure_capture_effects(&closure_captures, None, state);
                    if !borrowed_constructor {
                        self.mark_simple_move_source(&arg.value, state);
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

    fn check_consumed_expr(&mut self, expr: &Expr, state: &mut MoveState) {
        self.check_escaping_closure_values(expr, state);
        let closure_captures = self.closure_literal_capture_summary(expr, state);
        self.apply_closure_capture_effects(&closure_captures, None, state);
        self.mark_simple_move_source(expr, state);
    }

    fn check_assignment_root_use(&mut self, id: NodeID, symbol: Symbol, state: &mut MoveState) {
        let key_path = KeyPath::root(symbol);
        if let Some((moved, _)) = self.moved_key_path_for_use(&key_path, id, false, state) {
            self.error(
                id,
                OwnershipError::UseAfterMove {
                    name: self.render_key_path(moved),
                    ty: "owned value".to_string(),
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
        self.note_key_path_use(&key_path, state);
    }

    fn check_return_value(&mut self, expr: &Expr, state: &mut MoveState) {
        self.check_escaping_closure_values(expr, state);
        let closure_captures = self.closure_literal_capture_summary(expr, state);
        self.apply_closure_capture_effects(&closure_captures, None, state);
        if !self.expr_is_copy(expr) {
            self.check_move_out_of_borrowed_value(expr.id, expr, state);
        }
        if self.expr_contains_untracked_borrowed_aggregate(expr) {
            let ty = self.borrowed_value_ty(expr);
            self.error(expr.id, OwnershipError::UnknownBorrowProvenance { ty });
            return;
        }
        if !self.expr_is_borrowed(expr) {
            self.mark_simple_move_source(expr, state);
            return;
        }
        let info = self.borrow_info(expr, &state.borrows);
        if info.origin == BorrowOrigin::Unknown {
            let ty = self.borrowed_value_ty(expr);
            self.error(expr.id, OwnershipError::UnknownBorrowProvenance { ty });
        } else if info.origin.is_function_owned() {
            let ty = self.borrowed_value_ty(expr);
            self.error(expr.id, OwnershipError::ReturningLocalBorrow { ty });
        }
    }

    fn seed_shared_borrow_params(&self, params: &[Parameter], state: &mut MoveState) {
        for param in params {
            let Some((kind, ty)) = self.param_borrow_ty(param) else {
                continue;
            };
            let Ok(symbol) = param.name.symbol() else {
                continue;
            };
            state.borrowed_roots.insert(symbol, ty.clone());
            if kind == BorrowKind::Shared {
                state.shared_borrow_roots.insert(symbol, ty);
            }
        }
    }

    fn mark_simple_move_source(&mut self, expr: &Expr, state: &mut MoveState) {
        if !self.expr_is_copy(expr) {
            self.check_move_out_of_borrowed_value(expr.id, expr, state);
        }
        let Some(key_path) = self.key_path(expr) else {
            return;
        };
        if self.expr_is_owned(expr) && key_path.is_tracked_storage_root() {
            self.check_move_while_borrowed(expr.id, &key_path, state);
            state.moved.insert(key_path.clone(), expr.id);
            state.invalidate_borrows_of(&key_path);
        }
    }

    fn check_key_path_use(&mut self, expr: &Expr, key_path: &KeyPath, state: &mut MoveState) {
        self.check_key_path_use_for_id(expr.id, key_path, self.expr_is_owned(expr), state);
    }

    fn check_key_path_use_for_id(
        &mut self,
        id: NodeID,
        key_path: &KeyPath,
        use_is_owned: bool,
        state: &mut MoveState,
    ) {
        if let Some((moved, _)) = self.moved_key_path_for_use(key_path, id, use_is_owned, state) {
            self.error(
                id,
                OwnershipError::UseAfterMove {
                    name: self.render_key_path(moved),
                    ty: self
                        .types
                        .node_types
                        .get(&id)
                        .map(Ty::render_mono)
                        .unwrap_or_else(|| "owned value".to_string()),
                },
            );
        } else if let Some((borrow, owner)) = self.invalid_borrow_for_use(key_path, state) {
            self.error(
                id,
                OwnershipError::UseAfterInvalidatedBorrow {
                    name: self.render_key_path(borrow),
                    owner: self.render_key_path(owner),
                    ty: self
                        .types
                        .node_types
                        .get(&id)
                        .map(Ty::render_mono)
                        .unwrap_or_else(|| "borrowed value".to_string()),
                },
            );
        }
        let owner = self.loan_owner_for_key_path(key_path, state);
        self.check_borrow_conflicts(id, &owner, BorrowKind::Shared, Some(key_path), state);
        self.note_key_path_use(key_path, state);
    }

    fn moved_key_path_for_use<'a>(
        &self,
        key_path: &KeyPath,
        _id: NodeID,
        use_is_owned: bool,
        state: &'a MoveState,
    ) -> Option<(&'a KeyPath, NodeID)> {
        state.moved.iter().find_map(|(moved, node)| {
            (moved.contains(key_path) || key_path.contains(moved) && use_is_owned)
                .then_some((moved, *node))
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

    fn drop_target_key_path(&self, target: &mir::DropTarget<'_>) -> Option<KeyPath> {
        match target {
            mir::DropTarget::Symbol { symbol, .. } => Some(KeyPath::root(*symbol)),
            mir::DropTarget::Expr(expr) => self.key_path(expr),
        }
    }

    fn key_path_from_mir(body: &mir::Body<'_>, key_path: &mir::KeyPath) -> Option<KeyPath> {
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
        if let Some(Ty::Borrow(BorrowKind::Shared, _)) = self.types.node_types.get(&receiver.id) {
            let name = self
                .key_path(receiver)
                .map(|key_path| self.render_key_path(&key_path))
                .unwrap_or_else(|| "borrowed value".to_string());
            let ty = self
                .types
                .node_types
                .get(&receiver.id)
                .map(Ty::render_mono)
                .unwrap_or_else(|| "shared borrow".to_string());
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
        if let Some(ty) = self.types.node_types.get(&param.id)
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
        match self.types.node_types.get(&expr.id) {
            Some(Ty::Borrow(kind, _)) => Some(*kind),
            Some(ty) if self.is_borrowed_type(ty) => Some(BorrowKind::Shared),
            _ => None,
        }
    }

    fn borrowed_value_ty(&self, expr: &Expr) -> String {
        self.types
            .node_types
            .get(&expr.id)
            .map(Ty::render_mono)
            .unwrap_or_else(|| "borrowed value".to_string())
    }

    fn allows_unknown_local_borrow(&self, expr: &Expr) -> bool {
        let Some(Ty::Borrow(_, inner)) = self.types.node_types.get(&expr.id) else {
            return false;
        };
        self.is_copy_type(inner)
    }

    fn install_borrow(
        &mut self,
        borrower: KeyPath,
        info: BorrowInfo,
        id: NodeID,
        state: &mut MoveState,
    ) {
        let loan_id = LoanId(self.output.facts.borrows.len() as u32);
        let origin_id = OriginId(self.output.facts.borrows.len() as u32);
        self.output.facts.borrows.push(LoanFact {
            id: loan_id,
            origin: origin_id,
            point: None,
            borrower: borrower.clone(),
            owner: info.owner.clone(),
            kind: info.kind,
        });
        if let Some(owner) = &info.owner {
            self.check_borrow_conflicts(id, owner, info.kind, None, state);
            state.add_loan(borrower.clone(), owner.clone(), info.kind);
        }
        if info.kind == BorrowKind::Shared {
            state
                .shared_borrow_roots
                .insert(borrower.root, borrow_kind_name(info.kind).to_string());
        }
        state
            .borrowed_roots
            .insert(borrower.root, borrow_kind_name(info.kind).to_string());
        state.borrows.insert(borrower.clone(), info);
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
        let ty = self
            .types
            .node_types
            .get(&expr.id)
            .map(Ty::render_mono)
            .unwrap_or_else(|| "owned value".to_string());
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

    fn note_key_path_use(&self, key_path: &KeyPath, state: &mut MoveState) {
        let Some(count) = state.use_counts.get_mut(&key_path.root) else {
            return;
        };
        if *count == 0 {
            return;
        }
        *count -= 1;
        if *count == 0 {
            state.release_loan_for_borrower(&KeyPath::root(key_path.root));
        }
    }

    fn stored_field_symbol(&self, expr: &Expr) -> Option<Symbol> {
        stored_field_symbol(self.types, expr)
    }

    fn call_argument_types(&self, callee: &Expr) -> Option<Vec<Ty>> {
        let Ty::Func(params, _, _) = self.types.node_types.get(&callee.id)? else {
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
        let resolution = self.types.member_resolutions.get(&callee.id)?;
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
                    let ExprKind::Member(_, label, _) = &callee.kind else {
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
        self.types
            .node_types
            .get(&expr.id)
            .is_some_and(|ty| self.needs_drop_type(ty))
    }

    fn expr_is_copy(&self, expr: &Expr) -> bool {
        self.types
            .node_types
            .get(&expr.id)
            .is_some_and(|ty| self.is_copy_type(ty))
    }

    fn expr_is_borrowed(&self, expr: &Expr) -> bool {
        self.types
            .node_types
            .get(&expr.id)
            .is_some_and(|ty| self.is_borrowed_type(ty))
    }

    fn check_untracked_borrowed_aggregate(&mut self, expr: &Expr) {
        if self.expr_contains_untracked_borrowed_aggregate(expr) {
            let ty = self.borrowed_value_ty(expr);
            self.error(expr.id, OwnershipError::UnknownBorrowProvenance { ty });
        }
    }

    fn expr_contains_untracked_borrowed_aggregate(&self, expr: &Expr) -> bool {
        self.types.node_types.get(&expr.id).is_some_and(|ty| {
            !matches!(ty, Ty::Func(..))
                && self.contains_borrowed_type(ty)
                && !self.is_borrowed_type(ty)
        })
    }

    fn borrow_info(&self, expr: &Expr, env: &BorrowEnv) -> BorrowInfo {
        match &expr.kind {
            ExprKind::Variable(name) => match name.symbol() {
                Ok(symbol) => self.symbol_borrow_info(symbol, env, expr),
                Err(_) => BorrowInfo::new(BorrowOrigin::Unknown, None),
            },
            ExprKind::LiteralString(_) => BorrowInfo::new(BorrowOrigin::Static, None),
            ExprKind::Member(Some(_), ..) if self.key_path(expr).is_some() => {
                let owner = self.key_path(expr).expect("checked above");
                self.key_path_borrow_info(&owner, expr, env)
            }
            ExprKind::Call { callee, args, .. } => self.call_borrow_info(callee, args, env),
            _ => BorrowInfo::new(BorrowOrigin::Unknown, None),
        }
    }

    fn call_borrow_info(
        &self,
        callee: &Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
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
        let Some(Ty::Func(_, ret, _)) = self.types.node_types.get(&callee.id) else {
            return false;
        };
        self.is_borrowed_type(ret)
    }

    fn call_constructs_borrowed_value(&self, callee: &Expr) -> bool {
        matches!(callee.kind, ExprKind::Constructor(_)) && self.call_returns_borrowed(callee)
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
            _ if self.key_path(receiver).is_some() => {
                let owner = self.key_path(receiver).expect("checked above");
                self.borrow_info_with_default_owner(
                    self.key_path_borrow_info(&owner, receiver, env),
                    receiver,
                )
            }
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
        args: &[crate::node_kinds::call_arg::CallArg],
        params: Option<&[Ty]>,
        env: &BorrowEnv,
    ) -> BorrowInfo {
        let Some(params) = params else {
            return BorrowInfo::new(BorrowOrigin::Unknown, None);
        };
        let mut result: Option<BorrowInfo> = None;
        for (arg, param) in args.iter().zip(params) {
            if !self.is_borrowed_type(param) {
                continue;
            }
            let info =
                self.borrow_info_with_default_owner(self.borrow_info(&arg.value, env), &arg.value);
            if result.is_some() {
                return BorrowInfo::new(BorrowOrigin::Unknown, None);
            }
            result = Some(info);
        }
        result.unwrap_or_else(|| BorrowInfo::new(BorrowOrigin::Unknown, None))
    }

    fn single_constructor_borrow_source_info(
        &self,
        args: &[crate::node_kinds::call_arg::CallArg],
        env: &BorrowEnv,
    ) -> BorrowInfo {
        let mut result: Option<BorrowInfo> = None;
        for arg in args {
            if !self.expr_is_borrowed(&arg.value) && !self.expr_is_owned(&arg.value) {
                continue;
            }
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
            && self
                .types
                .node_types
                .get(&expr.id)
                .is_some_and(|ty| self.is_borrowed_type(ty) || self.is_owned_type(ty))
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
                if self
                    .types
                    .node_types
                    .get(&expr.id)
                    .is_some_and(|ty| self.is_borrowed_type(ty) || self.is_owned_type(ty))
                {
                    BorrowInfo::new(BorrowOrigin::Local, Some(key_path))
                } else {
                    BorrowInfo::new(BorrowOrigin::Unknown, None)
                }
            }
            _ => BorrowInfo::new(BorrowOrigin::Unknown, None),
        }
    }

    fn param_origin(&self, symbol: Symbol, expr: &Expr) -> BorrowOrigin {
        let root_ty = root_expr(expr).and_then(|root| self.types.node_types.get(&root.id));
        let symbol_ty = self.symbol_ty(symbol);
        let expr_ty = self.types.node_types.get(&expr.id);
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
            ExprKind::Member(Some(receiver), label, _) => {
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

fn collect_block_binders(block: &Block, out: &mut FxHashSet<Symbol>) {
    for arg in &block.args {
        if let Ok(symbol) = arg.name.symbol() {
            out.insert(symbol);
        }
    }
    for node in &block.body {
        collect_node_binders(node, out);
    }
}

fn collect_inline_ir_exprs(nodes: &[Node], out: &mut FxHashSet<NodeID>) {
    for node in nodes {
        collect_inline_ir_node(node, out);
    }
}

fn collect_inline_ir_node(node: &Node, out: &mut FxHashSet<NodeID>) {
    match node {
        Node::Decl(decl) => match &decl.kind {
            DeclKind::Let { rhs, .. } => {
                if let Some(rhs) = rhs {
                    collect_inline_ir_expr(rhs, out);
                }
            }
            DeclKind::Func(func) => {
                collect_inline_ir_block(&func.body, out);
            }
            DeclKind::Method { func, .. } => collect_inline_ir_block(&func.body, out),
            DeclKind::Init { body, .. } => collect_inline_ir_block(body, out),
            DeclKind::Struct { body, .. }
            | DeclKind::Enum { body, .. }
            | DeclKind::Protocol { body, .. }
            | DeclKind::Extend { body, .. } => {
                for decl in &body.decls {
                    collect_inline_ir_node(&Node::Decl(decl.clone()), out);
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
        },
        Node::Stmt(stmt) => collect_inline_ir_stmt(&stmt.kind, out),
        Node::Expr(expr) => collect_inline_ir_expr(expr, out),
        Node::Block(block) => collect_inline_ir_block(block, out),
        Node::MatchArm(arm) => collect_inline_ir_block(&arm.body, out),
        Node::Func(func) => collect_inline_ir_block(&func.body, out),
        _ => {}
    }
}

fn collect_inline_ir_block(block: &Block, out: &mut FxHashSet<NodeID>) {
    collect_inline_ir_exprs(&block.body, out);
}

fn collect_inline_ir_stmt(stmt: &StmtKind, out: &mut FxHashSet<NodeID>) {
    match stmt {
        StmtKind::Expr(expr) | StmtKind::Return(Some(expr)) | StmtKind::Continue(Some(expr)) => {
            collect_inline_ir_expr(expr, out);
        }
        StmtKind::If(condition, then_block, else_block) => {
            collect_inline_ir_expr(condition, out);
            collect_inline_ir_block(then_block, out);
            if let Some(else_block) = else_block {
                collect_inline_ir_block(else_block, out);
            }
        }
        StmtKind::Assignment(lhs, rhs) => {
            collect_inline_ir_expr(lhs, out);
            collect_inline_ir_expr(rhs, out);
        }
        StmtKind::Loop(condition, body) => {
            if let Some(condition) = condition {
                collect_inline_ir_expr(condition, out);
            }
            collect_inline_ir_block(body, out);
        }
        StmtKind::For { iterable, body, .. } => {
            collect_inline_ir_expr(iterable, out);
            collect_inline_ir_block(body, out);
        }
        StmtKind::Handling { body, .. } => collect_inline_ir_block(body, out),
        StmtKind::Return(None) | StmtKind::Continue(None) | StmtKind::Break => {}
    }
}

fn collect_inline_ir_expr(expr: &Expr, out: &mut FxHashSet<NodeID>) {
    match &expr.kind {
        ExprKind::InlineIR(_) => {
            out.insert(expr.id);
        }
        ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
            for item in items {
                collect_inline_ir_expr(item, out);
            }
        }
        ExprKind::Unary(_, inner) | ExprKind::As(inner, _) => collect_inline_ir_expr(inner, out),
        ExprKind::Binary(lhs, _, rhs) => {
            collect_inline_ir_expr(lhs, out);
            collect_inline_ir_expr(rhs, out);
        }
        ExprKind::Block(block) => collect_inline_ir_block(block, out),
        ExprKind::Call {
            callee,
            args,
            trailing_block,
            ..
        } => {
            collect_inline_ir_expr(callee, out);
            for arg in args {
                collect_inline_ir_expr(&arg.value, out);
            }
            if let Some(block) = trailing_block {
                collect_inline_ir_block(block, out);
            }
        }
        ExprKind::CallEffect { args, .. } => {
            for arg in args {
                collect_inline_ir_expr(&arg.value, out);
            }
        }
        ExprKind::Member(Some(receiver), ..) => collect_inline_ir_expr(receiver, out),
        ExprKind::Func(func) => collect_inline_ir_block(&func.body, out),
        ExprKind::If(condition, then_block, else_block) => {
            collect_inline_ir_expr(condition, out);
            collect_inline_ir_block(then_block, out);
            collect_inline_ir_block(else_block, out);
        }
        ExprKind::Match(scrutinee, arms) => {
            collect_inline_ir_expr(scrutinee, out);
            for arm in arms {
                collect_inline_ir_block(&arm.body, out);
            }
        }
        ExprKind::RecordLiteral { fields, spread } => {
            if let Some(spread) = spread {
                collect_inline_ir_expr(spread, out);
            }
            for field in fields {
                collect_inline_ir_expr(&field.value, out);
            }
        }
        ExprKind::Incomplete(_)
        | ExprKind::LiteralInt(_)
        | ExprKind::LiteralFloat(_)
        | ExprKind::LiteralTrue
        | ExprKind::LiteralFalse
        | ExprKind::LiteralString(_)
        | ExprKind::Variable(_)
        | ExprKind::Constructor(_)
        | ExprKind::RowVariable(_)
        | ExprKind::Member(None, ..) => {}
    }
}

fn collect_node_binders(node: &Node, out: &mut FxHashSet<Symbol>) {
    match node {
        Node::Decl(decl) => match &decl.kind {
            DeclKind::Let { lhs, rhs, .. } => {
                for (_, symbol) in lhs.collect_binders() {
                    out.insert(symbol);
                }
                if let Some(rhs) = rhs {
                    collect_expr_binders(rhs, out);
                }
            }
            DeclKind::Func(func) => {
                collect_block_binders(&func.body, out);
            }
            DeclKind::Method { func, .. } => {
                collect_block_binders(&func.body, out);
            }
            DeclKind::Init { params, body, .. } => {
                for param in params {
                    if let Ok(symbol) = param.name.symbol() {
                        out.insert(symbol);
                    }
                }
                collect_block_binders(body, out);
            }
            DeclKind::Struct { body, .. }
            | DeclKind::Enum { body, .. }
            | DeclKind::Protocol { body, .. }
            | DeclKind::Extend { body, .. } => {
                for decl in &body.decls {
                    collect_node_binders(&Node::Decl(decl.clone()), out);
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
        },
        Node::Stmt(stmt) => collect_stmt_binders(&stmt.kind, out),
        Node::Expr(expr) => collect_expr_binders(expr, out),
        Node::Block(block) => collect_block_binders(block, out),
        Node::MatchArm(arm) => {
            for (_, symbol) in arm.pattern.collect_binders() {
                out.insert(symbol);
            }
            collect_block_binders(&arm.body, out);
        }
        Node::Func(func) => collect_block_binders(&func.body, out),
        _ => {}
    }
}

fn collect_stmt_binders(stmt: &StmtKind, out: &mut FxHashSet<Symbol>) {
    match stmt {
        StmtKind::Expr(expr) | StmtKind::Return(Some(expr)) | StmtKind::Continue(Some(expr)) => {
            collect_expr_binders(expr, out);
        }
        StmtKind::If(condition, then_block, else_block) => {
            collect_expr_binders(condition, out);
            collect_block_binders(then_block, out);
            if let Some(else_block) = else_block {
                collect_block_binders(else_block, out);
            }
        }
        StmtKind::Assignment(lhs, rhs) => {
            collect_expr_binders(lhs, out);
            collect_expr_binders(rhs, out);
        }
        StmtKind::Loop(condition, body) => {
            if let Some(condition) = condition {
                collect_expr_binders(condition, out);
            }
            collect_block_binders(body, out);
        }
        StmtKind::For {
            pattern,
            iterable,
            body,
        } => {
            for (_, symbol) in pattern.collect_binders() {
                out.insert(symbol);
            }
            collect_expr_binders(iterable, out);
            collect_block_binders(body, out);
        }
        StmtKind::Handling { body, .. } => collect_block_binders(body, out),
        StmtKind::Return(None) | StmtKind::Continue(None) | StmtKind::Break => {}
    }
}

fn collect_expr_binders(expr: &Expr, out: &mut FxHashSet<Symbol>) {
    match &expr.kind {
        ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_binders(item, out);
            }
        }
        ExprKind::Unary(_, inner) | ExprKind::As(inner, _) => collect_expr_binders(inner, out),
        ExprKind::Binary(lhs, _, rhs) => {
            collect_expr_binders(lhs, out);
            collect_expr_binders(rhs, out);
        }
        ExprKind::Block(block) => collect_block_binders(block, out),
        ExprKind::Call {
            callee,
            args,
            trailing_block,
            ..
        } => {
            collect_expr_binders(callee, out);
            for arg in args {
                collect_expr_binders(&arg.value, out);
            }
            if let Some(block) = trailing_block {
                collect_block_binders(block, out);
            }
        }
        ExprKind::CallEffect { args, .. } => {
            for arg in args {
                collect_expr_binders(&arg.value, out);
            }
        }
        ExprKind::Member(Some(receiver), ..) => collect_expr_binders(receiver, out),
        ExprKind::Func(func) => collect_block_binders(&func.body, out),
        ExprKind::If(condition, then_block, else_block) => {
            collect_expr_binders(condition, out);
            collect_block_binders(then_block, out);
            collect_block_binders(else_block, out);
        }
        ExprKind::Match(scrutinee, arms) => {
            collect_expr_binders(scrutinee, out);
            for arm in arms {
                for (_, symbol) in arm.pattern.collect_binders() {
                    out.insert(symbol);
                }
                collect_block_binders(&arm.body, out);
            }
        }
        ExprKind::RecordLiteral { fields, spread } => {
            if let Some(spread) = spread {
                collect_expr_binders(spread, out);
            }
            for field in fields {
                collect_expr_binders(&field.value, out);
            }
        }
        ExprKind::InlineIR(_)
        | ExprKind::Incomplete(_)
        | ExprKind::LiteralInt(_)
        | ExprKind::LiteralFloat(_)
        | ExprKind::LiteralTrue
        | ExprKind::LiteralFalse
        | ExprKind::LiteralString(_)
        | ExprKind::Variable(_)
        | ExprKind::Constructor(_)
        | ExprKind::RowVariable(_)
        | ExprKind::Member(None, ..) => {}
    }
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

fn point_kind(statement: &mir::Statement<'_>) -> PointKind {
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

fn terminator_successors(terminator: &mir::Terminator<'_>) -> Vec<mir::BlockId> {
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

fn map_drop_reason(reason: mir::DropReason) -> DropReason {
    match reason {
        mir::DropReason::ScopeExit => DropReason::ScopeExit,
        mir::DropReason::AssignmentReplace => DropReason::AssignmentReplace,
        mir::DropReason::EarlyExit => DropReason::EarlyExit,
    }
}

fn mir_drop_elaboration(kind: DropKind) -> mir::DropElaboration {
    match kind {
        DropKind::Static => mir::DropElaboration::Static,
        DropKind::Dead => mir::DropElaboration::Dead,
        DropKind::Conditional => mir::DropElaboration::Conditional,
        DropKind::Open => mir::DropElaboration::Open,
    }
}

fn classify_drop(key_path: &KeyPath, state: &DropState) -> DropKind {
    if state.moved_all.keys().any(|moved| moved == key_path) {
        return DropKind::Dead;
    }
    if state
        .moved_any
        .keys()
        .any(|moved| key_path.contains(moved) && moved != key_path)
    {
        return DropKind::Open;
    }
    if state
        .initialized_all
        .iter()
        .any(|live| live.contains(key_path))
        && !state.moved_any.keys().any(|moved| moved == key_path)
    {
        DropKind::Static
    } else if state
        .initialized_any
        .iter()
        .any(|live| live.contains(key_path))
    {
        DropKind::Conditional
    } else {
        DropKind::Dead
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        compiling::driver::{Driver, DriverConfig, Source},
        diagnostic::AnyDiagnostic,
        name_resolution::symbol::Symbol,
        ownership::{DropKind, DropReason, OwnershipOutput, PointKind},
    };
    use rustc_hash::FxHashMap;

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
        (typed.phase.ownership, typed.phase.types.display_names)
    }

    #[test]
    fn rejects_borrowed_field_in_owned_struct() {
        let errors = ownership_errors(
            "
            struct Bad {
                let path: Substring
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("cannot be stored in owned struct Bad.path")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_borrowed_payload_in_owned_enum() {
        let errors = ownership_errors(
            "
            enum Bad {
                case path(Substring)
            }
            ",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.contains("cannot be stored in owned enum Bad.path")),
            "{errors:?}"
        );
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
                .any(|error| error.contains("borrow provenance is unknown")),
            "{errors:?}"
        );
    }

    #[test]
    fn rejects_binding_record_containing_local_borrow() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let record = { sub: s.slice(0, 1) }
                record.sub.length
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
    fn rejects_binding_owned_generic_container_containing_borrow() {
        let errors = ownership_errors(
            "
            enum Maybe<T> {
                case some(T)
                case none
            }

            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let maybe = Maybe.some(s.slice(0, 1))
                0
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
                .any(|error| error.contains("borrow provenance is unknown")),
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
    fn allows_borrow_use_before_owner_move() {
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
    fn mutable_borrow_expires_after_last_borrow_use() {
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
    fn explicit_borrow_capture_keeps_owner_borrowed_while_closure_is_stored() {
        let errors = ownership_errors(
            "
            func bad() -> String {
                let s = \"hello\" + \" world\"
                let f = func [&s]() -> Int { s.length }
                return s
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
    fn explicit_mut_borrow_capture_blocks_reads_while_closure_is_stored() {
        let errors = ownership_errors(
            "
            func bad() -> Int {
                let s = \"hello\" + \" world\"
                let f = func [&mut s]() -> Int { s.length }
                s.length
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
                .any(|obligation| obligation.kind == DropKind::Static),
            "expected a static drop obligation for s, got {s_obligations:?}"
        );
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
                .any(|obligation| obligation.kind == DropKind::Conditional),
            "expected a conditional drop obligation for s, got {s_obligations:?}"
        );
        assert!(
            !s_obligations
                .iter()
                .any(|obligation| obligation.kind == DropKind::Dead),
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
