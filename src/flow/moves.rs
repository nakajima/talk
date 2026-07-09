//! Move checking: the state lattice (`MoveState`), the drop classification
//! rule, and the expression-level transfer functions the CFG engine
//! (`flow::cfg`) runs over each body's MIR blocks. Statement-embedded
//! blocks with no MIR blocks of their own (handler bodies, trailing
//! blocks) still walk tree-style through `walk_block`: branches check
//! against clones of the incoming state and merge at the join.
//!
//! What consumes a value is the legacy rule set verbatim: binding rhs,
//! assignment rhs, by-value call argument, by-value/`consuming` receiver,
//! return/continue value, discarded statement value, aggregate-literal
//! element, `[consuming]` capture. A consume only moves when the type needs
//! a drop (`GradeView::needs_drop`); copy types never move. Borrows arise
//! from `&`-typed parameters and borrow-containing bindings; they end at the
//! borrower's last use (`flow::liveness`).

use rustc_hash::{FxHashMap, FxHashSet};

use crate::compiling::module::ModuleId;
use crate::flow::OwnershipError;
use crate::node_id::NodeID;
use crate::typed_ast::{self, ExprKind};
use crate::types::TypeOutput;
use crate::types::ty::{Perm, Ty};

use super::drops::DropElaboration;
use super::grades::GradeView;
use super::liveness::Liveness;
use super::loans::{ActiveLoan, Origin, Provenance};
use super::place::Place;

#[derive(Clone, Default)]
pub(crate) struct MoveState {
    /// May-moved (or uninitialized) places — union at joins; drives
    /// use-after-move errors and the Conditional/Open drop kinds.
    pub(crate) moved: FxHashMap<Place, (NodeID, Ty)>,
    /// Must-moved places — intersection at joins; a must-moved place's
    /// scope-exit drop is Dead.
    moved_all: FxHashSet<Place>,
    /// Definitely-initialized places — intersection at joins.
    initialized_all: FxHashSet<Place>,
    /// Maybe-initialized places — union at joins.
    initialized_any: FxHashSet<Place>,
    /// Active NLL loans: borrower → owner at a permission.
    pub(crate) loans: Vec<ActiveLoan>,
    /// Where each borrowed value may reach.
    pub(crate) provenances: FxHashMap<Place, Provenance>,
    /// Borrowers whose owner moved or was reassigned while they were live.
    pub(crate) invalid_borrows: FxHashMap<Place, Place>,
    /// Roots that ARE borrowed values (borrow-typed bindings and params),
    /// with their permission.
    pub(crate) borrowed_roots: FxHashMap<crate::name_resolution::symbol::Symbol, Perm>,
    /// Shared-borrow roots: assignment through them is rejected.
    pub(crate) shared_borrow_roots: FxHashSet<crate::name_resolution::symbol::Symbol>,
    /// Closure values and their capture summaries (for escape checks and
    /// non-copy classification).
    pub(crate) closure_captures: FxHashMap<Place, super::captures::CaptureSummary>,
    /// Provenance of call-result temporaries, recorded at the Call
    /// statement (a method's borrowed result reaches its receiver's
    /// owners) and read where the consuming statement's `Temp` binds.
    pub(crate) temp_provenances: FxHashMap<u32, Provenance>,
}

impl MoveState {
    /// CFG-join: may-sets union, must-sets intersect (the legacy
    /// `MoveState`/`DropState` merge semantics in one place), reporting
    /// whether anything changed — the worklist's fixpoint test.
    pub(crate) fn join_from(&mut self, other: &MoveState) -> bool {
        let mut changed = false;
        for (place, fact) in &other.moved {
            if !self.moved.contains_key(place) {
                self.moved.insert(place.clone(), fact.clone());
                changed = true;
            }
        }
        let before = self.moved_all.len();
        self.moved_all
            .retain(|place| other.moved_all.contains(place));
        changed |= self.moved_all.len() != before;
        let before = self.initialized_all.len();
        self.initialized_all
            .retain(|place| other.initialized_all.contains(place));
        changed |= self.initialized_all.len() != before;
        let before = self.initialized_any.len();
        self.initialized_any
            .extend(other.initialized_any.iter().cloned());
        changed |= self.initialized_any.len() != before;
        for loan in &other.loans {
            if !self
                .loans
                .iter()
                .any(|mine| mine.borrower == loan.borrower && mine.owner == loan.owner)
            {
                self.loans.push(loan.clone());
                changed = true;
            }
        }
        for (place, provenance) in &other.provenances {
            if !self.provenances.contains_key(place) {
                self.provenances.insert(place.clone(), provenance.clone());
                changed = true;
            }
        }
        for (borrower, owner) in &other.invalid_borrows {
            if !self.invalid_borrows.contains_key(borrower) {
                self.invalid_borrows.insert(borrower.clone(), owner.clone());
                changed = true;
            }
        }
        for (root, kind) in &other.borrowed_roots {
            if !self.borrowed_roots.contains_key(root) {
                self.borrowed_roots.insert(*root, *kind);
                changed = true;
            }
        }
        let before = self.shared_borrow_roots.len();
        self.shared_borrow_roots
            .extend(other.shared_borrow_roots.iter().copied());
        changed |= self.shared_borrow_roots.len() != before;
        for (place, summary) in &other.closure_captures {
            if !self.closure_captures.contains_key(place) {
                self.closure_captures.insert(place.clone(), summary.clone());
                changed = true;
            }
        }
        for (temp, provenance) in &other.temp_provenances {
            match self.temp_provenances.get_mut(temp) {
                // Arms deliver to the same join temp: the temp's reach is
                // the union over delivering paths.
                Some(existing) => changed |= existing.union_with(provenance),
                None => {
                    self.temp_provenances.insert(*temp, provenance.clone());
                    changed = true;
                }
            }
        }
        changed
    }

    /// Re-initialize a place (binding or assignment target): the place and
    /// all its sub-places are live again.
    pub(crate) fn restore(&mut self, place: &Place) {
        self.moved.retain(|moved, _| !place.contains(moved));
        self.moved_all.retain(|moved| !place.contains(moved));
        self.initialized_all.insert(place.clone());
        self.initialized_any.insert(place.clone());
    }

    pub(crate) fn note_move(&mut self, place: Place, node: NodeID, ty: Ty) {
        self.moved_all.insert(place.clone());
        self.moved.insert(place, (node, ty));
    }

    /// A local left its scope: forget everything rooted at it.
    pub(crate) fn finish_local(&mut self, place: &Place) {
        self.moved.retain(|moved, _| !place.contains(moved));
        self.moved_all.retain(|moved| !place.contains(moved));
        self.initialized_all.retain(|init| !place.contains(init));
        self.initialized_any.retain(|init| !place.contains(init));
        self.loans.retain(|loan| loan.borrower.root != place.root);
        self.provenances
            .retain(|borrower, _| borrower.root != place.root);
        self.invalid_borrows
            .retain(|borrower, _| borrower.root != place.root);
        self.borrowed_roots.remove(&place.root);
        self.shared_borrow_roots.remove(&place.root);
        self.closure_captures
            .retain(|closure, _| closure.root != place.root);
    }

    /// The moved entry that makes `use_place` invalid, if any: a moved
    /// ancestor covers any use; a moved sub-place blocks whole-value
    /// (owned) uses only.
    pub(crate) fn moved_for_use(
        &self,
        use_place: &Place,
        use_is_owned: bool,
    ) -> Option<(&Place, &(NodeID, Ty))> {
        self.moved.iter().find(|(moved, _)| {
            moved.contains(use_place) || (use_is_owned && use_place.contains(moved))
        })
    }
}

/// The legacy `classify_drop` rule, verbatim: how a scheduled drop of
/// `place` lowers given the state at the drop point.
pub(crate) fn classify(place: &Place, state: &MoveState) -> DropElaboration {
    if state.moved_all.contains(place) {
        return DropElaboration::Dead;
    }
    if state
        .moved
        .keys()
        .any(|moved| place.contains(moved) && moved != place)
    {
        return DropElaboration::Open;
    }
    if state
        .initialized_all
        .iter()
        .any(|init| init.contains(place))
        && !state.moved.contains_key(place)
    {
        return DropElaboration::Static;
    }
    if state
        .initialized_any
        .iter()
        .any(|init| init.contains(place))
    {
        return DropElaboration::Conditional;
    }
    DropElaboration::Dead
}

/// The per-body checker context `enter_body`/`exit_body` swap (mirroring
/// `check_func`'s save/restore).
pub(crate) struct BodyContext {
    scopes: Vec<ScopeFrame>,
    liveness: Liveness,
    borrowed_params: FxHashSet<crate::name_resolution::symbol::Symbol>,
    param_tys: FxHashMap<crate::name_resolution::symbol::Symbol, Ty>,
    /// Temp numbering restarts per body; the consumed set must too.
    consumed_temps: rustc_hash::FxHashSet<u32>,
    ret_is_borrow: bool,
}

/// One scope's tracked locals, in declaration order.
struct ScopeFrame {
    locals: Vec<ScopeLocal>,
}

#[derive(Clone)]
struct ScopeLocal {
    symbol: crate::name_resolution::symbol::Symbol,
    ty: Ty,
}

pub(crate) struct MoveChecker<'a> {
    pub(crate) types: &'a TypeOutput,
    pub(crate) grades: GradeView<'a>,
    pub(crate) module_id: ModuleId,
    pub(crate) errors: Vec<(OwnershipError, NodeID)>,
    reported: FxHashSet<(NodeID, String)>,
    /// Enclosing scopes of the body being walked, outermost first.
    scopes: Vec<ScopeFrame>,
    /// Temps whose values were consumed (ownership transferred) by some
    /// statement — `TemporaryEnd` candidates for them classify `Dead`.
    /// Consumption of a temp is static per site (its single read either
    /// moves or borrows), so a plain set suffices; filled across the
    /// fixpoint/record passes, complete before checked facts are projected.
    pub(crate) consumed_temps: rustc_hash::FxHashSet<u32>,
    /// Borrower liveness for the body being walked (per body; swapped on
    /// nested-body entry like the scope stack).
    liveness: Liveness,
    /// `&`-typed (borrow-containing) parameters of the current body.
    pub(crate) borrowed_params: FxHashSet<crate::name_resolution::symbol::Symbol>,
    /// Whether the current body's declared return type is a borrow: its
    /// returns borrow (provenance-checked) instead of consuming, even when
    /// the returned expression's own type is owned.
    pub(crate) ret_is_borrow: bool,
    /// Parameter types of the current body (for borrowed-root queries).
    pub(crate) param_tys: FxHashMap<crate::name_resolution::symbol::Symbol, Ty>,
    /// Which parameter indices a free function's returned borrow reaches.
    pub(crate) return_reach: FxHashMap<crate::name_resolution::symbol::Symbol, Vec<usize>>,
    /// Expressions whose use consumes their place.
    pub(crate) consumed: FxHashSet<NodeID>,
    /// Expressions that clone instead of moving: CheapClone values
    /// extracted from a borrow (tier 2 — lowering retains the buffers).
    pub(crate) auto_clones: FxHashSet<NodeID>,
    /// Locals to install in the NEXT pushed scope frame: owned by-value
    /// parameters (their drops ride the callee) and match-arm payload
    /// binders (scoped to the arm body).
    pending_locals: Vec<ScopeLocal>,
    /// Editor-facing facts (inlay hints, hover), accumulated during the walk.
    pub(crate) facts: super::FlowFacts,
    /// Global → the global that borrows it. A borrow-wrapping global is
    /// legal when its loans are rooted in other globals; the owners recorded
    /// here become immutable program-wide (see `check_flow`'s post-pass).
    pub(crate) global_borrows:
        FxHashMap<crate::name_resolution::symbol::Symbol, crate::name_resolution::symbol::Symbol>,
    /// Assignments to globals made inside function bodies: cross-procedural
    /// writes the per-body NLL walk cannot see.
    pub(crate) global_writes: Vec<(NodeID, crate::name_resolution::symbol::Symbol)>,
    /// Nesting depth of function bodies below the file's top level.
    pub(crate) fn_depth: usize,
    /// Whether `error` reports (the CFG engine reports only on its final,
    /// converged pass; the tree walk's errors are superseded by it).
    pub(crate) report_errors: bool,
    /// Whether the walk records persistent side effects (facts, consume /
    /// auto-clone flags, drop schedules): true for the tree walk, false for
    /// every CFG-engine walk, whose repeated visits would duplicate them.
    pub(crate) recording: bool,
    /// Runtime ownership transfers produced by the statement/terminator
    /// currently being recorded. Logical consumes that do not transfer
    /// runtime ownership (notably effect performs) suppress this collection.
    runtime_moves: Option<Vec<Place>>,
    runtime_moves_enabled: bool,
}

impl<'a> MoveChecker<'a> {
    pub(crate) fn new(types: &'a TypeOutput, module_id: ModuleId) -> Self {
        MoveChecker {
            types,
            grades: GradeView::new(types),
            module_id,
            errors: vec![],
            reported: FxHashSet::default(),
            scopes: vec![],
            liveness: Liveness::default(),
            consumed_temps: rustc_hash::FxHashSet::default(),
            borrowed_params: FxHashSet::default(),
            ret_is_borrow: false,
            param_tys: FxHashMap::default(),
            return_reach: FxHashMap::default(),
            consumed: FxHashSet::default(),
            auto_clones: FxHashSet::default(),
            pending_locals: vec![],
            facts: super::FlowFacts::default(),
            global_borrows: FxHashMap::default(),
            global_writes: vec![],
            fn_depth: 0,
            report_errors: true,
            recording: true,
            runtime_moves: None,
            runtime_moves_enabled: true,
        }
    }

    pub(crate) fn begin_runtime_moves(&mut self) {
        self.runtime_moves = Some(Vec::new());
    }

    pub(crate) fn take_runtime_moves(&mut self) -> Vec<Place> {
        self.runtime_moves.take().unwrap_or_default()
    }

    pub(crate) fn with_runtime_moves_suppressed<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let old = self.runtime_moves_enabled;
        self.runtime_moves_enabled = false;
        let result = f(self);
        self.runtime_moves_enabled = old;
        result
    }

    pub(crate) fn record_runtime_move(&mut self, place: &Place) {
        if self.recording
            && self.runtime_moves_enabled
            && let Some(moves) = &mut self.runtime_moves
            && !moves.iter().any(|seen| seen == place)
        {
            moves.push(place.clone());
        }
    }

    pub(crate) fn error(&mut self, error: OwnershipError, node: NodeID) {
        if !self.report_errors {
            return;
        }
        if self.reported.insert((node, error.to_string())) {
            self.errors.push((error, node));
        }
    }

    // ----- Bodies -----------------------------------------------------------

    /// Seed each parameter: a borrow-containing parameter starts with
    /// caller-owned (`BorrowedParam`) provenance, so returning it is legal
    /// and moving out of it is not.
    pub(crate) fn seed_params(
        &mut self,
        params: &[typed_ast::Parameter],
        func_ty: Option<&Ty>,
        state: &mut MoveState,
    ) {
        let ty_params = func_ty.and_then(func_params).unwrap_or_default();
        for (index, param) in params.iter().enumerate() {
            let Ok(symbol) = param.name.symbol() else {
                continue;
            };
            let Some(ty) = param
                .ty
                .clone()
                .or_else(|| self.types.node_types.get(&param.id).cloned())
                .or_else(|| ty_params.get(index).cloned())
            else {
                continue;
            };
            self.param_tys.insert(symbol, ty.clone());
            if !self.grades.contains_borrowed(&ty) {
                // A consumed by-value argument's drop rides the callee: the
                // parameter is a scope local of the body. (`'heap`-carrying
                // parameters are exempt — params neither acquire nor
                // release the region ledger.)
                let generic = matches!(ty, Ty::Param(_) | Ty::Proj(..));
                if (generic || self.grades.needs_drop(&ty)) && !self.grades.contains_object(&ty) {
                    self.pending_locals.push(ScopeLocal {
                        symbol,
                        ty: ty.clone(),
                    });
                    // Parameters arrive initialized (else the exit drop
                    // classifies Dead).
                    state.restore(&Place::root(symbol));
                }
                continue;
            }
            self.borrowed_params.insert(symbol);
            // A borrowed parameter's storage arrives initialized like any
            // other: without this, an `AssignmentReplace` drop for one of
            // its fields (`self.storage = fresh` in a `mut func`) classifies
            // Dead and the replaced value leaks. No scope-exit candidates
            // exist for borrows, so this only feeds replace classification.
            state.restore(&Place::root(symbol));
            let place = Place::root(symbol);
            let kind = match &ty {
                Ty::Borrow(perm, _) => *perm,
                _ => Perm::Shared,
            };
            state.provenances.insert(
                place.clone(),
                Provenance::direct(Origin::BorrowedParam, None, kind),
            );
            let _ = &place;
            state.borrowed_roots.insert(symbol, kind);
            if !kind.is_exclusive() {
                state.shared_borrow_roots.insert(symbol);
            }
        }
    }

    /// A returned value: borrow-containing returns validate their provenance
    /// (tier 1: parameter-derived is fine; owned/unknown are errors); owned
    /// returns consume (which also checks move-out-of-borrowed and closure
    /// escapes).
    pub(crate) fn check_return_value(&mut self, expr: &typed_ast::Expr, state: &mut MoveState) {
        // A borrow-typed function return is a borrow even when the
        // returned expression's own type is owned (`-> &mut Storage {
        // self.storage }`): consuming it would extract — a tier-2 clone
        // whose retain nothing ever releases.
        if self.ret_is_borrow || self.grades.contains_borrowed(&expr.ty) {
            // Embedded rvalue temps are still delivered: unmarked, their
            // `TemporaryEnd` candidates would classify live and free the
            // returned value out from under the caller.
            self.check_return_provenance(expr, state);
            self.mark_rvalue_temps_consumed(expr);
            self.walk_expr(expr, state);
        } else {
            self.consume_expr(expr, state);
        }
    }

    pub(crate) fn check_let(
        &mut self,
        lhs: &typed_ast::Pattern,
        annotation: Option<&crate::node_kinds::type_annotation::TypeAnnotation>,
        rhs: Option<&typed_ast::Expr>,
        state: &mut MoveState,
    ) {
        // A single-binder let's type comes from its `&`/`&mut` annotation
        // (the legacy `binding_expected_ty`), else its rhs; destructuring
        // binders carry their own node types.
        use crate::node_kinds::type_annotation::TypeAnnotationKind;
        let annotation_borrow = match annotation.map(|annotation| &annotation.kind) {
            Some(TypeAnnotationKind::Borrow { mutable: true, .. }) => Some(Perm::Exclusive),
            Some(TypeAnnotationKind::Borrow { mutable: false, .. }) => Some(Perm::Shared),
            _ => None,
        };
        let whole_binding_ty = match (&lhs.kind, rhs) {
            (typed_ast::PatternKind::Bind(_), Some(rhs)) => match annotation_borrow {
                Some(perm) => Some(Ty::Borrow(perm, Box::new(rhs.ty.clone()))),
                None => Some(rhs.ty.clone()),
            },
            _ => None,
        };
        let single_binder = lhs.collect_binders().len() == 1;

        // Borrow-containing single binding: provenance install, not a move.
        let mut handled_rhs = false;
        if let Some(rhs) = rhs
            && single_binder
            && let Some((binder_id, binder)) = lhs.collect_binders().first().copied()
        {
            let binder_ty = match annotation_borrow {
                Some(_) => whole_binding_ty.clone().unwrap_or(Ty::Error),
                None => self
                    .types
                    .node_types
                    .get(&binder_id)
                    .cloned()
                    .or_else(|| whole_binding_ty.clone())
                    .unwrap_or(Ty::Error),
            };
            if self.grades.contains_borrowed(&binder_ty) && !self.grades.contains_object(&binder_ty)
            {
                let mut provenance = self.expr_provenance(rhs, state);
                // A `&`/`&mut` binding borrows its sources at the annotated
                // permission.
                if let Ty::Borrow(perm, _) = &binder_ty {
                    provenance = provenance.with_kind(*perm);
                }
                self.validate_local_provenance(binder_id, &binder_ty, &provenance);
                self.walk_expr(rhs, state);
                self.install_provenance(
                    binder_id,
                    Place::root(binder),
                    &binder_ty,
                    provenance,
                    state,
                );
                handled_rhs = true;
            } else if let ExprKind::Func(func) = &rhs.kind {
                // Binding a closure: check it in bound (non-escaping)
                // context, remember its summary for non-copy/escape
                // classification, and apply its borrow captures with the
                // binder as the borrower.
                let summary = self.check_closure(func, state, EscapeContext::Bound);
                let binder_place = Place::root(binder);
                self.apply_borrow_captures(binder_place.clone(), binder_id, &summary, state);
                state.closure_captures.insert(binder_place, summary);
                handled_rhs = true;
            }
        }
        if !handled_rhs && let Some(rhs) = rhs {
            self.consume_expr(rhs, state);
        }

        for (id, binder) in lhs.collect_binders() {
            let ty = self
                .types
                .node_types
                .get(&id)
                .cloned()
                .or_else(|| whole_binding_ty.clone())
                .unwrap_or(Ty::Error);
            if let Some(frame) = self.scopes.last_mut() {
                frame.locals.push(ScopeLocal {
                    symbol: binder,
                    ty: ty.clone(),
                });
            }
            let place = Place::root(binder);
            if rhs.is_some() {
                state.restore(&place);
            } else {
                // `let s: String` with no initializer: the binder starts
                // uninitialized, which the move lattice models as moved.
                state.note_move(place, id, ty);
            }
        }
    }

    // ----- Drop scheduling ----------------------------------------------------

    pub(crate) fn ty_is_linear(&self, ty: &Ty) -> bool {
        use crate::types::catalog::Grade;
        matches!(ty, Ty::Nominal(symbol, _)
            if self.types.catalog.grade_of(*symbol) == Grade::Linear)
    }

    // ----- Statement/node walk ----------------------------------------------

    // ----- CFG-engine support (flow::cfg) --------------------------------------

    /// Prune loans whose borrower is dead after `id` (the engine's
    /// per-statement equivalent of `prune_after`).
    pub(crate) fn prune_at(&mut self, state: &mut MoveState, id: NodeID) {
        state.prune_dead_loans(&self.liveness, id);
    }

    /// Swap in a body's checking context (fresh scopes/liveness/params, the
    /// same swaps `check_func` performs), returning the outer context.
    /// `is_function` distinguishes function bodies from a file's top level
    /// (which is not nested below it).
    pub(crate) fn enter_body(&mut self, liveness: Liveness, is_function: bool) -> BodyContext {
        let outer = BodyContext {
            scopes: std::mem::take(&mut self.scopes),
            liveness: std::mem::replace(&mut self.liveness, liveness),
            borrowed_params: std::mem::take(&mut self.borrowed_params),
            param_tys: std::mem::take(&mut self.param_tys),
            consumed_temps: std::mem::take(&mut self.consumed_temps),
            ret_is_borrow: std::mem::take(&mut self.ret_is_borrow),
        };
        if is_function {
            self.fn_depth += 1;
        }
        outer
    }

    pub(crate) fn exit_body(&mut self, outer: BodyContext, is_function: bool) {
        if is_function {
            self.fn_depth -= 1;
        }
        self.scopes = outer.scopes;
        self.liveness = outer.liveness;
        self.borrowed_params = outer.borrowed_params;
        self.param_tys = outer.param_tys;
        self.consumed_temps = outer.consumed_temps;
        self.ret_is_borrow = outer.ret_is_borrow;
    }

    /// Open the body's root scope frame, adopting any pending locals the
    /// param seeding registered.
    pub(crate) fn push_body_frame(&mut self) {
        let pending = std::mem::take(&mut self.pending_locals);
        self.scopes.push(ScopeFrame { locals: pending });
    }

    pub(crate) fn pop_body_frame(&mut self) {
        self.scopes.pop();
    }

    /// Register a storage-live local with the innermost frame so root-type
    /// lookups see it (the engine's counterpart of `check_let`'s
    /// registration; `let` binders arrive here too, harmlessly twice).
    pub(crate) fn register_scope_local(
        &mut self,
        symbol: crate::name_resolution::symbol::Symbol,
        ty: Ty,
    ) {
        let Some(frame) = self.scopes.last_mut() else {
            return;
        };
        if frame.locals.iter().any(|local| local.symbol == symbol) {
            return;
        }
        frame.locals.push(ScopeLocal { symbol, ty });
    }

    pub(crate) fn check_assignment(
        &mut self,
        _stmt_id: NodeID,
        lhs: &typed_ast::Expr,
        rhs: &typed_ast::Expr,
        state: &mut MoveState,
    ) {
        // Assignment through a shared borrow is rejected — except through
        // `'heap` references, which mutate in place by design.
        if let Some((receiver_root, receiver_ty)) =
            self.shared_borrow_assignment_receiver(lhs, state)
            && !self.object_receiver(&receiver_ty)
        {
            let error = OwnershipError::AssignThroughSharedBorrow {
                name: render_symbol(receiver_root, self.types),
                ty: receiver_ty.render_mono(),
            };
            self.error(error, lhs.id);
        }

        if let Some(place) = self.place(lhs) {
            // A write to a global from inside a function body: the
            // per-body NLL walk cannot see whether a global borrows it, so
            // record it for `check_flow`'s cross-procedural post-pass.
            if self.recording
                && self.fn_depth > 0
                && matches!(
                    place.root,
                    crate::name_resolution::symbol::Symbol::Global(_)
                )
            {
                self.global_writes.push((lhs.id, place.root));
            }
            // Reassigning a borrowed binding re-derives its provenance.
            if self.grades.contains_borrowed(&lhs.ty)
                && !self.grades.contains_object(&lhs.ty)
                && place.fields.is_empty()
            {
                let mut provenance = self.expr_provenance(rhs, state);
                if let Ty::Borrow(perm, _) = &lhs.ty {
                    provenance = provenance.with_kind(*perm);
                }
                self.validate_local_provenance(lhs.id, &lhs.ty, &provenance);
                self.walk_expr(rhs, state);
                state.restore(&place);
                self.install_provenance(lhs.id, place, &lhs.ty, provenance, state);
                return;
            }

            self.consume_expr(rhs, state);
            // Writing through a moved root is a use of the moved value
            // (`person.name = x` after `person` moved), but assigning to the
            // moved place itself re-initializes it.
            let root = Place::root(place.root);
            if let Some((moved, (_, ty))) = state.moved_for_use(&root, false)
                && !place.contains(moved)
            {
                let error = OwnershipError::UseAfterMove {
                    name: render_place(moved, self.types),
                    ty: ty.render_mono(),
                };
                self.error(error, lhs.id);
            }
            // The old value is replaced: drop it first (classified at the
            // pre-assignment state, so a moved-out place drops Dead), and any
            // borrows of it are invalidated.
            if self.grades.needs_drop(&lhs.ty) || self.grades.contains_object(&lhs.ty) {
                state.invalidate_borrows_of(&place);
            }
            state.restore(&place);
        } else {
            self.consume_expr(rhs, state);
            self.walk_expr(lhs, state);
        }
    }

    /// The shared-borrow receiver an assignment writes through, if any:
    /// `self.n = …` in a `func` (shared self), or any member chain whose
    /// root is a shared borrow.
    fn shared_borrow_assignment_receiver(
        &self,
        lhs: &typed_ast::Expr,
        state: &MoveState,
    ) -> Option<(crate::name_resolution::symbol::Symbol, Ty)> {
        let receiver = match &lhs.kind {
            ExprKind::Member(Some(receiver), _) | ExprKind::Proj(receiver, ..) => receiver,
            _ => return None,
        };
        let mut current = receiver.as_ref();
        loop {
            match &current.kind {
                ExprKind::Variable(name) => {
                    let symbol = name.symbol().ok()?;
                    if state.shared_borrow_roots.contains(&symbol)
                        || matches!(current.ty, Ty::Borrow(perm, _) if !perm.is_exclusive())
                    {
                        return Some((symbol, current.ty.clone()));
                    }
                    return None;
                }
                ExprKind::Member(Some(inner), _) | ExprKind::Proj(inner, ..) => {
                    if matches!(current.ty, Ty::Borrow(perm, _) if !perm.is_exclusive()) {
                        let root = self.place(current).map(|place| place.root)?;
                        return Some((root, current.ty.clone()));
                    }
                    current = inner.as_ref();
                }
                _ => return None,
            }
        }
    }

    // ----- Expression walk ---------------------------------------------------

    /// Walk an expression whose value is consumed by its context: a place is
    /// moved (if owned), an aggregate literal consumes its elements, and
    /// anything else evaluates normally (its interior consume sites are its
    /// own).
    pub(crate) fn consume_expr(&mut self, expr: &typed_ast::Expr, state: &mut MoveState) {
        self.check_object_boundaries(expr);
        // A call's effects (receiver borrows, argument consumption) rode
        // its own Call/Perform statement; its result is an rvalue with no
        // place effects.
        if matches!(
            expr.kind,
            ExprKind::Call { .. } | ExprKind::CallEffect { .. }
        ) {
            return;
        }
        // A closure value consumed by its context escapes the frame.
        if let ExprKind::Func(func) = &expr.kind {
            self.check_closure(func, state, EscapeContext::Escaping);
            return;
        }
        if let Some(place) = self.place(expr) {
            if let Some(summary) = state.closure_captures.get(&place).cloned() {
                self.check_escaping_summary(expr.id, &summary);
            }
            self.move_place(expr, place, state);
            return;
        }
        match &expr.kind {
            ExprKind::Tuple(items)
            | ExprKind::LiteralArray(items)
            | ExprKind::Con { args: items, .. } => {
                for item in items {
                    self.consume_expr(item, state);
                }
            }
            ExprKind::RecordLiteral { fields, spread } => {
                for field in fields {
                    self.consume_expr(&field.value, state);
                }
                if let Some(spread) = spread {
                    self.consume_expr(spread, state);
                }
            }
            // Opaque: their effects (and the arms' value consumption)
            // already rode the enclosing body's blocks.
            ExprKind::Block(_) | ExprKind::Match(..) => {}
            // Consuming a temp takes the embedded call/construct result:
            // its `TemporaryEnd` candidate classifies `Dead`.
            ExprKind::Temp(temp) => {
                self.consumed_temps.insert(*temp);
            }
            _ => self.walk_expr(expr, state),
        }
    }

    /// A call-site ownership marker (ADR 0018). Returns true when the
    /// marker fully handled the argument; false hands it back to the
    /// default per-parameter rules.
    fn apply_argument_marker(
        &mut self,
        mode: crate::node_kinds::call_arg::ArgMode,
        param: Option<&Ty>,
        value: &typed_ast::Expr,
        state: &mut MoveState,
    ) -> bool {
        use crate::node_kinds::call_arg::ArgMode;
        let param_perm = match param {
            Some(Ty::Borrow(perm, _)) => Some(*perm),
            _ => None,
        };
        match mode {
            ArgMode::Borrow => match param_perm {
                Some(perm) if !perm.is_exclusive() => false,
                Some(_) => self.argument_marker_error(
                    "borrow",
                    "the parameter needs exclusive (`mut`) access",
                    value,
                    state,
                ),
                None => self.argument_marker_error(
                    "borrow",
                    "the parameter takes ownership; use `consume` or `copy`",
                    value,
                    state,
                ),
            },
            ArgMode::Mut => match param_perm {
                Some(perm) if perm.is_exclusive() => false,
                _ => self.argument_marker_error("mut", "the parameter is not `mut`", value, state),
            },
            ArgMode::Consume => {
                if param_perm.is_some() {
                    return self.argument_marker_error(
                        "consume",
                        "the parameter borrows; it does not take ownership",
                        value,
                        state,
                    );
                }
                self.consume_expr_forced(value, state);
                true
            }
            ArgMode::Copy => {
                if param_perm.is_some() {
                    return self.argument_marker_error(
                        "copy",
                        "the parameter borrows; nothing is consumed",
                        value,
                        state,
                    );
                }
                if self.place(value).is_none() {
                    // An rvalue is already owned: nothing to copy, the
                    // default consumption applies.
                    return false;
                }
                let ty = value.ty.clone();
                if self.grades.is_copy(&ty) {
                    self.walk_expr(value, state);
                    return true;
                }
                if self.grades.is_cheap_clone(&ty) || matches!(ty, Ty::Param(_) | Ty::Proj(..)) {
                    if self.recording {
                        self.auto_clones.insert(value.id);
                    }
                    self.walk_expr(value, state);
                    return true;
                }
                let reason = format!("{} cannot be copied", ty.render_mono());
                self.argument_marker_error("copy", &reason, value, state)
            }
        }
    }

    fn argument_marker_error(
        &mut self,
        marker: &str,
        reason: &str,
        value: &typed_ast::Expr,
        state: &mut MoveState,
    ) -> bool {
        let error = OwnershipError::ArgumentMarker {
            marker: marker.into(),
            reason: reason.into(),
        };
        self.error(error, value.id);
        self.walk_expr(value, state);
        true
    }

    /// `consume`-marked argument: like `consume_expr`, but a place moves
    /// even when a later use is live (no liveness auto-clone) and a
    /// borrowed extraction never falls back to a tier-2 clone.
    /// A marked `for` source is a real move: both `consume` and `mut`
    /// reject sources reached through borrows (the silent clone would
    /// mutate or drain a copy); `consume` additionally rejects sources
    /// used again after the loop, while `mut` restores the place at loop
    /// end so later uses are fine. Rvalue sources are already owned;
    /// nothing to check.
    pub(crate) fn check_marked_for_source(
        &mut self,
        mode: crate::node_kinds::call_arg::ArgMode,
        rhs: &typed_ast::Expr,
    ) {
        use crate::node_kinds::call_arg::ArgMode;
        let marker = match mode {
            ArgMode::Consume => "consume",
            ArgMode::Mut => "mut",
            ArgMode::Borrow | ArgMode::Copy => return,
        };
        let Some(place) = self.place(rhs) else { return };
        if let Some(Ty::Borrow(..)) = self.root_ty(place.root) {
            let error = OwnershipError::ArgumentMarker {
                marker: marker.into(),
                reason: "cannot take a value reached through a borrow".into(),
            };
            self.error(error, rhs.id);
            return;
        }
        if mode == ArgMode::Consume
            && !self.grades.is_copy(&rhs.ty)
            && !self.liveness.dead_after(rhs.id, place.root)
        {
            let error = OwnershipError::ArgumentMarker {
                marker: marker.into(),
                reason: "the value is used again later".into(),
            };
            self.error(error, rhs.id);
        }
    }

    fn consume_expr_forced(&mut self, expr: &typed_ast::Expr, state: &mut MoveState) {
        if let Some(place) = self.place(expr) {
            if let Some(summary) = state.closure_captures.get(&place).cloned() {
                self.check_escaping_summary(expr.id, &summary);
            }
            self.move_place_with(expr, place, state, true);
            return;
        }
        self.consume_expr(expr, state);
    }

    /// Walk an expression for its uses (reads); consume sites inside it
    /// (call arguments, receivers, aggregate elements) apply their own rules.
    pub(crate) fn walk_expr(&mut self, expr: &typed_ast::Expr, state: &mut MoveState) {
        self.check_object_boundaries(expr);
        if let Some(place) = self.place(expr) {
            self.check_use(expr.id, &expr.ty, &place, false, state);
            return;
        }
        match &expr.kind {
            // Opaque — the Call/Perform statement transfer applies their
            // effects directly.
            ExprKind::Call { .. } | ExprKind::CallEffect { .. } => {}
            ExprKind::Member(Some(receiver), _) | ExprKind::Proj(receiver, ..) => {
                self.walk_expr(receiver, state)
            }
            ExprKind::Member(None, _) | ExprKind::Variable(_) | ExprKind::Constructor(_) => {}
            ExprKind::Tuple(items)
            | ExprKind::LiteralArray(items)
            | ExprKind::Con { args: items, .. } => {
                for item in items {
                    self.consume_expr(item, state);
                }
            }
            ExprKind::RecordLiteral { fields, spread } => {
                for field in fields {
                    self.consume_expr(&field.value, state);
                }
                if let Some(spread) = spread {
                    self.consume_expr(spread, state);
                }
            }
            ExprKind::Block(_) | ExprKind::Match(..) => {}
            ExprKind::Func(func) => {
                self.check_closure(func, state, EscapeContext::Bound);
            }
            ExprKind::InlineIR(ir) => {
                for bind in &ir.binds {
                    // A generic-typed value handed to raw IR transfers
                    // ownership (`_store<Element>`'s value): the
                    // implicit-copy rule inserts the retain. Concrete
                    // binds stay reads.
                    if matches!(bind.ty, Ty::Param(_) | Ty::Proj(..)) {
                        self.consume_expr(bind, state);
                    } else {
                        self.walk_expr(bind, state);
                    }
                }
            }
            ExprKind::Lit(_) | ExprKind::Temp(_) => {}
        }
    }

    pub(crate) fn check_call(
        &mut self,
        callee: &typed_ast::Expr,
        args: &[typed_ast::CallArg],
        state: &mut MoveState,
    ) {
        // Receiver: a borrowed self parameter (from the method's scheme, which
        // is self-first) borrows; a by-value/`consuming` self consumes. A
        // member that is a stored field being *called* is a closure-typed
        // field, not a method — its receiver reads.
        let mut value_params: Option<Vec<Ty>> = None;
        if let ExprKind::Proj(receiver, ..) = &callee.kind {
            // A closure-typed stored field being called: the read is the
            // projection's own; a non-place receiver evaluates as a value.
            if self.place(callee).is_some() {
                self.walk_expr(callee, state);
            } else {
                self.consume_expr(receiver, state);
            }
        } else if let ExprKind::Member(Some(receiver), _) = &callee.kind
            && matches!(receiver.kind, ExprKind::Constructor(_))
        {
            // Protocol-static / type-static form (`Add.add(a, rhs)` — the
            // operator desugar's shape): the head names a type, not a
            // value. Every argument aligns with the FULL parameter list,
            // self included — stripping the first param here consumed
            // borrowed receivers.
            value_params = self.member_callable_params(callee);
        } else if let ExprKind::Member(Some(receiver), _) = &callee.kind {
            let method_params = self.member_callable_params(callee);
            let self_param = method_params.as_ref().and_then(|params| params.first());
            match self_param {
                Some(Ty::Borrow(perm, inner)) => {
                    let is_object = self.grades.is_object(inner);
                    let perm = *perm;
                    self.walk_expr(receiver, state);
                    if !is_object && let Some(receiver_place) = self.place(receiver) {
                        if perm.is_exclusive() {
                            self.check_exclusive_root(receiver.id, &receiver_place);
                        }
                        let owner = state.loan_owner_for(&receiver_place);
                        let perm = state.rebased_perm(&receiver_place, perm);
                        self.check_borrow_conflicts(
                            receiver.id,
                            &owner,
                            perm,
                            Some(&receiver_place),
                            state,
                        );
                        if perm.is_exclusive() {
                            state.invalidate_borrows_of_except(&owner, Some(&receiver_place));
                        }
                    }
                }
                _ => self.consume_expr(receiver, state),
            }
            value_params = method_params.map(|params| params.get(1..).unwrap_or(&[]).to_vec());
        } else {
            self.walk_expr(callee, state);
        }
        let params = value_params.unwrap_or_else(|| callee_params(callee));

        // Constructor args flow into the constructed value: they consume
        // unless the result is trivially copyable (then nothing owns
        // anything). Gating on copy — not needs-drop — routes generic and
        // handle-carrying payloads through the ledger too.
        let borrowed_constructor = matches!(callee.kind, ExprKind::Constructor(_))
            && self.grades.is_copy(&result_ty(callee));

        for (index, arg) in args.iter().enumerate() {
            let param = params.get(index);
            if let Some(mode) = arg.mode
                && self.apply_argument_marker(mode, param, &arg.value, state)
            {
                continue;
            }
            match param {
                Some(Ty::Borrow(perm, inner)) => {
                    let is_object = self.grades.is_object(inner);
                    let perm = *perm;
                    self.walk_expr(&arg.value, state);
                    if !is_object && let Some(arg_place) = self.place(&arg.value) {
                        if perm.is_exclusive() {
                            self.check_exclusive_root(arg.value.id, &arg_place);
                        }
                        let owner = state.loan_owner_for(&arg_place);
                        let perm = state.rebased_perm(&arg_place, perm);
                        self.check_borrow_conflicts(
                            arg.value.id,
                            &owner,
                            perm,
                            Some(&arg_place),
                            state,
                        );
                        if perm.is_exclusive() {
                            state.invalidate_borrows_of_except(&owner, Some(&arg_place));
                        }
                    } else if !is_object && perm.is_exclusive() && self.place(&arg.value).is_none()
                    {
                        // V1: a `mut` parameter writes back; a temporary
                        // has no home for the write.
                        let error = OwnershipError::ArgumentMarker {
                            marker: "mut".into(),
                            reason: "a `mut` parameter needs a mutable place to write back to"
                                .into(),
                        };
                        self.error(error, arg.value.id);
                    }
                }
                _ if borrowed_constructor => {
                    // Ledger rule B: place reads RETAIN into the region
                    // (the owner's scope-exit drop still runs), rvalues
                    // MOVE in — so any embedded call-result temp is
                    // consumed by the region and must not release at its
                    // full expression's end.
                    self.mark_rvalue_temps_consumed(&arg.value);
                    self.walk_expr(&arg.value, state)
                }
                _ => self.consume_expr(&arg.value, state),
            }
        }
    }

    /// Mark every call/construct temp inside an rvalue expression tree as
    /// consumed (its value moves into whatever owns the rvalue — a region
    /// acquire path takes it without a flow-level consume).
    fn mark_rvalue_temps_consumed(&mut self, expr: &typed_ast::Expr) {
        match &expr.kind {
            ExprKind::Temp(temp) => {
                self.consumed_temps.insert(*temp);
            }
            ExprKind::Tuple(items)
            | ExprKind::LiteralArray(items)
            | ExprKind::Con { args: items, .. } => {
                for item in items {
                    self.mark_rvalue_temps_consumed(item);
                }
            }
            ExprKind::RecordLiteral { fields, spread } => {
                for field in fields {
                    self.mark_rvalue_temps_consumed(&field.value);
                }
                if let Some(spread) = spread {
                    self.mark_rvalue_temps_consumed(spread);
                }
            }
            _ => {}
        }
    }

    /// The full self-first parameter list of a member call's method, from
    /// the resolved member's scheme (the callee expression's own type is the
    /// bound-method type with self already stripped).
    pub(crate) fn member_callable_params(&self, callee: &typed_ast::Expr) -> Option<Vec<Ty>> {
        use crate::types::output::MemberResolution;
        match callee.member_resolution.as_ref()? {
            MemberResolution::Direct(symbol) => self
                .types
                .schemes
                .get(symbol)
                .and_then(|scheme| func_params(&scheme.ty)),
            MemberResolution::ViaConformance { protocol, witness } => self
                .types
                .schemes
                .get(witness)
                .and_then(|scheme| func_params(&scheme.ty))
                .or_else(|| {
                    let (ExprKind::Member(_, label) | ExprKind::Proj(_, label, _)) = &callee.kind
                    else {
                        return None;
                    };
                    self.types
                        .catalog
                        .requirement_in_ref(protocol, &label.to_string())
                        .and_then(|(_, requirement)| self.types.schemes.get(&requirement.symbol))
                        .and_then(|scheme| func_params(&scheme.ty))
                }),
        }
    }

    // ----- Places, uses, moves ------------------------------------------------

    /// The type of a symbol visible in the current body: scope locals,
    /// then parameters, then top-level schemes.
    pub(crate) fn symbol_local_ty(
        &self,
        symbol: crate::name_resolution::symbol::Symbol,
    ) -> Option<Ty> {
        for frame in self.scopes.iter().rev() {
            for local in &frame.locals {
                if local.symbol == symbol {
                    return Some(local.ty.clone());
                }
            }
        }
        self.param_tys.get(&symbol).cloned().or_else(|| {
            self.types
                .schemes
                .get(&symbol)
                .map(|scheme| scheme.ty.clone())
        })
    }

    /// The declared/checked type of a place root, searching innermost
    /// scope locals first, then parameters, then top-level schemes.
    pub(crate) fn root_ty(&self, root: crate::name_resolution::symbol::Symbol) -> Option<Ty> {
        for scope in self.scopes.iter().rev() {
            if let Some(local) = scope.locals.iter().rev().find(|l| l.symbol == root) {
                return Some(local.ty.clone());
            }
        }
        self.param_tys.get(&root).cloned().or_else(|| {
            self.types
                .schemes
                .get(&root)
                .map(|scheme| scheme.ty.clone())
        })
    }

    /// Whether an assignment receiver is a `'heap` reference (directly or
    /// through a borrow).
    fn object_receiver(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Borrow(_, inner) => self.grades.is_object(inner),
            other => self.grades.is_object(other),
        }
    }

    /// v1 ledger boundaries: `'heap` values cannot enter existentials or
    /// raw-storage containers (both are invisible to the region scans).
    pub(crate) fn check_object_boundaries(&mut self, expr: &typed_ast::Expr) {
        self.check_boundaries(expr.id, &expr.ty, expr.existential_pack.as_ref());
    }

    /// The object-boundary rules on operand data: a `'heap` handle may not
    /// pack into an existential or ride a raw-storage container.
    pub(crate) fn check_boundaries(
        &mut self,
        node: NodeID,
        ty: &Ty,
        pack: Option<&crate::types::output::ExistentialPack>,
    ) {
        if let Some(pack) = pack
            && self.grades.contains_object(&pack.payload)
        {
            let error = OwnershipError::ObjectInExistential {
                ty: pack.payload.render_mono(),
            };
            self.error(error, node);
        }
        if let Ty::Nominal(symbol, args) = ty
            && !args.is_empty()
            && self.raw_storage_backed(*symbol)
        {
            for arg in args {
                if self.grades.contains_object(arg) {
                    let error = OwnershipError::ObjectInRawStorage {
                        container: ty.render_mono(),
                        ty: arg.render_mono(),
                    };
                    self.error(error, node);
                    break;
                }
            }
        }
    }

    /// A struct whose stored fields (transitively) reach a `RawPtr` — its
    /// element storage is raw memory the region ledger cannot scan.
    fn raw_storage_backed(&self, symbol: crate::name_resolution::symbol::Symbol) -> bool {
        use crate::name_resolution::symbol::Symbol;
        let mut seen = FxHashSet::default();
        let mut stack = vec![symbol];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if let Some(info) = self.types.catalog.structs.get(&current) {
                for (_, (_, field_ty)) in &info.fields {
                    if let Ty::Nominal(field_symbol, _) = field_ty {
                        if *field_symbol == Symbol::RawPtr {
                            return true;
                        }
                        stack.push(*field_symbol);
                    }
                }
            }
        }
        false
    }

    /// The place an expression names, if it is one: a variable, or a chain
    /// of stored-field accesses off one.
    pub(crate) fn place(&self, expr: &typed_ast::Expr) -> Option<Place> {
        super::place::place_for_expr(expr)
    }

    pub(crate) fn check_use(
        &mut self,
        node: NodeID,
        ty: &Ty,
        place: &Place,
        use_is_owned: bool,
        state: &MoveState,
    ) {
        self.check_invalidated_use(node, ty, place, state);
        if let Some((moved, (_, ty))) = state.moved_for_use(place, use_is_owned) {
            let error = OwnershipError::UseAfterMove {
                name: render_place(moved, self.types),
                ty: ty.render_mono(),
            };
            self.error(error, node);
        }
        // A read of a mutably-borrowed owner conflicts (NLL: while the loan
        // is live). The borrower reading through itself is fine.
        if !use_is_owned {
            let owner = state.loan_owner_for(place);
            self.check_borrow_conflicts(node, &owner, Perm::Shared, Some(place), state);
        }
    }

    fn move_place(&mut self, expr: &typed_ast::Expr, place: Place, state: &mut MoveState) {
        self.move_place_with(expr, place, state, false);
    }

    /// `forced` = a `consume`-marked argument (ADR 0018): no liveness
    /// auto-clone (the move happens even before a live use, which then
    /// errors) and no tier-2 clone out of a borrow (moving out of a
    /// borrow errors instead).
    fn move_place_with(
        &mut self,
        expr: &typed_ast::Expr,
        place: Place,
        state: &mut MoveState,
        forced: bool,
    ) {
        let owned = self.grades.needs_drop(&expr.ty);
        let noncopy_closure = state
            .closure_captures
            .get(&place)
            .is_some_and(|summary| !summary.is_copyable());
        self.check_use(expr.id, &expr.ty, &place, owned || noncopy_closure, state);
        if !self.grades.is_copy(&expr.ty)
            && self.check_move_out_of_borrowed_with(expr, &place, state, forced)
        {
            // Tier 2: the extraction clones (lowering retains the buffers),
            // so the owner stays live — a read, not a move.
            return;
        }
        // GENERIC (Param/Proj-typed) values: the LAST consume moves, every
        // earlier consume implicitly copies (tier-2 auto-clone: CheapClone
        // retains, Copy is free — decided per instantiation at lowering).
        // Liveness decides which is which: `dead_after` is conservative
        // (false in sibling branches, loop-carried uses extend to the loop
        // end), so over-approximation only adds a balanced retain+release
        // pair, never a move before a live use. A moved-then-used generic
        // can therefore never arise — moving early and reusing would read
        // memory the consumer may already have freed.
        if matches!(expr.ty, Ty::Param(_) | Ty::Proj(..)) && tracked_root(place.root) {
            if !forced && !self.liveness.dead_after(expr.id, place.root) {
                if self.recording {
                    self.auto_clones.insert(expr.id);
                }
                return;
            }
            self.check_move_while_borrowed(expr.id, &place, state);
            if self.recording {
                self.consumed.insert(expr.id);
                self.facts.moves.push(super::FlowMoveFact {
                    node: expr.id,
                    place: render_place(&place, self.types),
                    ty: expr.ty.render_mono(),
                });
            }
            state.invalidate_borrows_of(&place);
            self.record_runtime_move(&place);
            state.note_move(place, expr.id, expr.ty.clone());
            return;
        }
        if (owned || noncopy_closure) && tracked_root(place.root) {
            self.check_move_while_borrowed(expr.id, &place, state);
            if self.recording {
                self.consumed.insert(expr.id);
                self.facts.moves.push(super::FlowMoveFact {
                    node: expr.id,
                    place: render_place(&place, self.types),
                    ty: expr.ty.render_mono(),
                });
            }
            state.invalidate_borrows_of(&place);
            self.record_runtime_move(&place);
            state.note_move(place, expr.id, expr.ty.clone());
        }
    }
}

/// Where a closure value flows, for the escape checks.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum EscapeContext {
    /// Bound or used locally.
    Bound,
    /// Returned, passed by value, or otherwise leaves the frame.
    Escaping,
}

fn tracked_root(root: crate::name_resolution::symbol::Symbol) -> bool {
    use crate::name_resolution::symbol::Symbol;
    matches!(
        root,
        Symbol::DeclaredLocal(_)
            | Symbol::PatternBindLocal(_)
            | Symbol::ParamLocal(_)
            | Symbol::Global(_)
    )
}

/// The callee expression's own parameter types (no self).
fn callee_params(callee: &typed_ast::Expr) -> Vec<Ty> {
    func_params(&callee.ty).unwrap_or_default()
}

pub(crate) fn func_params(ty: &Ty) -> Option<Vec<Ty>> {
    match ty {
        Ty::Func(params, ..) => Some(params.clone()),
        _ => None,
    }
}

/// A constructor call's produced type (the function's return).
fn result_ty(callee: &typed_ast::Expr) -> Ty {
    match &callee.ty {
        Ty::Func(_, ret, _) => (**ret).clone(),
        other => other.clone(),
    }
}

pub(crate) fn render_place(place: &Place, types: &TypeOutput) -> String {
    let mut out = render_symbol(place.root, types);
    for field in &place.fields {
        out.push('.');
        out.push_str(&render_symbol(*field, types));
    }
    out
}

pub(crate) fn render_symbol(
    symbol: crate::name_resolution::symbol::Symbol,
    types: &TypeOutput,
) -> String {
    types
        .display_names
        .get(&symbol)
        .map(|name| name.to_string())
        .unwrap_or_else(|| format!("{symbol}"))
}
