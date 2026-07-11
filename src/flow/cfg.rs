//! The flow checker's CFG engine (ADR 0010 stage 3): a forward dataflow
//! worklist over each stored MIR body. `MoveState` joins at block entry
//! from all predecessor exits, so `break`/`continue`/`return` are edges —
//! their states reach the loop exit / loop head / function exit — instead
//! of the tree walk's discard-at-join approximation.
//!
//! The per-statement transfer functions are the tree walk's expression
//! walkers, run in CFG-boundary mode: nested `if`/`match`/block expressions
//! embedded in statements are opaque (their effects rode the enclosing
//! body's blocks); statement-embedded blocks with no blocks of their own
//! (handler bodies, trailing blocks) still walk tree-style inside.
//!
//! The engine is the single flow authority (ADR 0010 stage 4): a recording
//! pass at the converged states produces the editor facts, statement/runtime
//! move sets, auto-clone flags, and per-point candidate elaborations; a final
//! pass reports the errors with the checked facts in place.

use std::collections::VecDeque;

use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::compiling::driver::Source;
use crate::lower::mir;
use crate::name_resolution::symbol::Symbol;
use crate::node_id::NodeID;
use crate::typed_ast::{self, TypedFile};
use crate::types::ty::{Perm, Ty};

use super::drops::{DropElaboration, DropReason};
use super::liveness::Liveness;
use super::moves::{MoveChecker, MoveState, classify};
use super::place::Place;

/// Check every stored body of the module on its CFG, plus a transient
/// per-file top-level body (whose classifications are discarded — lowering
/// uses the combined `main` body — but whose errors are the file's).
pub(crate) fn check_bodies(
    checker: &mut MoveChecker,
    files: &IndexMap<Source, TypedFile>,
    bodies: &mut crate::lower::mir::ModuleBodies,
) {
    let saved = (checker.report_errors, checker.recording);
    checker.recording = false;

    for file in files.values() {
        // The file's top level checks as its own body (fresh state, the
        // full roots — declaration members included), errors only: the
        // COMBINED main body below carries the recording.
        let mut top = mir::build_nodes(checker.types, &file.roots);
        let liveness = Liveness::analyze(&file.roots);
        check_body(
            checker,
            &mut top,
            liveness,
            &[],
            None,
            BodyRole::TopLevelErrors,
        );

        // Every function-like body under the roots, in pre-order — matching
        // the structural builder's enumeration.
        let mut walk = BodyWalk { checker, bodies };
        for root in &file.roots {
            use derive_visitor::Drive;
            root.drive(&mut walk);
        }
    }

    // The combined `main` body: every file's runnable top-level nodes in
    // order — exactly what lowering executes. Checked with cross-file
    // state (runtime-faithful) and stored as checked MIR; its errors are the
    // per-file walks' (already reported), so this pass only records.
    let main_nodes = crate::lower::mir::main_body_nodes(files.values());
    let mut main_body = mir::build_nodes(checker.types, &main_nodes);
    let liveness = Liveness::analyze(&main_nodes);
    check_body(
        checker,
        &mut main_body,
        liveness,
        &[],
        None,
        BodyRole::MainRecording,
    );
    bodies.set_top_level(main_body);

    (checker.report_errors, checker.recording) = saved;
}

/// What a body's check produces: stored bodies do everything; the per-file
/// top-level walks only report (the combined main records for them, so
/// facts aren't duplicated); the combined main only records (its errors
/// would duplicate the per-file walks').
#[derive(Clone, Copy, PartialEq)]
enum BodyRole {
    Stored,
    TopLevelErrors,
    MainRecording,
}

/// Drives `check_body` over each function-like body as the enumeration
/// encounters it: closures and named functions (whose params seed from the
/// expression type or the scheme) and init bodies (which seed nothing).
#[derive(derive_visitor::Visitor)]
#[visitor(typed_ast::Expr(enter), typed_ast::Decl(enter))]
struct BodyWalk<'a, 'types> {
    checker: &'a mut MoveChecker<'types>,
    bodies: &'a mut crate::lower::mir::ModuleBodies,
}

impl BodyWalk<'_, '_> {
    fn enter_expr(&mut self, expr: &typed_ast::Expr) {
        if let typed_ast::ExprKind::Func(func) = &expr.kind {
            self.check_func_body(func, Some(expr.ty.clone()));
        }
    }

    fn enter_decl(&mut self, decl: &typed_ast::Decl) {
        match &decl.kind {
            typed_ast::DeclKind::Func(func) => {
                let func_ty = func
                    .name
                    .symbol()
                    .ok()
                    .and_then(|symbol| self.checker.types.schemes.get(&symbol))
                    .map(|scheme| scheme.ty.clone());
                self.check_func_body(func, func_ty);
            }
            typed_ast::DeclKind::Method { func, .. } => {
                let func_ty = func
                    .name
                    .symbol()
                    .ok()
                    .and_then(|symbol| self.checker.types.schemes.get(&symbol))
                    .map(|scheme| scheme.ty.clone());
                self.check_func_body(func, func_ty);
            }
            typed_ast::DeclKind::Init { body, .. } => {
                let Some(stored) = self.bodies.get_mut(body.id) else {
                    return;
                };
                // An init seeds nothing: self is constructed, not owned.
                let liveness = Liveness::analyze(&body.body);
                check_body(self.checker, stored, liveness, &[], None, BodyRole::Stored);
            }
            _ => {}
        }
    }

    fn check_func_body(&mut self, func: &typed_ast::Func, func_ty: Option<Ty>) {
        let Some(stored) = self.bodies.get_mut(func.body.id) else {
            return;
        };
        // Bodies swap in fresh liveness like `check_func`.
        let liveness = Liveness::analyze(&func.body.body);
        check_body(
            self.checker,
            stored,
            liveness,
            &func.params,
            func_ty,
            BodyRole::Stored,
        );
    }
}

/// Fixpoint, recording, annotation, and error passes over one body.
fn check_body(
    checker: &mut MoveChecker,
    body: &mut mir::Body,
    liveness: Liveness,
    params: &[typed_ast::Parameter],
    func_ty: Option<Ty>,
    role: BodyRole,
) {
    let is_function = role == BodyRole::Stored;
    let outer = checker.enter_body(liveness, is_function);
    // A borrow-returning body (`-> &mut T { self.field }`) hands the
    // caller a borrow: the returned expression must not tier-2-clone
    // (nothing would release the retain).
    checker.ret_is_borrow = matches!(
        &func_ty,
        Some(Ty::Func(_, ret, _)) if matches!(&**ret, Ty::Borrow(..))
    );
    let mut entry_state = MoveState::default();
    if !params.is_empty() {
        checker.seed_params(params, func_ty.as_ref(), &mut entry_state);
    }
    checker.push_body_frame();

    // ----- Fixpoint: silent transfer until block-entry states converge.
    checker.report_errors = false;
    let mut entries: FxHashMap<usize, MoveState> = FxHashMap::default();
    entries.insert(body.entry.0, entry_state);
    let mut work: VecDeque<usize> = VecDeque::from([body.entry.0]);
    while let Some(index) = work.pop_front() {
        let mut state = entries[&index].clone();
        transfer_block(checker, body, index, &mut state, false);
        for (successor, edge_state) in successor_states(checker, body, index, &state) {
            match entries.get_mut(&successor) {
                Some(existing) => {
                    if existing.join_from(&edge_state) && !work.contains(&successor) {
                        work.push_back(successor);
                    }
                }
                None => {
                    entries.insert(successor, edge_state);
                    work.push_back(successor);
                }
            }
        }
    }

    if role != BodyRole::TopLevelErrors {
        // ----- Recording pass at the converged states: facts, runtime moves,
        // auto-clone flags, globals, and per-point candidate elaborations.
        checker.recording = true;
        for index in 0..body.blocks.len() {
            let Some(entry) = entries.get(&index) else {
                continue;
            };
            let mut state = entry.clone();
            transfer_block(checker, body, index, &mut state, true);
            // Terminator edge effects (scrutinee consumption, arm-binder
            // seeding) record their facts here too; the edge states are
            // already converged and are discarded.
            checker.begin_runtime_moves();
            successor_states(checker, body, index, &state);
            body.blocks[index].terminator_ownership.moves = checker.take_runtime_moves();
        }
        checker.recording = false;

        // ----- Bake recorded expression flags onto embedded nodes. Runtime
        // move sets and drop elaborations were written directly at their MIR
        // program points.
        let results = super::mir_annotate::FlowResults {
            consumed: &checker.consumed,
            auto_clones: &checker.auto_clones,
        };
        super::mir_annotate::annotate_flags_and_moves(body, &results);
    }

    if role != BodyRole::MainRecording {
        // ----- Error pass at the same converged states, with checked facts in
        // place (the Read-statement use-check consults them).
        checker.report_errors = true;
        for index in 0..body.blocks.len() {
            let Some(entry) = entries.get(&index) else {
                continue;
            };
            let mut state = entry.clone();
            transfer_block(checker, body, index, &mut state, false);
            // Terminator edge effects report their errors here (each block
            // is visited once, so nothing double-reports).
            successor_states(checker, body, index, &state);
        }
        checker.report_errors = false;
    }

    checker.pop_body_frame();
    checker.exit_body(outer, is_function);
}

/// Run one block's statements through the transfer functions, mutating
/// `state` in place; when `annotate`, also write candidate elaborations.
fn transfer_block(
    checker: &mut MoveChecker,
    body: &mut mir::Body,
    block: usize,
    state: &mut MoveState,
    annotate: bool,
) {
    for index in 0..body.blocks[block].statements.len() {
        if annotate {
            checker.begin_runtime_moves();
        }
        let elaboration = {
            let statement = &body.blocks[block].statements[index];
            transfer_statement(checker, &statement.kind, state, annotate)
        };
        if annotate {
            body.blocks[block].statements[index].ownership.moves = checker.take_runtime_moves();
        }
        if annotate && let Some(elaboration) = elaboration {
            body.blocks[block].statements[index].ownership.drop = elaboration;
        }
    }
}

/// Transfer one statement; returns `Some(new elaboration)` for a candidate
/// the reporting pass should overwrite.
fn transfer_statement(
    checker: &mut MoveChecker,
    statement: &mir::Statement,
    state: &mut MoveState,
    annotate: bool,
) -> Option<Option<mir::DropElaborationResult>> {
    match statement {
        mir::Statement::ScopeEnter { .. } | mir::Statement::ScopeExit { .. } => {}
        mir::Statement::StorageLive { id, symbol } => {
            let ty = local_ty(checker, *id, *symbol);
            checker.register_scope_local(*symbol, ty);
        }
        mir::Statement::StorageDead { symbol, .. } => {
            state.finish_local(&Place::root(*symbol));
        }
        // Reads and calls are evaluation statements INSIDE a source node:
        // no loan pruning until the node's consuming statement, or a loan
        // could die between a receiver read and the value use of the same
        // node (the tree prunes per node, after the whole statement).
        mir::Statement::Read {
            node,
            ty,
            place,
            consumes,
            pack,
        } => {
            // A place this node CONSUMES is checked once, as an owned use,
            // by its consuming statement — a shared-use check here would
            // report spurious borrow conflicts on the move.
            if !consumes {
                checker.check_boundaries(*node, ty, pack.as_ref());
                if let Some(place) = place {
                    checker.check_use(*node, ty, place, false, state);
                }
            }
        }
        mir::Statement::ConsumeValue { expr } => {
            checker.consume_expr(expr, state);
            checker.prune_at(state, expr.id);
        }
        mir::Statement::ReturnValue { expr, destination } => {
            match destination {
                mir::ValueDestination::Return | mir::ValueDestination::TailReturn => {
                    checker.check_return_value(expr, state);
                }
                mir::ValueDestination::Continuation(temp) => {
                    // The join block reads this construct's value as a
                    // `Temp`: record the delivered value's provenance so a
                    // borrowed match/if result reaches whatever its arm
                    // tails reach (states merging at the join union the
                    // arms' entries).
                    if checker.grades.contains_borrowed(&expr.ty) {
                        let provenance = checker.expr_provenance(expr, state);
                        state.temp_provenances.insert(*temp, provenance);
                    }
                    checker.consume_expr(expr, state);
                }
                mir::ValueDestination::Fallthrough => {
                    checker.consume_expr(expr, state);
                }
                mir::ValueDestination::TempThenContinue(temp) => {
                    if checker.grades.contains_borrowed(&expr.ty) {
                        let provenance = checker.expr_provenance(expr, state);
                        state.temp_provenances.insert(*temp, provenance);
                    }
                    checker.consume_expr(expr, state);
                }
            }
            checker.prune_at(state, expr.id);
        }
        mir::Statement::ContinueValue { expr } => {
            checker.consume_expr(expr, state);
            checker.prune_at(state, expr.id);
        }
        mir::Statement::Bind {
            lhs,
            type_annotation,
            rhs,
            for_source_mode,
        } => {
            if let Some(mode) = for_source_mode
                && let Some(rhs) = rhs
            {
                checker.check_marked_for_source(*mode, rhs);
            }
            checker.check_let(lhs, type_annotation.as_ref(), rhs.as_ref(), state);
            if let Some(rhs) = rhs {
                checker.prune_at(state, rhs.id);
            }
        }
        mir::Statement::Assign { lhs, rhs, .. } => {
            checker.check_assignment(NodeID::SYNTHESIZED, lhs, rhs, state);
            checker.prune_at(state, rhs.id);
        }
        mir::Statement::AssignmentRootUse { .. } => {}
        mir::Statement::Call {
            expr: _,
            temp,
            result_ty: _,
            callee,
            args,
            trailing_block,
        } => {
            let _ = trailing_block;
            // The result's provenance (a borrowed method result reaches
            // its receiver's owners) is read where the temp binds.
            let provenance = checker.call_provenance(callee, args, state);
            checker.check_call(callee, args, state);
            state.temp_provenances.insert(*temp, provenance);
        }
        mir::Statement::Perform { expr, .. } => {
            // The effect's arguments are source-consumed by the perform, but
            // the runtime payload remains owned by the performer. Do not
            // record a runtime transfer or lowering would clear the drop flag
            // and leak the payload on the performed path.
            if let typed_ast::ExprKind::CallEffect { args, .. } = &expr.kind {
                checker.with_runtime_moves_suppressed(|checker| {
                    for arg in args {
                        checker.consume_expr(&arg.value, state);
                    }
                });
            }
        }
        mir::Statement::Function { decl_func, .. } => {
            // Named nested `func` declarations apply their capture effects
            // here; every other function-like statement applies them at its
            // embedded consumption site (binding rhs, argument, value use).
            if let Some(func) = decl_func {
                checker.check_closure(func, state, super::moves::EscapeContext::Bound);
            }
        }
        // The handler body has its own CFG blocks (the `Handler`
        // terminator's edges carry the may-execute semantics); the
        // statement's embedded copy only carries source metadata.
        mir::Statement::Handling { .. } => {}
        mir::Statement::DeclBody { body } => {
            transfer_decl_body(checker, body, state);
        }
        mir::Statement::DropCandidate { target, reason, .. } => {
            return Some(classify_candidate(
                checker, target, *reason, state, annotate,
            ));
        }
    }
    None
}

/// Type-member property defaults evaluate against the enclosing state (the
/// bodies themselves are separate jobs).
fn transfer_decl_body(
    checker: &mut MoveChecker,
    body: &crate::typed_ast::Body,
    state: &mut MoveState,
) {
    for decl in &body.decls {
        match &decl.kind {
            typed_ast::DeclKind::Property {
                default_value: Some(value),
                ..
            } => checker.consume_expr(value, state),
            typed_ast::DeclKind::Struct { body, .. }
            | typed_ast::DeclKind::Enum { body, .. }
            | typed_ast::DeclKind::Extend { body, .. }
            | typed_ast::DeclKind::Protocol { body, .. } => {
                transfer_decl_body(checker, body, state)
            }
            _ => {}
        }
    }
}

/// Classify a drop candidate from the state at its point, mirroring the
/// tree walk's `schedule_drop` rules (needs-release filter, the arm-binder
/// alias rule, the linear must-consume error).
fn classify_candidate(
    checker: &mut MoveChecker,
    target: &mir::DropTarget,
    reason: DropReason,
    state: &MoveState,
    annotate: bool,
) -> Option<mir::DropElaborationResult> {
    use crate::name_resolution::symbol::Symbol;

    let (place, symbol, id) = match target {
        mir::DropTarget::Symbol { id, symbol } => (Place::root(*symbol), Some(*symbol), *id),
        // A `TemporaryEnd` candidate: the embedded `Temp` read is the
        // value. Consumed temps handed their value on (`Dead`); anything
        // droppable (or generic — each specialization elides per θ) that
        // was merely read drops here. Consumption is static per temp, so
        // the checker-level set (complete before the annotate pass)
        // classifies without per-path state.
        mir::DropTarget::Expr(expr) if matches!(expr.kind, typed_ast::ExprKind::Temp(_)) => {
            let typed_ast::ExprKind::Temp(temp) = expr.kind else {
                unreachable!()
            };
            let generic = matches!(expr.ty, Ty::Param(_) | Ty::Proj(..));
            if !generic
                && !checker.grades.needs_drop(&expr.ty)
                && !checker.grades.contains_object(&expr.ty)
            {
                return None;
            }
            let kind = if checker.consumed_temps.contains(&temp) {
                mir::DropElaboration::Dead
            } else {
                mir::DropElaboration::Static
            };
            return annotate.then_some(mir::DropElaborationResult {
                key_path: None,
                kind,
            });
        }
        mir::DropTarget::Expr(expr) => {
            // The assignment-replace target: classified at the
            // pre-assignment state (this candidate precedes the Assign).
            let place = checker.place(expr)?;
            // A `'heap`-carrying field replaced through a borrowed
            // receiver keeps the ledger's centralized cleanup: the region
            // is the caller's value's; releasing here kills it while the
            // owner still holds handles. Owned (non-object) replaced
            // values drop normally.
            let borrowed_root = matches!(checker.root_ty(place.root), Some(Ty::Borrow(..)));
            let kind = if borrowed_root && checker.grades.contains_object(&expr.ty) {
                DropElaboration::Dead
            } else {
                classify(&place, state)
            };
            return annotate.then_some(mir::DropElaborationResult {
                key_path: Some(place),
                kind,
            });
        }
    };
    let symbol_value = symbol?;
    let ty = local_ty(checker, id, symbol_value);
    // "Needs release": owned values drop; `'heap`-handle carriers release
    // their regions. GENERIC (Param/Proj) types classify too — the flow
    // runs once over the generic body, and each specialization elides
    // the drop when its instantiation doesn't need one. Otherwise the
    // candidate stays unelaborated.
    let generic = matches!(ty, Ty::Param(_) | Ty::Proj(..));
    if !generic && !checker.grades.needs_drop(&ty) && !checker.grades.contains_object(&ty) {
        return None;
    }
    // A pattern binder over a handle-only payload is a pure alias of the
    // scrutinee's value (which outlives the arm): no ledger event.
    // Generic binders stay aliases as well (the scrutinee's teardown
    // owns the payload).
    if matches!(symbol_value, Symbol::PatternBindLocal(_))
        && (generic || !checker.grades.needs_drop(&ty))
    {
        return None;
    }
    let kind = classify(&place, state);
    let is_param = matches!(symbol_value, Symbol::ParamLocal(_));
    if !is_param
        && kind != DropElaboration::Dead
        && matches!(reason, DropReason::ScopeExit | DropReason::EarlyExit)
        && checker.ty_is_linear(&ty)
    {
        let error = super::errors::OwnershipError::LinearNotConsumed {
            name: super::moves::render_place(&place, checker.types),
            ty: ty.render_mono(),
        };
        checker.error(error, id);
    }
    if checker.recording {
        checker.facts.drops.push(super::FlowDropFact {
            node: id,
            place: super::moves::render_place(&place, checker.types),
            ty: ty.render_mono(),
            kind,
            reason,
        });
    }
    annotate.then_some(mir::DropElaborationResult {
        key_path: Some(place),
        kind,
    })
}

fn local_ty(
    checker: &MoveChecker,
    id: NodeID,
    symbol: crate::name_resolution::symbol::Symbol,
) -> Ty {
    checker
        .symbol_local_ty(symbol)
        .or_else(|| checker.types.local_tys.get(&symbol).cloned())
        .or_else(|| checker.types.node_types.get(&id).cloned())
        .unwrap_or(Ty::Error)
}

/// The successor blocks of `block`'s terminator, each with the state that
/// flows along that edge.
fn successor_states(
    checker: &mut MoveChecker,
    body: &mir::Body,
    block: usize,
    exit_state: &MoveState,
) -> Vec<(usize, MoveState)> {
    match &body.blocks[block].terminator {
        mir::Terminator::Unset
        | mir::Terminator::Return
        | mir::Terminator::ReturnVoid
        | mir::Terminator::Break
        | mir::Terminator::Continue => vec![],
        mir::Terminator::Jump(target) => vec![(target.0, exit_state.clone())],
        mir::Terminator::Branch {
            then_block,
            else_block,
            ..
        } => vec![
            (then_block.0, exit_state.clone()),
            (else_block.0, exit_state.clone()),
        ],
        mir::Terminator::Loop {
            body_block,
            exit_block,
            ..
        } => vec![
            (body_block.0, exit_state.clone()),
            (exit_block.0, exit_state.clone()),
        ],
        // A handler body runs zero or more times; the two edges are the
        // tree walk's clone+merge (zero-or-one approximation, matching it).
        mir::Terminator::Handler { body_block, join } => vec![
            (body_block.0, exit_state.clone()),
            (join.0, exit_state.clone()),
        ],
        mir::Terminator::Switch {
            scrutinee,
            match_arms,
            arms,
            default,
            ..
        } => {
            // The scrutinee's evaluation rode this block's statements; its
            // consumption (when the match consumes it) happens here, after
            // snapshotting the provenance the arm binders re-borrow.
            let mut state = exit_state.clone();
            let scrutinee_provenance = checker
                .grades
                .contains_borrowed(&scrutinee.ty)
                .then(|| checker.expr_provenance(scrutinee, &state));
            // The match's dominant context consumes its scrutinee (the tree
            // walk's `consume_scrutinee` default); borrowed and copy
            // scrutinees don't move either way.
            checker.consume_expr(scrutinee, &mut state);
            let mut successors = vec![];
            for (index, arm_block) in arms.iter().enumerate() {
                let mut arm_state = state.clone();
                if let Some(arms) = match_arms
                    && let Some(arm) = arms.get(index)
                {
                    seed_arm_binders(
                        checker,
                        scrutinee,
                        arm,
                        scrutinee_provenance.as_ref(),
                        &mut arm_state,
                    );
                }
                successors.push((arm_block.0, arm_state));
            }
            if let Some(default) = default {
                successors.push((default.0, state.clone()));
            }
            successors
        }
    }
}

impl MoveChecker<'_> {
    /// Borrow permission of each binder's projection. Pattern syntax views
    /// through borrows, so this walk preserves the ownership fact that the
    /// binder's surface type intentionally omits.
    fn pattern_binder_borrows(
        &self,
        pattern: &typed_ast::Pattern,
        ty: &Ty,
    ) -> FxHashMap<Symbol, Perm> {
        let mut result = FxHashMap::default();
        self.collect_pattern_binder_borrows(pattern, ty, None, &mut result);
        result
    }

    fn collect_pattern_binder_borrows(
        &self,
        pattern: &typed_ast::Pattern,
        ty: &Ty,
        mut inherited: Option<Perm>,
        result: &mut FxHashMap<Symbol, Perm>,
    ) {
        let mut viewed = ty;
        loop {
            match viewed {
                Ty::Borrow(perm, inner) => {
                    inherited = Some(match inherited {
                        Some(outer) if !outer.is_exclusive() || !perm.is_exclusive() => {
                            Perm::Shared
                        }
                        Some(_) => Perm::Exclusive,
                        None => *perm,
                    });
                    viewed = inner;
                }
                Ty::Unique(inner) => viewed = inner,
                _ => break,
            }
        }

        match &pattern.kind {
            typed_ast::PatternKind::Bind(name) => {
                if let Some(perm) = inherited
                    && let Ok(symbol) = name.symbol()
                {
                    result.insert(symbol, perm);
                }
            }
            typed_ast::PatternKind::Tuple(patterns) => {
                if let Ty::Tuple(items) = viewed {
                    for (pattern, item) in patterns.iter().zip(items) {
                        self.collect_pattern_binder_borrows(pattern, item, inherited, result);
                    }
                }
            }
            typed_ast::PatternKind::Or(patterns) => {
                for pattern in patterns {
                    self.collect_pattern_binder_borrows(pattern, viewed, inherited, result);
                }
            }
            typed_ast::PatternKind::Variant {
                variant_name,
                fields,
                ..
            } => {
                let Ty::Nominal(symbol, args) = viewed else {
                    return;
                };
                let Some(info) = self.types.catalog.enums.get(symbol) else {
                    return;
                };
                let Some(variant) = info.variants.get(variant_name) else {
                    return;
                };
                let substitution: FxHashMap<Symbol, Ty> = info
                    .params
                    .iter()
                    .copied()
                    .zip(args.iter().cloned())
                    .collect();
                let Some(instantiation) = variant
                    .instantiate(&substitution, &Default::default(), &Default::default())
                    .refined_by_result(viewed)
                else {
                    return;
                };
                for (pattern, payload) in fields.iter().zip(&instantiation.argument_types) {
                    self.collect_pattern_binder_borrows(pattern, payload, inherited, result);
                }
            }
            typed_ast::PatternKind::Record { fields } => {
                let Ty::Record(row) = viewed else {
                    return;
                };
                for field in fields {
                    let (name, subpattern) = match &field.kind {
                        typed_ast::RecordFieldPatternKind::Bind(name) => (name, None),
                        typed_ast::RecordFieldPatternKind::Equals { name, value } => {
                            (name, Some(value))
                        }
                        typed_ast::RecordFieldPatternKind::Rest => continue,
                    };
                    let label = name.name_str();
                    let Some((_, field_ty)) = row
                        .fields
                        .iter()
                        .find(|(field_label, _)| field_label.to_string() == label)
                    else {
                        continue;
                    };
                    if let Some(perm) = inherited
                        && let Ok(symbol) = name.symbol()
                    {
                        result.insert(symbol, perm);
                    }
                    if let Some(subpattern) = subpattern {
                        self.collect_pattern_binder_borrows(
                            subpattern, field_ty, inherited, result,
                        );
                    }
                }
            }
            typed_ast::PatternKind::LiteralInt(_)
            | typed_ast::PatternKind::LiteralFloat(_)
            | typed_ast::PatternKind::LiteralTrue
            | typed_ast::PatternKind::LiteralFalse
            | typed_ast::PatternKind::Wildcard
            | typed_ast::PatternKind::Struct { .. } => {}
        }
    }
}

/// Mirror `walk_match`'s per-arm seeding: borrowed projections re-borrow
/// the scrutinee's owners; every binder starts initialized.
fn seed_arm_binders(
    checker: &mut MoveChecker,
    scrutinee: &typed_ast::Expr,
    arm: &typed_ast::MatchArm,
    scrutinee_provenance: Option<&super::loans::Provenance>,
    state: &mut MoveState,
) {
    let binder_borrows = checker.pattern_binder_borrows(&arm.pattern, &scrutinee.ty);
    if let Some(provenance) = scrutinee_provenance {
        for (binder_id, binder) in arm.pattern.collect_binders() {
            // Binder types live in `local_tys` (keyed by symbol — typing's
            // `mono` map), not `node_types`. Pattern viewing can also erase
            // a borrow from the binder's surface type, so projection
            // ownership is consulted independently.
            let binder_ty = local_ty(checker, binder_id, binder);
            if checker.grades.contains_borrowed(&binder_ty) || binder_borrows.contains_key(&binder)
            {
                checker.install_provenance(
                    binder_id,
                    Place::root(binder),
                    &binder_ty,
                    provenance.clone(),
                    state,
                );
            }
        }
    }
    for (_, binder) in arm.pattern.collect_binders() {
        state.restore(&Place::root(binder));
        if let Some(&perm) = binder_borrows.get(&binder) {
            state.borrowed_roots.insert(binder, perm);
            if !perm.is_exclusive() {
                state.shared_borrow_roots.insert(binder);
            }
        }
    }
}
