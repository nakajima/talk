//! Closure captures: summaries, mode validation, escape checks, and the
//! effects captures apply to the parent state — the legacy checker's
//! capture surface, reimplemented over the typed tree.
//!
//! Rules (legacy-verbatim):
//! - An implicit capture of an ownership-sensitive value (borrowed-containing
//!   or needs-drop) is rejected until a mode is explicit.
//! - With an explicit capture list, every used free variable must be listed.
//! - `[copy x]` requires a copyable type; `[consuming x]` cannot take
//!   borrowed values; `[&x]`/`[&mut x]` borrow (and pin the owner while the
//!   closure value lives).
//! - An escaping closure (returned, passed by value, discarded) cannot carry
//!   borrow captures, and its implicit captures must not be escape-sensitive
//!   (borrowed-containing, needs-drop, or generic — minus copy locals).
//! - A closure value with captures is itself non-copy unless every capture
//!   is a copy of a copyable, unborrowed value.

use rustc_hash::FxHashSet;

use crate::flow::OwnershipError;
use crate::node_id::NodeID;
use crate::node_kinds::func::CaptureMode;
use crate::typed_ast;
use crate::types::ty::{Perm, Ty};

use super::liveness::collect_free_reads;
use super::moves::{EscapeContext, MoveChecker, MoveState};
use super::place::Place;

#[derive(Clone, Debug)]
pub(crate) struct Capture {
    pub(crate) symbol: crate::name_resolution::symbol::Symbol,
    pub(crate) ty: Ty,
    pub(crate) mode: Option<CaptureMode>,
    pub(crate) borrowed_in_parent: bool,
    pub(crate) copyable: bool,
    pub(crate) ownership_sensitive: bool,
    pub(crate) escape_sensitive: bool,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct CaptureSummary {
    pub(crate) captures: Vec<Capture>,
}

impl CaptureSummary {
    /// A closure value is copyable only when every capture is a copy of a
    /// copyable, unborrowed value (or an implicit non-sensitive one).
    pub(crate) fn is_copyable(&self) -> bool {
        self.captures.iter().all(|capture| match capture.mode {
            Some(CaptureMode::Copy) => capture.copyable && !capture.borrowed_in_parent,
            Some(_) => false,
            None => !capture.borrowed_in_parent && !capture.ownership_sensitive,
        })
    }
}

fn mode_name(mode: CaptureMode) -> &'static str {
    match mode {
        CaptureMode::Copy => "copy",
        CaptureMode::Move => "consuming",
        CaptureMode::BorrowShared => "&",
        CaptureMode::BorrowMut => "&mut",
    }
}

impl MoveChecker<'_> {
    /// Check a closure at its creation site: build the capture summary,
    /// validate modes, and apply the parent-state effects. The body itself
    /// is checked from the store by the CFG engine.
    pub(crate) fn check_closure(
        &mut self,
        func: &typed_ast::Func,
        state: &mut MoveState,
        context: EscapeContext,
    ) -> CaptureSummary {
        let summary = self.capture_summary(func, state);
        self.check_capture_modes(func.id, &summary, !func.captures.is_empty());

        // Implicit captures of ownership-sensitive values need a mode.
        for capture in &summary.captures {
            if capture.mode.is_none() && capture.ownership_sensitive {
                let error = OwnershipError::UnsupportedClosureCapture {
                    name: super::moves::render_symbol(capture.symbol, self.types),
                    ty: capture.ty.render_mono(),
                };
                self.error(error, func.id);
            }
        }

        if context == EscapeContext::Escaping {
            self.check_escaping_summary(func.id, &summary);
        }

        // Parent-state effects: copies read, moves move; borrows are applied
        // by the binding that names the closure (the loan needs a borrower).
        for capture in &summary.captures {
            let place = Place::root(capture.symbol);
            match capture.mode {
                Some(CaptureMode::Move) => {
                    self.check_capture_use(func.id, &place, true, state);
                    if !capture.copyable {
                        self.check_move_while_borrowed(func.id, &place, state);
                        state.invalidate_borrows_of(&place);
                        self.record_runtime_move(&place);
                        state.note_move(place, func.id, capture.ty.clone());
                    }
                }
                _ => {
                    self.check_capture_use(func.id, &place, false, state);
                }
            }
        }

        summary
    }

    /// Apply a bound closure's borrow captures: the binder is the borrower,
    /// pinning each captured owner until the closure value's last use.
    pub(crate) fn apply_borrow_captures(
        &mut self,
        binder: Place,
        node: NodeID,
        summary: &CaptureSummary,
        state: &mut MoveState,
    ) {
        for capture in &summary.captures {
            let kind = match capture.mode {
                Some(CaptureMode::BorrowShared) => Perm::Shared,
                Some(CaptureMode::BorrowMut) => Perm::Exclusive,
                _ => continue,
            };
            let owner = Place::root(capture.symbol);
            self.check_borrow_conflicts(node, &owner, kind, Some(&binder), state);
            state.add_loan(binder.clone(), owner, kind);
        }
    }

    /// A closure value escaping the frame: borrow captures cannot escape,
    /// and implicit captures must not be escape-sensitive.
    pub(crate) fn check_escaping_summary(&mut self, node: NodeID, summary: &CaptureSummary) {
        for capture in &summary.captures {
            // A `'heap` handle in an escaping closure's environment is
            // invisible to the region ledger: reject regardless of mode.
            if self.grades.contains_object(&capture.ty) {
                let error = OwnershipError::EscapingObjectCapture {
                    name: super::moves::render_symbol(capture.symbol, self.types),
                    ty: capture.ty.render_mono(),
                };
                self.error(error, node);
                continue;
            }
            match capture.mode {
                Some(CaptureMode::BorrowShared) | Some(CaptureMode::BorrowMut) => {
                    let error = OwnershipError::EscapingClosureCapture {
                        name: super::moves::render_symbol(capture.symbol, self.types),
                        ty: capture.ty.render_mono(),
                        reason: "borrow captures are tied to the current stack frame".to_string(),
                    };
                    self.error(error, node);
                }
                None if capture.escape_sensitive => {
                    let error = OwnershipError::UnsupportedClosureCapture {
                        name: super::moves::render_symbol(capture.symbol, self.types),
                        ty: capture.ty.render_mono(),
                    };
                    self.error(error, node);
                }
                _ => {}
            }
        }
    }

    fn check_capture_modes(
        &mut self,
        node: NodeID,
        summary: &CaptureSummary,
        require_explicit: bool,
    ) {
        for capture in &summary.captures {
            match capture.mode {
                None if require_explicit => {
                    let error = OwnershipError::ImplicitClosureCapture {
                        name: super::moves::render_symbol(capture.symbol, self.types),
                        ty: capture.ty.render_mono(),
                    };
                    self.error(error, node);
                }
                Some(CaptureMode::Copy) if !capture.copyable => {
                    let error = OwnershipError::InvalidClosureCaptureMode {
                        name: super::moves::render_symbol(capture.symbol, self.types),
                        mode: mode_name(CaptureMode::Copy).to_string(),
                        ty: capture.ty.render_mono(),
                        reason: "copy captures require a copyable type".to_string(),
                    };
                    self.error(error, node);
                }
                Some(CaptureMode::Move)
                    if self.grades.is_borrowed_value(&capture.ty)
                        || self.grades.contains_borrowed(&capture.ty) =>
                {
                    let error = OwnershipError::InvalidClosureCaptureMode {
                        name: super::moves::render_symbol(capture.symbol, self.types),
                        mode: mode_name(CaptureMode::Move).to_string(),
                        ty: capture.ty.render_mono(),
                        reason: "move captures cannot take ownership of borrowed values"
                            .to_string(),
                    };
                    self.error(error, node);
                }
                _ => {}
            }
        }
    }

    fn check_capture_use(&mut self, node: NodeID, place: &Place, owned: bool, state: &MoveState) {
        if let Some((moved, (_, ty))) = state.moved_for_use(place, owned) {
            let error = OwnershipError::UseAfterMove {
                name: super::moves::render_place(moved, self.types),
                ty: ty.render_mono(),
            };
            self.error(error, node);
        }
    }

    /// The closure's captures: free-variable reads of the body plus every
    /// explicitly listed capture, with modes from the `[...]` list.
    fn capture_summary(&mut self, func: &typed_ast::Func, state: &MoveState) -> CaptureSummary {
        let mut bound: FxHashSet<crate::name_resolution::symbol::Symbol> = FxHashSet::default();
        for param in &func.params {
            if let Ok(symbol) = param.name.symbol() {
                bound.insert(symbol);
            }
        }
        let mut used = FxHashSet::default();
        collect_free_reads(&func.body, &mut bound, &mut used);

        let explicit: Vec<(crate::name_resolution::symbol::Symbol, CaptureMode)> = func
            .captures
            .iter()
            .filter_map(|spec| spec.name.symbol().ok().map(|symbol| (symbol, spec.mode)))
            .collect();

        let mut symbols: Vec<crate::name_resolution::symbol::Symbol> = used.into_iter().collect();
        symbols.sort();
        for (symbol, _) in &explicit {
            if !symbols.contains(symbol) {
                symbols.push(*symbol);
            }
        }

        let captures = symbols
            .into_iter()
            .map(|symbol| {
                let ty = self.symbol_local_ty(symbol).unwrap_or(Ty::Error);
                let mode = explicit
                    .iter()
                    .find(|(explicit_symbol, _)| *explicit_symbol == symbol)
                    .map(|(_, mode)| *mode);
                let borrowed_in_parent = state.borrowed_roots.contains_key(&symbol)
                    || state.provenances.contains_key(&Place::root(symbol));
                let copyable = self.grades.is_copy(&ty);
                let ownership_sensitive =
                    self.grades.contains_borrowed(&ty) || self.grades.needs_drop(&ty);
                let escape_sensitive = (ownership_sensitive || contains_param(&ty))
                    && !(copyable && !borrowed_in_parent && !contains_param(&ty));
                Capture {
                    symbol,
                    ty,
                    mode,
                    borrowed_in_parent,
                    copyable,
                    ownership_sensitive,
                    escape_sensitive,
                }
            })
            .collect();
        CaptureSummary { captures }
    }
}

fn contains_param(ty: &Ty) -> bool {
    use std::ops::ControlFlow;
    ty.try_visit(&mut |t| {
        if matches!(t, Ty::Param(_)) {
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(())
        }
    })
    .is_break()
}
