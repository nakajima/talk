//! Type-level ownership queries for the flow checker: does a type need a
//! drop (and therefore move on use), and is it trivially copyable? Ports the
//! legacy checker's `type_contains_owned`/`type_is_copy` verbatim in
//! semantics, but reads everything from the type catalog. The `Owner` /
//! `Borrowed` marker protocols are still honored while the core library
//! carries them; they retire with the legacy checker.
//!
//! ## Deliberate dual: declared Copy (typing) vs structural copy (here)
//!
//! Typing's Copy judgment (`catalog.grade_of(head) == Grade::Copy`,
//! `copies_out_of_borrow`) is DECLARED — scalars, payload-free enums, and
//! explicit `Copy` conformances — and gates coercion legality: may a
//! borrowed value satisfy an owned slot, is `&Int` erased to `Int`
//! (ADR 0014). [`GradeView::is_copy`] is STRUCTURAL — a field walk — and
//! answers move-on-use for the flow lattice: does using the value move
//! it, does its storage need a drop. Example: `struct Point { let x: Int,
//! let y: Int }` with no `Copy` conformance is structurally copy (using a
//! `Point` never moves it; nothing to drop) but not declared Copy
//! (`&Point` does not coerce to owned `Point` — the declaration is the
//! API contract, so adding a `String` field later cannot silently
//! legalize existing call sites). Do not "unify" the two: making typing
//! structural widens coercions behind the author's back, and making flow
//! declared-only would schedule moves and drops for values that have
//! nothing to drop.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::name_resolution::symbol::Symbol;
use crate::types::TypeOutput;
use crate::types::ty::Ty;

/// The tier-2 ownership action for a value leaving storage its consumer
/// does not own (a borrowed/temp extraction, a `copy` argument, a region
/// constructor's place read): what must happen for the extracted value to
/// get an independent lifetime. One judgment behind every site that used
/// to spell the `Copy` / `CheapClone`-or-generic / owned-droppable split
/// by hand; the ACTION each site takes per variant stays local to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Tier2Action {
    /// No owned parts: nothing to emit.
    Copy,
    /// `CheapClone`: an O(1) buffer retain — the clone and the original
    /// release independently.
    Retain,
    /// Generic (`Param`/`Proj`): mark a retain and let the θ-resolved
    /// instantiation decide at lowering (Copy: nothing, CheapClone:
    /// retain, owned non-CheapClone: a loud lowering error).
    Generic,
    /// Owned droppable, not retainable: ownership must transfer.
    Move,
}

pub(crate) struct GradeView<'a> {
    types: &'a TypeOutput,
}

impl<'a> GradeView<'a> {
    pub(crate) fn new(types: &'a TypeOutput) -> Self {
        GradeView { types }
    }

    /// "Owned" == "needs drop": using this type's value at a consume site
    /// moves it, and its storage requires a drop when live at scope exit.
    pub(crate) fn needs_drop(&self, ty: &Ty) -> bool {
        self.contains_owned(ty, &mut FxHashSet::default())
    }

    /// Trivially copyable: using the value never moves it. Not the exact
    /// complement of [`GradeView::needs_drop`] — type params and unsolved
    /// projections are neither.
    pub(crate) fn is_copy(&self, ty: &Ty) -> bool {
        self.copy_ty(ty, &mut FxHashSet::default())
    }

    /// A `'heap` object type: values are region-allocated references —
    /// alias-on-use, never moved, released at region granularity.
    pub(crate) fn is_object(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Nominal(symbol, _) => self.symbol_is_object(*symbol),
            _ => false,
        }
    }

    /// Declared `'heap` on a declaration head — the symbol-level twin of
    /// [`GradeView::is_object`] for callers holding a destructured head.
    pub(crate) fn symbol_is_object(&self, symbol: Symbol) -> bool {
        self.types.catalog.is_heap(symbol)
    }

    /// Whether the VALUE of this type carries an object handle anywhere —
    /// the binding needs region acquire/release bookkeeping. Mirrors
    /// [`GradeView::contains_borrowed`]: function values are excluded.
    pub(crate) fn contains_object(&self, ty: &Ty) -> bool {
        self.contains_object_inner(ty, &mut FxHashSet::default())
    }

    fn contains_object_inner(&self, ty: &Ty, seen: &mut FxHashSet<Symbol>) -> bool {
        match ty {
            Ty::Borrow(_, inner) | Ty::Unique(inner) => self.contains_object_inner(inner, seen),
            Ty::Nominal(symbol, args) => {
                if self.types.catalog.is_heap(*symbol) {
                    return true;
                }
                if !seen.insert(*symbol) {
                    return false;
                }
                let contains = self
                    .payload_types(*symbol, args)
                    .iter()
                    .any(|field| self.contains_object_inner(field, seen))
                    || args.iter().any(|arg| self.contains_object_inner(arg, seen));
                seen.remove(symbol);
                contains
            }
            Ty::Tuple(items) => items
                .iter()
                .any(|item| self.contains_object_inner(item, seen)),
            Ty::Record(row) => row
                .fields
                .iter()
                .any(|(_, field)| self.contains_object_inner(field, seen)),
            Ty::Func(..)
            | Ty::Any { .. }
            | Ty::Proj(..)
            | Ty::Var(_)
            | Ty::Param(_)
            | Ty::Eff(_)
            | Ty::Error => false,
        }
    }

    /// See [`Tier2Action`]. Built on this view's structural predicates —
    /// deliberately NOT typing's declared `CoerceKind` (see the module
    /// doc's declared/structural dual).
    pub(crate) fn tier2_action(&self, ty: &Ty) -> Tier2Action {
        if matches!(ty, Ty::Param(_) | Ty::Proj(..)) {
            return Tier2Action::Generic;
        }
        if self.is_cheap_clone(ty) {
            return Tier2Action::Retain;
        }
        if self.needs_drop(ty) {
            return Tier2Action::Move;
        }
        Tier2Action::Copy
    }

    /// Cloning this type is an O(1) buffer retain (the `CheapClone`
    /// marker): extracting it from a borrow clones silently instead of
    /// moving out.
    pub(crate) fn is_cheap_clone(&self, ty: &Ty) -> bool {
        match ty {
            // The declared rows (with their where-clause contexts) decide,
            // through the same catalog judgment the marker field check and
            // clone-witness selection use.
            Ty::Nominal(symbol, args) => self.types.catalog.cheap_clone_rows(*symbol, args),
            _ => false,
        }
    }

    pub(crate) fn param_copies_out_of_borrow(&self, symbol: Symbol) -> bool {
        self.types
            .catalog
            .param_bounds
            .get(&symbol)
            .is_some_and(|bounds| self.types.catalog.bounds_coerce_kind(bounds).is_some())
    }

    /// A borrowed *value* type: `Substring` and friends (the `Borrowed`
    /// marker), or a `&T` itself.
    pub(crate) fn is_borrowed_value(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Borrow(..) => true,
            Ty::Nominal(symbol, _) => self.symbol_is_borrowed_value(*symbol),
            _ => false,
        }
    }

    /// The `Borrowed` marker on a declaration head — the symbol-level twin
    /// of [`GradeView::is_borrowed_value`] for callers holding a
    /// destructured nominal head.
    pub(crate) fn symbol_is_borrowed_value(&self, symbol: Symbol) -> bool {
        self.has_marker(symbol, Symbol::Borrowed)
    }

    /// Declared `'linear`: values must move (never copy) and must reach a
    /// consume site, even when every field is structurally copyable.
    pub(crate) fn is_linear(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Nominal(symbol, _) if self.symbol_is_linear(*symbol))
    }

    fn symbol_is_linear(&self, symbol: Symbol) -> bool {
        self.types.catalog.grade_of(symbol) == crate::types::catalog::Grade::Linear
    }

    /// Whether the VALUE of this type contains a borrow: a `&T`, or a
    /// nominal carrying the `Borrowed` marker (directly or in its
    /// arguments/fields). Function types are excluded — a function value
    /// whose signature mentions borrows is not itself a borrowed value.
    pub(crate) fn contains_borrowed(&self, ty: &Ty) -> bool {
        self.contains_borrowed_inner(ty, &mut FxHashSet::default())
    }

    fn contains_borrowed_inner(&self, ty: &Ty, seen: &mut FxHashSet<Symbol>) -> bool {
        match ty {
            Ty::Borrow(..) => true,
            Ty::Unique(inner) => self.contains_borrowed_inner(inner, seen),
            Ty::Nominal(symbol, args) => {
                if self.has_marker(*symbol, Symbol::Borrowed) {
                    return true;
                }
                if !seen.insert(*symbol) {
                    return false;
                }
                let contains = self
                    .payload_types(*symbol, args)
                    .iter()
                    .any(|field| self.contains_borrowed_inner(field, seen))
                    || args
                        .iter()
                        .any(|arg| self.contains_borrowed_inner(arg, seen));
                seen.remove(symbol);
                contains
            }
            Ty::Tuple(items) => items
                .iter()
                .any(|item| self.contains_borrowed_inner(item, seen)),
            Ty::Record(row) => row
                .fields
                .iter()
                .any(|(_, field)| self.contains_borrowed_inner(field, seen)),
            Ty::Func(..)
            | Ty::Any { .. }
            | Ty::Proj(..)
            | Ty::Var(_)
            | Ty::Param(_)
            | Ty::Eff(_)
            | Ty::Error => false,
        }
    }

    fn copy_ty(&self, ty: &Ty, seen: &mut FxHashSet<Symbol>) -> bool {
        match ty {
            Ty::Borrow(..) | Ty::Func(..) => true,
            // Unique values are the sole reference by definition: never copy.
            Ty::Unique(_) => false,
            Ty::Nominal(symbol, args) => {
                if self.has_marker(*symbol, Symbol::Borrowed) {
                    return true;
                }
                // Object handles copy freely: the region, not the use
                // site, accounts for the value's lifetime.
                if self.types.catalog.is_heap(*symbol) {
                    return true;
                }
                if self.contains_owned(ty, &mut FxHashSet::default()) {
                    return false;
                }
                if matches!(
                    *symbol,
                    Symbol::Int | Symbol::Float | Symbol::Bool | Symbol::Void | Symbol::Never
                ) || *symbol == Symbol::RawPtr
                    || *symbol == Symbol::Byte
                {
                    return true;
                }
                // Recursion guard: a cycle without owned content is copy.
                if !seen.insert(*symbol) {
                    return true;
                }
                let copy = self
                    .payload_types(*symbol, args)
                    .iter()
                    .all(|field| self.copy_ty(field, seen));
                seen.remove(symbol);
                copy
            }
            Ty::Tuple(items) => items.iter().all(|item| self.copy_ty(item, seen)),
            Ty::Record(row) => row
                .fields
                .iter()
                .all(|(_, field)| self.copy_ty(field, seen)),
            // An effect argument is runtime-inert: it never blocks a copy.
            Ty::Eff(_) => true,
            Ty::Any { .. } | Ty::Proj(..) | Ty::Var(_) | Ty::Param(_) | Ty::Error => false,
        }
    }

    fn contains_owned(&self, ty: &Ty, seen: &mut FxHashSet<Symbol>) -> bool {
        match ty {
            Ty::Borrow(..) => false,
            // A unique value is owned by definition: it moves and drops.
            Ty::Unique(_) => true,
            Ty::Nominal(symbol, args) => {
                if self.has_marker(*symbol, Symbol::Borrowed) {
                    return false;
                }
                // Interior ownership of a heap object is the region's
                // business: handles neither move nor drop per-use.
                if self.types.catalog.is_heap(*symbol) {
                    return false;
                }
                if self.has_marker(*symbol, Symbol::Owner)
                    || self.has_marker(*symbol, Symbol::Deinit)
                {
                    return true;
                }
                // A linear declaration is owned by fiat (see is_linear).
                if self.symbol_is_linear(*symbol) {
                    return true;
                }
                if !seen.insert(*symbol) {
                    return false;
                }
                let owned = self
                    .payload_types(*symbol, args)
                    .iter()
                    .any(|field| self.contains_owned(field, seen));
                seen.remove(symbol);
                owned
            }
            Ty::Tuple(items) => items.iter().any(|item| self.contains_owned(item, seen)),
            Ty::Record(row) => row
                .fields
                .iter()
                .any(|(_, field)| self.contains_owned(field, seen)),
            // Existentials own conservatively: the payload is hidden.
            Ty::Any { .. } => true,
            // Generic params stay copy-like at flow (moves untracked):
            // the CALLER of a generic-param position owns its rvalue
            // arguments and drops them post-call, per specialization
            // (lower/calls.rs release_temps_then).
            Ty::Func(..) | Ty::Proj(..) | Ty::Var(_) | Ty::Param(_) | Ty::Eff(_) | Ty::Error => {
                false
            }
        }
    }

    /// Every stored payload type of a nominal, with the application's
    /// generic arguments substituted in: struct field types, or all enum
    /// variants' constructor parameter types.
    fn payload_types(&self, symbol: Symbol, args: &[Ty]) -> Vec<Ty> {
        let catalog = &self.types.catalog;
        if let Some(info) = catalog.structs.get(&symbol) {
            let subst = param_subst(&info.params, args);
            return info
                .fields
                .values()
                .map(|(_, ty)| substitute(ty, &subst))
                .collect();
        }
        if let Some(info) = catalog.enums.get(&symbol) {
            let subst = param_subst(&info.params, args);
            return info
                .variants
                .values()
                .flat_map(|variant| match &variant.constructor_scheme.ty {
                    Ty::Func(payloads, ..) => {
                        payloads.iter().map(|ty| substitute(ty, &subst)).collect()
                    }
                    _ => vec![],
                })
                .collect();
        }
        vec![]
    }

    fn has_marker(&self, symbol: Symbol, marker: Symbol) -> bool {
        self.types.catalog.has_bare_conformance(symbol, marker)
    }
}

/// A syntactic `&T` in stored position (not under a function type: a
/// function value whose signature mentions borrows is fine to store).
/// Deliberately NOT [`GradeView::contains_borrowed`]: this is the
/// declaration-position question for `check_borrow_storage`, so nominal
/// heads are transparent — a `Borrowed`-marker type (`Substring`) is a
/// storable value whose loans provenance tracks, and a concrete nominal's
/// own fields were checked at its own declaration. Only the syntactic
/// borrow (including via generic arguments) is rejected.
pub(crate) fn stores_borrow(ty: &Ty) -> bool {
    match ty {
        Ty::Borrow(..) => true,
        Ty::Unique(inner) => stores_borrow(inner),
        Ty::Nominal(_, args) => args.iter().any(stores_borrow),
        Ty::Tuple(items) => items.iter().any(stores_borrow),
        Ty::Record(row) => row.fields.iter().any(|(_, field)| stores_borrow(field)),
        Ty::Func(..)
        | Ty::Any { .. }
        | Ty::Proj(..)
        | Ty::Var(_)
        | Ty::Param(_)
        | Ty::Eff(_)
        | Ty::Error => false,
    }
}

fn param_subst(params: &[Symbol], args: &[Ty]) -> FxHashMap<Symbol, Ty> {
    params.iter().copied().zip(args.iter().cloned()).collect()
}

fn substitute(ty: &Ty, subst: &FxHashMap<Symbol, Ty>) -> Ty {
    if subst.is_empty() {
        return ty.clone();
    }
    ty.substitute(subst, &FxHashMap::default(), &FxHashMap::default())
}
