//! Type-level ownership queries for the flow checker: does a type need a
//! drop (and therefore move on use), and is it trivially copyable? Ports the
//! legacy checker's `type_contains_owned`/`type_is_copy` verbatim in
//! semantics, but reads everything from the type catalog. The `Owner` /
//! `Borrowed` marker protocols are still honored while the core library
//! carries them; they retire with the legacy checker.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::name_resolution::symbol::Symbol;
use crate::types::TypeOutput;
use crate::types::ty::Ty;

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
            Ty::Nominal(symbol, _) => self.types.catalog.is_heap(*symbol),
            _ => false,
        }
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
            Ty::Tuple(items) => items.iter().any(|item| self.contains_object_inner(item, seen)),
            Ty::Record(row) => row
                .fields
                .iter()
                .any(|(_, field)| self.contains_object_inner(field, seen)),
            Ty::Func(..)
            | Ty::Any { .. }
            | Ty::Proj(..)
            | Ty::Var(_)
            | Ty::Param(_)
            | Ty::Error => false,
        }
    }

    /// Cloning this type is an O(1) buffer retain (the `CheapClone`
    /// marker): extracting it from a borrow clones silently instead of
    /// moving out.
    pub(crate) fn is_cheap_clone(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Nominal(symbol, _) => self.has_marker(*symbol, Symbol::CheapClone),
            _ => false,
        }
    }

    /// A borrowed *value* type: `Substring` and friends (the `Borrowed`
    /// marker), or a `&T` itself.
    pub(crate) fn is_borrowed_value(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Borrow(..) => true,
            Ty::Nominal(symbol, _) => self.has_marker(*symbol, Symbol::Borrowed),
            _ => false,
        }
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
                    || args.iter().any(|arg| self.contains_borrowed_inner(arg, seen));
                seen.remove(symbol);
                contains
            }
            Ty::Tuple(items) => items.iter().any(|item| self.contains_borrowed_inner(item, seen)),
            Ty::Record(row) => row
                .fields
                .iter()
                .any(|(_, field)| self.contains_borrowed_inner(field, seen)),
            Ty::Func(..)
            | Ty::Any { .. }
            | Ty::Proj(..)
            | Ty::Var(_)
            | Ty::Param(_)
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
            Ty::Record(row) => row.fields.iter().all(|(_, field)| self.copy_ty(field, seen)),
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
                // A linear declaration is owned by fiat: its values must
                // move (never copy) and must reach a consume site, even when
                // every field is structurally copyable.
                if self.types.catalog.grade_of(*symbol) == crate::types::catalog::Grade::Linear {
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
            Ty::Func(..) | Ty::Proj(..) | Ty::Var(_) | Ty::Param(_) | Ty::Error => false,
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
                    Ty::Func(payloads, ..) => payloads.iter().map(|ty| substitute(ty, &subst)).collect(),
                    _ => vec![],
                })
                .collect();
        }
        vec![]
    }

    fn has_marker(&self, symbol: Symbol, marker: Symbol) -> bool {
        self.types
            .catalog
            .conformances
            .contains_key(&(symbol, marker))
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
