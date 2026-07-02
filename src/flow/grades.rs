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

    fn contains_owned(&self, ty: &Ty, seen: &mut FxHashSet<Symbol>) -> bool {
        match ty {
            Ty::Borrow(..) => false,
            Ty::Nominal(symbol, args) => {
                if self.has_marker(*symbol, Symbol::Borrowed) {
                    return false;
                }
                if self.has_marker(*symbol, Symbol::Owner) {
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
