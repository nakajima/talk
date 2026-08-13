//! The one value-adaptation judgment (ADR 0054; ADR 0057 slice 1).
//!
//! "How does a value of type `found` cross into a slot of type `expected`?"
//! is decided here and nowhere else. Every crossing site — constraint
//! generation, the solver's `Adapt` dispatcher, function-type unification,
//! member dispatch, finalize's pack and marker checks — calls [`adapt`] (or
//! the tier query [`donation_tier`]) and translates the returned [`Adapted`]
//! into its own phase's vocabulary: a wanted constraint, a solver queue
//! push, a diagnostic. No caller re-derives the rule; the permission tier
//! tests and borrow peels below are private to this module by design.
//!
//! The judgment is pure over the store and catalog: it resolves variables
//! (`shallow`) but never binds one, and it reports what should happen
//! rather than doing it. That is what makes it callable from every phase —
//! the property whose absence bred the eight divergent copies ADR 0054
//! catalogs.

use super::catalog::{CoerceKind, TypeCatalog};
use super::solve::VarStore;
use super::ty::{Perm, Ty};

/// Where the crossing happens. Only distinctions that change the rule:
/// argument positions run the full ladder; result positions allow only the
/// covariant `&mut` → `&` downgrade; return/body positions donate a borrow
/// into an owned slot unconditionally (MIR owns the return-donation rule).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Site {
    Argument,
    Result,
    Return,
}

/// The donation tier a borrow uses to fill an owned slot. `Copy` extracts
/// by value (nothing to emit), `CheapClone` by an O(1) retain that lowering
/// emits at the recorded node, `Share` by the implicit-sharing
/// clone-at-boundary rule (lowering derives the retain from the type).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Donation {
    Copy,
    CheapClone,
    Share,
}

/// What the crossing site should do. Origin/reason bookkeeping stays with
/// the caller (each phase has its own demotion convention); the shapes and
/// the decision are the judgment's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Adapted {
    /// One equality remains. `peeled` reports that an ownership wrapper was
    /// crossed (the application boundary is consumed, so `Apply`-style
    /// reasons demote to their nested form where the caller tracks that).
    Eq { expected: Ty, found: Ty, peeled: bool },
    /// The shapes cannot adapt (incompatible borrow permissions): equate
    /// them unchanged so unification reports a mismatch naming both.
    Mismatch { expected: Ty, found: Ty },
    /// A borrow donates into the owned slot: equate `expected` with the
    /// borrow's referent and realize the tier (record `coerce_clones` on
    /// `CheapClone`).
    Donate {
        expected: Ty,
        found_inner: Ty,
        donation: Donation,
    },
    /// A rigid slot whose bounds carry no Copy/CheapClone evidence cannot
    /// accept a borrow: report non-conformance (bounds are closed, so no
    /// later fact can rescue it).
    NoEvidence { expected: Ty },
    /// A side is unresolved (variable or irreducible projection), so the
    /// crossing cannot be decided yet. `visible_borrow` reports whether the
    /// resolved side already shows an ownership wrapper — a peel or a
    /// donation may still apply once the unknown side resolves. What to do
    /// is the caller's scheduling strategy, not the rule's: the solver's
    /// `Adapt` dispatcher stays patient either way (its constraints arrived
    /// flagged as crossings, and premature equalities are ADR 0017 bug B),
    /// while the eager emitters requeue as `Constraint::Adapt` only when a
    /// borrow is visible and otherwise commit the plain equality that keeps
    /// inference moving.
    Unresolved { visible_borrow: bool },
    /// A borrow-typed slot fed an irreducible projection. No projection
    /// reduces to a borrow, so peeling the slot is sound — but committing
    /// `inner ~ projection` binds the projection into the slot NOW, before
    /// the member chain that will reduce it has run. Scheduling is the
    /// caller's: function-type decomposition peels eagerly (recursion-group
    /// generalization relies on the in-group binding), while the member and
    /// generation emitters requeue as `Constraint::Adapt` and take the
    /// solver's normalized view.
    PeelableProjection { expected_inner: Ty, found: Ty },
    /// An error operand: emit nothing, recovery already reported.
    Silent,
}

/// The judgment. Inputs are resolved only as deep as the rule needs
/// (`shallow`); callers pass types as they hold them.
pub(crate) fn adapt(
    store: &mut VarStore,
    catalog: &TypeCatalog,
    expected: &Ty,
    found: &Ty,
    site: Site,
) -> Adapted {
    if site == Site::Result {
        return match (store.shallow(expected), store.shallow(found)) {
            (Ty::Borrow(expected_perm, expected_inner), Ty::Borrow(found_perm, found_inner))
                if store.shallow_perm(expected_perm) == Perm::Shared
                    && store.shallow_perm(found_perm) == Perm::Exclusive =>
            {
                Adapted::Eq {
                    expected: *expected_inner,
                    found: *found_inner,
                    peeled: true,
                }
            }
            _ => Adapted::Eq {
                expected: expected.clone(),
                found: found.clone(),
                peeled: false,
            },
        };
    }

    // A unique slot: the move into `*T` makes the value unique, so the
    // wrapper peels on both sides and the referents equate.
    if let Ty::Unique(expected_inner) = store.shallow(expected) {
        let found = match store.shallow(found) {
            Ty::Unique(found_inner) => *found_inner,
            other => other,
        };
        return Adapted::Eq {
            expected: *expected_inner,
            found,
            peeled: true,
        };
    }

    match store.shallow(expected) {
        Ty::Borrow(expected_perm, expected_inner) => match store.shallow(found) {
            // An unresolved call result cannot decide: eagerly equating
            // the peeled inner would rigidly bind the result owned, then
            // conflict with a member scheme's borrow-typed return once it
            // resolves (ADR 0021's first-class borrow results).
            Ty::Var(_) => Adapted::Unresolved {
                visible_borrow: true,
            },
            found @ Ty::Proj(..) => Adapted::PeelableProjection {
                expected_inner: *expected_inner,
                found,
            },
            Ty::Borrow(found_perm, found_inner) => {
                let expected_perm = store.shallow_perm(expected_perm);
                let found_perm = store.shallow_perm(found_perm);
                if expected_perm == found_perm
                    || (expected_perm == Perm::Shared && found_perm == Perm::Exclusive)
                {
                    Adapted::Eq {
                        expected: *expected_inner,
                        found: *found_inner,
                        peeled: true,
                    }
                } else {
                    Adapted::Mismatch {
                        expected: expected.clone(),
                        found: found.clone(),
                    }
                }
            }
            Ty::Error => Adapted::Silent,
            found => Adapted::Eq {
                expected: *expected_inner,
                found,
                peeled: true,
            },
        },
        // An unresolved or irreducible slot fed a borrow: the donation
        // tier needs the slot's head, so the crossing waits for it.
        Ty::Var(_) | Ty::Proj(..)
            if matches!(store.shallow(found), Ty::Borrow(..)) =>
        {
            Adapted::Unresolved {
                visible_borrow: true,
            }
        }
        Ty::Var(_) if matches!(store.shallow(found), Ty::Var(_)) => Adapted::Unresolved {
            visible_borrow: false,
        },
        expected_shallow => match store.shallow(found) {
            Ty::Var(_) | Ty::Proj(..) => Adapted::Unresolved {
                visible_borrow: false,
            },
            Ty::Borrow(_, found_inner) => {
                // Returning a borrow into an owned result always donates a
                // retained reference; MIR already owns that return rule.
                if site == Site::Return {
                    return Adapted::Donate {
                        expected: expected.clone(),
                        found_inner: *found_inner,
                        donation: Donation::Share,
                    };
                }
                match donation_tier(catalog, &expected_shallow) {
                    Some(donation) => Adapted::Donate {
                        expected: expected.clone(),
                        found_inner: *found_inner,
                        donation,
                    },
                    None if matches!(expected_shallow, Ty::Param(_)) => Adapted::NoEvidence {
                        expected: expected.clone(),
                    },
                    None => Adapted::Eq {
                        expected: expected.clone(),
                        found: found.clone(),
                        peeled: true,
                    },
                }
            }
            Ty::Error => Adapted::Silent,
            _ => Adapted::Eq {
                expected: expected.clone(),
                found: found.clone(),
                peeled: false,
            },
        },
    }
}

/// The donation-tier lookup behind [`adapt`]'s borrow-into-owned arm and
/// finalize's pack/marker checks: how may an owned slot of this (resolved)
/// type be filled from a borrow? `None` means it may not — linear and
/// unique values refuse duplication, and a rigid parameter's proof goes
/// through its bounds.
#[allow(clippy::disallowed_methods)] // the judgment owns the tier queries
pub(crate) fn donation_tier(catalog: &TypeCatalog, ty: &Ty) -> Option<Donation> {
    match ty {
        Ty::Borrow(_, inner) => donation_tier(catalog, inner),
        Ty::Param(param) => {
            let bounds = catalog.param_bounds.get(param).cloned().unwrap_or_default();
            catalog.bounds_coerce_kind(&bounds).map(Donation::from)
        }
        Ty::Nominal(symbol, args) => catalog
            .coerce_kind_application(*symbol, args)
            .map(Donation::from)
            .or_else(|| catalog.implicitly_duplicable(ty).then_some(Donation::Share)),
        _ => catalog.implicitly_duplicable(ty).then_some(Donation::Share),
    }
}

/// Whether a `copy`-marked argument of this (resolved) type has the
/// evidence an explicit clone requires: a value-copy tier (`Copy` or
/// `CheapClone`), judged through a borrow and componentwise through
/// tuples. `Share` deliberately does not count — the marker asks for a
/// clone, not a retain.
pub(crate) fn copy_marker_evidence(catalog: &TypeCatalog, ty: &Ty) -> bool {
    match ty {
        Ty::Borrow(_, inner) => copy_marker_evidence(catalog, inner),
        Ty::Tuple(items) => items.iter().all(|item| copy_marker_evidence(catalog, item)),
        Ty::Error => true,
        Ty::Nominal(..) | Ty::Param(_) => matches!(
            donation_tier(catalog, ty),
            Some(Donation::Copy | Donation::CheapClone)
        ),
        _ => false,
    }
}

impl From<CoerceKind> for Donation {
    fn from(kind: CoerceKind) -> Self {
        match kind {
            CoerceKind::Copy => Donation::Copy,
            CoerceKind::CheapClone => Donation::CheapClone,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name_resolution::symbol::{StructId, Symbol, TypeParameterId};
    use crate::node_id::NodeID;
    use crate::types::catalog::StructInfo;
    use crate::types::ty::EffectRow;
    use crate::types::Level;

    fn func() -> Ty {
        Ty::Func(vec![], Box::new(int()), EffectRow::new(vec![], None))
    }

    fn int() -> Ty {
        Ty::Nominal(Symbol::Int, vec![])
    }

    fn borrow(perm: Perm, inner: Ty) -> Ty {
        Ty::Borrow(perm, Box::new(inner))
    }

    fn eq(expected: Ty, found: Ty, peeled: bool) -> Adapted {
        Adapted::Eq {
            expected,
            found,
            peeled,
        }
    }

    #[test]
    fn result_site_downgrades_exclusive_to_shared_and_nothing_else() {
        let mut store = VarStore::default();
        let catalog = TypeCatalog::default();
        let expected = borrow(Perm::Shared, int());
        let found = borrow(Perm::Exclusive, int());
        assert_eq!(
            adapt(&mut store, &catalog, &expected, &found, Site::Result),
            eq(int(), int(), true)
        );
        // The reverse direction stays invariant: equate unchanged.
        assert_eq!(
            adapt(&mut store, &catalog, &found, &expected, Site::Result),
            eq(found.clone(), expected.clone(), false)
        );
        // Non-borrow pairs stay invariant even when an argument-site rule
        // (auto-borrow, donation) would have applied.
        assert_eq!(
            adapt(&mut store, &catalog, &expected, &int(), Site::Result),
            eq(expected, int(), false)
        );
    }

    #[test]
    fn unique_expected_peels_on_both_sides() {
        let mut store = VarStore::default();
        let catalog = TypeCatalog::default();
        let expected = Ty::Unique(Box::new(int()));
        assert_eq!(
            adapt(&mut store, &catalog, &expected, &int(), Site::Argument),
            eq(int(), int(), true)
        );
        let found_unique = Ty::Unique(Box::new(int()));
        assert_eq!(
            adapt(&mut store, &catalog, &expected, &found_unique, Site::Argument),
            eq(int(), int(), true)
        );
    }

    #[test]
    fn borrow_slots_peel_matching_and_downgraded_permissions() {
        let mut store = VarStore::default();
        let catalog = TypeCatalog::default();
        let shared = borrow(Perm::Shared, int());
        let exclusive = borrow(Perm::Exclusive, int());
        assert_eq!(
            adapt(&mut store, &catalog, &shared, &shared, Site::Argument),
            eq(int(), int(), true)
        );
        assert_eq!(
            adapt(&mut store, &catalog, &shared, &exclusive, Site::Argument),
            eq(int(), int(), true)
        );
        // An exclusive slot fed a shared borrow does not adapt: the pair
        // equates unchanged so the mismatch names both borrows.
        assert_eq!(
            adapt(&mut store, &catalog, &exclusive, &shared, Site::Argument),
            Adapted::Mismatch {
                expected: exclusive.clone(),
                found: shared,
            }
        );
        // Auto-borrow: an owned value fills a borrow slot by peeling.
        assert_eq!(
            adapt(&mut store, &catalog, &exclusive, &int(), Site::Argument),
            eq(int(), int(), true)
        );
    }

    #[test]
    fn unresolved_operands_report_borrow_visibility() {
        let mut store = VarStore::default();
        let catalog = TypeCatalog::default();
        let var = Ty::Var(store.fresh_ty(Level(1), NodeID::ANY));
        let other_var = Ty::Var(store.fresh_ty(Level(1), NodeID::ANY));
        let shared = borrow(Perm::Shared, int());
        assert_eq!(
            adapt(&mut store, &catalog, &shared, &var, Site::Argument),
            Adapted::Unresolved {
                visible_borrow: true
            }
        );
        assert_eq!(
            adapt(&mut store, &catalog, &var, &shared, Site::Argument),
            Adapted::Unresolved {
                visible_borrow: true
            }
        );
        assert_eq!(
            adapt(&mut store, &catalog, &int(), &var, Site::Argument),
            Adapted::Unresolved {
                visible_borrow: false
            }
        );
        assert_eq!(
            adapt(&mut store, &catalog, &var, &other_var, Site::Argument),
            Adapted::Unresolved {
                visible_borrow: false
            }
        );
    }

    #[test]
    fn borrow_of_copy_donates_into_owned_slot() {
        let mut store = VarStore::default();
        let catalog = TypeCatalog::default();
        let found = borrow(Perm::Shared, int());
        assert_eq!(
            adapt(&mut store, &catalog, &int(), &found, Site::Argument),
            Adapted::Donate {
                expected: int(),
                found_inner: int(),
                donation: Donation::Copy,
            }
        );
    }

    #[test]
    fn rigid_slot_without_evidence_refuses_donation() {
        let mut store = VarStore::default();
        let mut catalog = TypeCatalog::default();
        let param = Symbol::TypeParameter(TypeParameterId::new(
            crate::front::module::ModuleId::Current,
            0,
        ));
        catalog.param_bounds.insert(param, vec![]);
        let expected = Ty::Param(param);
        let found = borrow(Perm::Shared, Ty::Param(param));
        assert_eq!(
            adapt(&mut store, &catalog, &expected, &found, Site::Argument),
            Adapted::NoEvidence { expected }
        );
    }

    #[test]
    fn linear_nominal_falls_through_to_plain_equality() {
        let mut store = VarStore::default();
        let mut catalog = TypeCatalog::default();
        let symbol = Symbol::Struct(StructId::new(crate::front::module::ModuleId::Current, 0));
        catalog.structs.insert(
            symbol,
            StructInfo {
                linear: true,
                ..StructInfo::default()
            },
        );
        let expected = Ty::Nominal(symbol, vec![]);
        let found = borrow(Perm::Shared, expected.clone());
        assert_eq!(
            adapt(&mut store, &catalog, &expected, &found, Site::Argument),
            eq(expected, found, true)
        );
    }

    #[test]
    fn return_site_donates_without_evidence() {
        let mut store = VarStore::default();
        let mut catalog = TypeCatalog::default();
        let symbol = Symbol::Struct(StructId::new(crate::front::module::ModuleId::Current, 0));
        catalog.structs.insert(
            symbol,
            StructInfo {
                linear: true,
                ..StructInfo::default()
            },
        );
        let expected = Ty::Nominal(symbol, vec![]);
        let found = borrow(Perm::Shared, expected.clone());
        assert_eq!(
            adapt(&mut store, &catalog, &expected, &found, Site::Return),
            Adapted::Donate {
                expected: expected.clone(),
                found_inner: expected,
                donation: Donation::Share,
            }
        );
    }

    #[test]
    fn error_operands_are_silent() {
        let mut store = VarStore::default();
        let catalog = TypeCatalog::default();
        let shared = borrow(Perm::Shared, int());
        assert_eq!(
            adapt(&mut store, &catalog, &shared, &Ty::Error, Site::Argument),
            Adapted::Silent
        );
        assert_eq!(
            adapt(&mut store, &catalog, &int(), &Ty::Error, Site::Argument),
            Adapted::Silent
        );
    }

    #[test]
    fn copy_marker_evidence_judges_through_borrows_and_tuples() {
        let catalog = TypeCatalog::default();
        assert!(copy_marker_evidence(&catalog, &int()));
        assert!(copy_marker_evidence(
            &catalog,
            &borrow(Perm::Shared, int())
        ));
        assert!(copy_marker_evidence(
            &catalog,
            &Ty::Tuple(vec![int(), int()])
        ));
        // A function value is retainable (`Share`) but not clonable
        // evidence: the marker demands a value-copy tier.
        assert!(!copy_marker_evidence(&catalog, &func()));
        assert!(!copy_marker_evidence(
            &catalog,
            &Ty::Tuple(vec![int(), func()])
        ));
    }

    #[test]
    fn donation_tier_peels_borrows_and_shares_duplicables() {
        let catalog = TypeCatalog::default();
        assert_eq!(donation_tier(&catalog, &int()), Some(Donation::Copy));
        assert_eq!(
            donation_tier(&catalog, &borrow(Perm::Shared, int())),
            Some(Donation::Copy)
        );
        assert_eq!(donation_tier(&catalog, &func()), Some(Donation::Share));
        assert_eq!(donation_tier(&catalog, &Ty::Unique(Box::new(int()))), None);
    }
}
