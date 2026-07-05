use super::*;

/// Normalize the head of a type: reduce an associated-type projection
/// through the conformance table when its base's head is concrete
/// (type-family top-level reaction, OutsideIn(X) JFP 2011 §7; instance
/// reduction per Chakravarty et al., ICFP 2005). Irreducible projections
/// (rigid base, or no binding) come back as `Proj`.
pub fn normalize_ty(store: &mut VarStore, catalog: &TypeCatalog, ty: &Ty) -> Ty {
    match store.shallow(ty) {
        Ty::Proj(base, protocol, assoc) => {
            let base = normalize_ty(store, catalog, &base);
            let projection_base = match &base {
                Ty::Borrow(_, inner) => normalize_ty(store, catalog, inner),
                other => other.clone(),
            };
            if let Ty::Nominal(symbol, args) = &projection_base
                && let Some(reduced) = reduce_projection(catalog, *symbol, args, protocol, assoc)
            {
                return normalize_ty(store, catalog, &reduced);
            }
            // A projection off the protocol's own Self param is the assoc
            // param itself: within P's context, `Self.A` ≡ `A`.
            if projection_base == Ty::Param(protocol) {
                return Ty::Param(assoc);
            }
            Ty::Proj(Box::new(base), protocol, assoc)
        }
        // Nested borrows collapse once a solved variable exposes the
        // inner borrow (the fold-time collapse can't see through vars).
        Ty::Borrow(perm, inner) => {
            let inner = store.shallow(&inner);
            let inner = normalize_ty(store, catalog, &inner);
            crate::types::ty::collapse_borrow(perm, inner)
        }
        Ty::Any { protocol, assoc } => Ty::Any {
            protocol,
            assoc: assoc
                .into_iter()
                .map(|(symbol, ty)| (symbol, normalize_ty(store, catalog, &ty)))
                .collect(),
        },
        other => other,
    }
}

/// Reduce one associated-type projection `Base.assoc` (with `Base`'s head
/// already a concrete `Nominal(symbol, args)`) through the conformance table:
/// bind the conformance row's rigid `self_args` against the head's `args`
/// (the instance binding of Hall et al., TOPLAS 1996) and substitute into the
/// assoc binding. `None` if no conformance provides the binding (the
/// projection stays stuck). Shared by the solver's `normalize_ty` and the
/// lowerer's post-solve normalizer so the reduction rule has one definition.
pub(crate) fn reduce_projection(
    catalog: &TypeCatalog,
    symbol: Symbol,
    args: &[Ty],
    protocol: Symbol,
    assoc: Symbol,
) -> Option<Ty> {
    let conformance = catalog.conformances.get(&(symbol, protocol))?;
    let binding = conformance.assoc.get(&assoc)?;
    let mut substitution = FxHashMap::default();
    for (pattern, actual) in conformance.self_args.iter().zip(args) {
        bind_param_pattern(pattern, actual, &mut substitution);
    }
    Some(binding.substitute(&substitution, &Default::default(), &Default::default()))
}

/// A projection whose base is still a unification variable cannot react yet
/// (the FLATTEN-style wait in OutsideIn's canonicalization): defer it.
pub(super) fn stuck_projection(store: &mut VarStore, ty: &Ty) -> bool {
    match ty {
        Ty::Proj(base, _, _) => {
            let base = store.shallow(base);
            matches!(base, Ty::Var(_)) || stuck_projection(store, &base)
        }
        _ => false,
    }
}
