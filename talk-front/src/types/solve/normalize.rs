use super::*;

/// Normalize the head of a type: reduce an associated-type projection
/// through the conformance table when its base's head is concrete.
pub fn normalize_ty(store: &mut VarStore, catalog: &TypeCatalog, ty: &Ty) -> Ty {
    match store.shallow(ty) {
        Ty::Proj(base, protocol, assoc) => {
            let protocol = ProtocolRef {
                protocol: protocol.protocol,
                args: protocol
                    .args
                    .iter()
                    .map(|arg| catalog.canonical_conformance_arg(normalize_ty(store, catalog, arg)))
                    .collect(),
            };
            let base = normalize_ty(store, catalog, &base);
            let projection_base = match &base {
                Ty::Borrow(_, inner) => normalize_ty(store, catalog, inner),
                other => other.clone(),
            };
            if let Ty::Nominal(symbol, args) = &projection_base
                && !protocol.has_unification_vars()
                && let Some(reduced) = reduce_projection(catalog, *symbol, args, &protocol, assoc)
            {
                return normalize_ty(store, catalog, &reduced);
            }
            if let Ty::Any {
                protocol: existential_protocol,
                assoc: overrides,
            } = &projection_base
                && existential_protocol == &protocol
                && let Some((_, reduced)) = overrides.iter().find(|(symbol, _)| *symbol == assoc)
            {
                return normalize_ty(store, catalog, reduced);
            }
            if projection_base == Ty::Param(protocol.protocol) {
                return Ty::Param(assoc);
            }
            Ty::Proj(Box::new(base), protocol, assoc)
        }
        Ty::Borrow(perm, inner) => {
            let inner = store.shallow(&inner);
            let inner = normalize_ty(store, catalog, &inner);
            crate::types::ty::collapse_borrow(perm, inner)
        }
        Ty::Any { protocol, assoc } => Ty::Any {
            protocol: ProtocolRef {
                protocol: protocol.protocol,
                args: protocol
                    .args
                    .iter()
                    .map(|arg| normalize_ty(store, catalog, arg))
                    .collect(),
            },
            assoc: assoc
                .into_iter()
                .map(|(symbol, ty)| (symbol, normalize_ty(store, catalog, &ty)))
                .collect(),
        },
        other => other,
    }
}

/// Reduce one associated-type projection through a selected conformance row.
pub(crate) fn reduce_projection(
    catalog: &TypeCatalog,
    symbol: Symbol,
    args: &[Ty],
    protocol: &ProtocolRef,
    assoc: Symbol,
) -> Option<Ty> {
    let matches = catalog.matching_conformances(symbol, args, protocol);
    let [matched] = matches.as_slice() else {
        return None;
    };
    let binding = matched.conformance.assoc.get(&assoc)?;
    Some(binding.substitute(
        &matched.substitution,
        &Default::default(),
        &Default::default(),
    ))
}

/// A projection whose base is still a unification variable cannot react yet.
pub(super) fn stuck_projection(store: &mut VarStore, ty: &Ty) -> bool {
    match ty {
        Ty::Proj(base, protocol, _) => {
            let base = store.shallow(base);
            let protocol_stuck = protocol.args.iter().any(|arg| {
                let arg = store.shallow(arg);
                matches!(arg, Ty::Var(_)) || stuck_projection(store, &arg)
            });
            protocol_stuck || matches!(base, Ty::Var(_)) || stuck_projection(store, &base)
        }
        _ => false,
    }
}
