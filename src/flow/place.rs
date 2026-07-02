//! Places: the storage locations the flow checker tracks. A `Place` is a
//! root binding plus a field path — the successor of the legacy checker's
//! `KeyPath`, keeping its prefix-based disjointness so `x.name` and `x.age`
//! never conflict.

use crate::name_resolution::symbol::Symbol;

/// The symbol-rooted place an expression names (a variable or a chain of
/// stored-field accesses off one), if any. The single definition of "what
/// place does this expression touch" — the flow checker and MIR lowering
/// must agree on it for drop schedules to join up.
pub fn place_for_expr(
    types: &crate::types::TypeOutput,
    expr: &crate::hir::Expr,
) -> Option<Place> {
    match &expr.kind {
        crate::hir::ExprKind::Variable(name) => name.symbol().ok().map(Place::root),
        crate::hir::ExprKind::Member(Some(receiver), _) => {
            let field = crate::types::output::stored_field_symbol(
                types,
                expr.member_resolution.as_ref(),
            )?;
            Some(place_for_expr(types, receiver)?.child(field))
        }
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    pub root: Symbol,
    pub fields: Vec<Symbol>,
}

impl Place {
    pub fn root(root: Symbol) -> Self {
        Place {
            root,
            fields: vec![],
        }
    }

    pub fn child(&self, field: Symbol) -> Self {
        let mut fields = self.fields.clone();
        fields.push(field);
        Place {
            root: self.root,
            fields,
        }
    }

    /// `self` covers `other`: equal roots and `self`'s field path is a
    /// prefix of `other`'s (moving/dropping `x` affects `x.name`).
    pub fn contains(&self, other: &Self) -> bool {
        self.root == other.root
            && self.fields.len() <= other.fields.len()
            && self
                .fields
                .iter()
                .zip(&other.fields)
                .all(|(left, right)| left == right)
    }

    /// Two places alias unless they diverge at some field: `x.name` and
    /// `x.age` are disjoint; `x` overlaps both.
    pub fn overlaps(&self, other: &Self) -> bool {
        self.contains(other) || other.contains(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name_resolution::symbol::DeclaredLocalId;

    fn local(id: u32) -> Symbol {
        Symbol::DeclaredLocal(DeclaredLocalId(id))
    }

    fn field(id: u32) -> Symbol {
        Symbol::DeclaredLocal(DeclaredLocalId(1000 + id))
    }

    #[test]
    fn sibling_fields_are_disjoint() {
        let x = Place::root(local(0));
        let name = x.child(field(1));
        let age = x.child(field(2));
        assert!(!name.overlaps(&age));
        assert!(x.overlaps(&name));
        assert!(name.overlaps(&x));
        assert!(x.contains(&name));
        assert!(!name.contains(&x));
    }

    #[test]
    fn different_roots_never_overlap() {
        let x = Place::root(local(0));
        let y = Place::root(local(1));
        assert!(!x.overlaps(&y));
    }
}
