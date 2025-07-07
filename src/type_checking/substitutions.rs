use std::collections::HashMap;

use crate::{ty::Ty, type_var_id::TypeVarID};

#[derive(Default, Debug, Clone)]
pub struct Substitutions {
    storage: HashMap<TypeVarID, Ty>,
}

impl Substitutions {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, type_var: TypeVarID, ty: Ty) {
        self.storage.insert(type_var, ty);
    }

    pub fn get(&self, type_var: &TypeVarID) -> Option<&Ty> {
        self.storage.get(type_var)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&TypeVarID, &Ty)> {
        self.storage.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&TypeVarID, &mut Ty)> {
        self.storage.iter_mut()
    }

    pub fn len(&self) -> usize {
        self.storage.len()
    }

    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
    }

    /// Compose this substitution with `other`, applying all mappings in `self`
    /// to the values of `other` and then merging the two maps. Mappings in
    /// `self` take precedence on conflicts.
    pub fn compose(mut self, other: &Substitutions) -> Substitutions {
        use crate::constraint_solver::ConstraintSolver;

        let mut composed = HashMap::new();

        // Apply `self` to each entry in `other` first
        for (var, ty) in other.iter() {
            let applied = ConstraintSolver::substitute_ty_with_map(ty, &self);
            composed.insert(var.clone(), applied);
        }

        // Mappings from `self` override anything from `other`
        for (var, ty) in self.storage.drain() {
            composed.insert(var, ty);
        }

        Substitutions { storage: composed }
    }
}

impl FromIterator<(TypeVarID, Ty)> for Substitutions {
    fn from_iter<T: IntoIterator<Item = (TypeVarID, Ty)>>(iter: T) -> Self {
        Substitutions {
            storage: HashMap::from_iter(iter),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{constraint_solver::ConstraintSolver, type_var_id::TypeVarKind};

    #[test]
    fn composes_and_applies() {
        let t1 = TypeVarID::new(1, TypeVarKind::Unbound);
        let t2 = TypeVarID::new(2, TypeVarKind::Unbound);
        let t3 = TypeVarID::new(3, TypeVarKind::Unbound);

        let mut s1 = Substitutions::new();
        s1.insert(t1.clone(), Ty::TypeVar(t2.clone()));

        let mut s2 = Substitutions::new();
        s2.insert(t2.clone(), Ty::TypeVar(t3.clone()));
        s2.insert(t3.clone(), Ty::Int);

        let composed = s1.compose(&s2);

        assert_eq!(
            ConstraintSolver::apply(&Ty::TypeVar(t1.clone()), &composed, 0),
            Ty::Int
        );
        assert_eq!(
            ConstraintSolver::apply(&Ty::TypeVar(t2.clone()), &composed, 0),
            Ty::Int
        );
    }

    #[test]
    fn compose_overrides_other() {
        let tv = TypeVarID::new(1, TypeVarKind::Unbound);

        let mut s1 = Substitutions::new();
        s1.insert(tv.clone(), Ty::Int);

        let mut s2 = Substitutions::new();
        s2.insert(tv.clone(), Ty::Bool);

        let composed = s1.compose(&s2);

        assert_eq!(
            ConstraintSolver::apply(&Ty::TypeVar(tv.clone()), &composed, 0),
            Ty::Int
        );
    }
}
