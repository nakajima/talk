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
}

impl FromIterator<(TypeVarID, Ty)> for Substitutions {
    fn from_iter<T: IntoIterator<Item = (TypeVarID, Ty)>>(iter: T) -> Self {
        Substitutions {
            storage: HashMap::from_iter(iter),
        }
    }
}
