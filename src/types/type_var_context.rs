use std::collections::BTreeSet;

use ena::unify::{InPlace, InPlaceUnificationTable, Snapshot, UnifyKey, UnifyValue};

use crate::{
    builtins,
    type_checker::TypeError,
    types::{
        ty::{Primitive, Ty},
        type_var::{TypeVar, TypeVarDefault},
    },
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct VarKey(u32); // Only used with ena

impl UnifyValue for Ty {
    type Error = TypeError;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, TypeError> {
        match (lhs, rhs) {
            (Ty::Var(_), ty) | (ty, Ty::Var(_)) => Ok(ty.clone()),
            _ => Ok(lhs.clone()),
        }
    }
}

impl UnifyKey for VarKey {
    type Value = Ty;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(i: u32) -> Self {
        VarKey(i)
    }

    fn tag() -> &'static str {
        "VarKey"
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeVarContext {
    table: InPlaceUnificationTable<VarKey>,
}

impl TypeVarContext {
    pub fn import_builtins(&mut self) {
        for builtin in builtins::builtins() {
            for var in builtin.unbound_vars {
                let key = self
                    .table
                    .new_key(Ty::Var(TypeVar::new(self.next_id(), TypeVarDefault::None)));

                assert!(
                    key.0 == var.id,
                    "Builtin type vars are not in sync: {var:?} <> {key:?}"
                );
            }
        }
    }

    pub fn apply_defaults(&mut self) -> Result<(), TypeError> {
        let mut roots = BTreeSet::new();

        for i in 0..self.table.len() {
            roots.insert(self.table.find(VarKey(i as u32)));
        }

        for root in roots {
            match self.table.probe_value(root) {
                Ty::Var(type_var) => match type_var.1 {
                    TypeVarDefault::Int => self.unify(type_var, Ty::Primitive(Primitive::Int))?,
                    TypeVarDefault::Float => {
                        self.unify(type_var, Ty::Primitive(Primitive::Float))?
                    }
                    TypeVarDefault::None => continue,
                },
                _ => continue,
            }
        }

        Ok(())
    }

    pub fn resolve(&mut self, ty: &Ty) -> Ty {
        if let Ty::Var(var) = ty {
            self.table.probe_value(VarKey(var.0))
        } else {
            ty.clone()
        }
    }

    pub fn new_var(&mut self, default: TypeVarDefault) -> TypeVar {
        let type_var = TypeVar::new(self.next_id(), default);
        let _ = self.table.new_key(Ty::Var(type_var));
        type_var
    }

    pub fn next_id(&self) -> u32 {
        self.table.len() as u32
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }

    pub fn is_empty(&self) -> bool {
        self.table.len() == 0
    }

    pub fn unify(&mut self, type_var: TypeVar, ty: Ty) -> Result<(), TypeError> {
        self.table.unify_var_value(VarKey(type_var.0), ty)
    }

    pub fn snapshot(&mut self) -> Snapshot<InPlace<VarKey>> {
        self.table.snapshot()
    }

    pub fn commit(&mut self, snapshot: Snapshot<InPlace<VarKey>>) {
        self.table.commit(snapshot);
    }

    pub fn rollback(&mut self, snapshot: Snapshot<InPlace<VarKey>>) {
        self.table.rollback_to(snapshot);
    }
}
