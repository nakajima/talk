use ena::unify::{InPlace, InPlaceUnificationTable, NoError, Snapshot, UnifyKey, UnifyValue};

use crate::{
    builtins,
    type_checker::TypeError,
    types::{ty::Ty, type_var::TypeVar},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct VarKey(u32); // Only used with ena

impl UnifyValue for Ty {
    type Error = TypeError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, TypeError> {
        todo!()
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
                let key = self.table.new_key(Ty::Var(TypeVar::new(self.next_id())));

                assert!(
                    key.0 == var.id,
                    "Builtin type vars are not in sync: {var:?} <> {key:?}"
                );
            }
        }
    }

    pub fn new_var(&mut self) -> TypeVar {
        let type_var = TypeVar::new(self.next_id());
        let key = self.table.new_key(Ty::Var(type_var));
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
