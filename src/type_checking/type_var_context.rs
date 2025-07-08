use ena::unify::{InPlace, InPlaceUnificationTable, NoError, Snapshot, UnifyKey, UnifyValue};

use crate::{
    builtins,
    ty::Ty,
    type_var_id::{TypeVarID, TypeVarKind},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct VarKey(u32); // Only used with ena

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

impl UnifyValue for Ty {
    type Error = NoError;

    fn unify_values(a: &Self, b: &Self) -> Result<Self, NoError> {
        match (a, b) {
            (Ty::TypeVar(_), _) => Ok(b.clone()),
            (_, Ty::TypeVar(_)) => Ok(a.clone()),
            _ if a == b => Ok(a.clone()),
            _ => {
                tracing::error!("unable to unify values: {a:?}, {b:?}");
                Ok(Ty::Void)
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeVarContext {
    table: InPlaceUnificationTable<VarKey>,
    kinds: Vec<TypeVarKind>, // indexed by VarKey.0
}

impl TypeVarContext {
    pub fn import_builtins(&mut self) {
        for builtin in builtins::builtins() {
            for var in builtin.unbound_vars {
                let kind = &var.kind;
                let key = self.table.new_key(Ty::TypeVar(TypeVarID {
                    id: self.kinds.len() as u32,
                    kind: kind.clone(),
                }));

                assert!(
                    key.0 == var.id,
                    "Builtin type vars are not in sync: {var:?} <> {key:?}"
                );

                self.kinds.push(kind.clone());
            }
        }
    }

    pub fn new_var(&mut self, kind: TypeVarKind) -> TypeVarID {
        let key = self.table.new_key(Ty::TypeVar(TypeVarID {
            id: self.kinds.len() as u32,
            kind: kind.clone(),
        }));

        self.kinds.push(kind.clone());

        TypeVarID::new(key.0, kind)
    }

    pub fn next_id(&self) -> usize {
        self.kinds.len()
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }

    pub fn is_empty(&self) -> bool {
        self.table.len() == 0
    }

    pub fn iter(&mut self) -> impl Iterator<Item = (TypeVarID, Ty)> {
        self.kinds.iter().enumerate().map(|(id, kind)| {
            (
                TypeVarID::new(id as u32, kind.clone()),
                self.table.probe_value(VarKey(id as u32)),
            )
        })
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

    pub fn try_probe(&mut self, var: &TypeVarID) -> Option<&Ty> {
        self.table.try_probe_value(VarKey(var.id))
    }

    pub fn find(&mut self, var: &TypeVarID) -> TypeVarID {
        // We don't know anything about this so just return it as is
        if var.id as usize >= self.table.len() {
            return var.clone();
        }

        let id = self.table.find(VarKey(var.id));
        let kind = self.kinds[id.0 as usize].clone();
        TypeVarID::new(id.0, kind)
    }

    pub fn probe(&mut self, var: &TypeVarID) -> Ty {
        self.table.probe_value(VarKey(var.id))
    }

    pub fn unify_value(&mut self, a: TypeVarID, b: Ty) {
        if a.is_canonical() {
            return;
        }

        self.table.union_value(VarKey(a.id), b);
    }

    pub fn unify(&mut self, a: TypeVarID, b: TypeVarID) {
        if a.is_canonical() || b.is_canonical() {
            return;
        }

        self.table.union(VarKey(a.id), VarKey(b.id));
    }

    pub fn kind(&self, var: TypeVarID) -> TypeVarKind {
        self.kinds[var.id as usize].clone()
    }
}
