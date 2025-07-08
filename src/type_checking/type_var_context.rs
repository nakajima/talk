use ena::unify::{InPlace, InPlaceUnificationTable, NoError, Snapshot, UnifyKey, UnifyValue};

use crate::{
    builtins,
    environment::free_type_vars,
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
            let type_vars = free_type_vars(&builtin.ty);
            for var in type_vars {
                self.kinds.push(var.kind);
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

        let ra = self.table.find(VarKey(a.id));
        let rb = self.table.find(VarKey(b.id));

        let kind_a = self.kinds[ra.0 as usize].clone();
        let kind_b = self.kinds[rb.0 as usize].clone();

        self.table.union(ra, rb);

        let root = self.table.find(ra);
        let new_kind = match (&kind_a, &kind_b) {
            (TypeVarKind::Placeholder(_), _) => kind_a,
            (_, TypeVarKind::Placeholder(_)) => kind_b,
            _ => kind_a,
        };
        self.kinds[root.0 as usize] = new_kind;
    }

    pub fn kind(&self, var: TypeVarID) -> TypeVarKind {
        self.kinds[var.id as usize].clone()
    }
}
