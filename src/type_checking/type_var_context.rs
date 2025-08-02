use ena::unify::{InPlace, InPlaceUnificationTable, NoError, Snapshot, UnifyKey, UnifyValue};

use crate::{
    builtins,
    expr_id::ExprID,
    ty::Ty2,
    type_var_id::{TypeVarID, TypeVarKind},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct VarKey(u32); // Only used with ena

impl UnifyKey for VarKey {
    type Value = Ty2;

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

impl UnifyValue for Ty2 {
    type Error = NoError;

    fn unify_values(a: &Self, b: &Self) -> Result<Self, NoError> {
        match (a, b) {
            (Ty2::TypeVar(_), _) => Ok(b.clone()),
            (_, Ty2::TypeVar(_)) => Ok(a.clone()),
            _ if a == b => Ok(a.clone()),
            _ => {
                tracing::error!("unable to unify values: {a:?}, {b:?}");
                Ok(Ty2::Void)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnificationEntry {
    Create {
        expr_id: ExprID,
        ty: Ty2,
        generation: u32,
    },
    Instantiated {
        expr_id: ExprID,
        canonical: TypeVarID,
        instantiated: Ty2,
        generation: u32,
    },
    Unify {
        expr_id: ExprID,
        before: Ty2,
        after: Ty2,
        generation: u32,
    },
}

#[derive(Debug, Clone, Default)]
pub struct TypeVarContext2 {
    table: InPlaceUnificationTable<VarKey>,
    kinds: Vec<(TypeVarKind, ExprID)>, // indexed by VarKey.0
    pub history: Vec<UnificationEntry>,
}

impl TypeVarContext2 {
    pub fn import_builtins(&mut self) {
        for builtin in builtins::builtins() {
            for var in builtin.unbound_vars {
                let kind = &var.kind;
                let key = self.table.new_key(Ty2::TypeVar(TypeVarID {
                    id: self.kinds.len() as u32,
                    kind: kind.clone(),
                    expr_id: var.expr_id,
                }));

                assert!(
                    key.0 == var.id,
                    "Builtin type vars are not in sync: {var:?} <> {key:?}"
                );

                self.kinds.push((kind.clone(), var.expr_id));
            }
        }
    }

    pub fn new_var(&mut self, kind: TypeVarKind, expr_id: ExprID, generation: u32) -> TypeVarID {
        let type_var = Ty2::TypeVar(TypeVarID {
            id: self.kinds.len() as u32,
            kind: kind.clone(),
            expr_id,
        });

        self.history.push(UnificationEntry::Create {
            expr_id,
            ty: type_var.clone(),
            generation,
        });

        let key = self.table.new_key(type_var);

        self.kinds.push((kind.clone(), expr_id));

        TypeVarID::new(key.0, kind, expr_id)
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

    pub fn iter(&mut self) -> impl Iterator<Item = (TypeVarID, Ty2)> {
        self.kinds.iter().enumerate().map(|(id, (kind, expr_id))| {
            (
                TypeVarID::new(id as u32, kind.clone(), *expr_id),
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

    pub fn try_probe(&mut self, var: &TypeVarID) -> Option<&Ty2> {
        self.table.try_probe_value(VarKey(var.id))
    }

    pub fn find(&mut self, var: &TypeVarID) -> TypeVarID {
        // We don't know anything about this so just return it as is
        if var.id as usize >= self.table.len() {
            return var.clone();
        }

        let id = self.table.find(VarKey(var.id));
        let (kind, expr_id) = self.kinds[id.0 as usize].clone();

        #[cfg(test)]
        tracing::trace!(
            "Finding {var:?} -> {:?}",
            TypeVarID::new(id.0, kind.clone(), expr_id)
        );

        TypeVarID::new(id.0, kind, expr_id)
    }

    pub fn probe(&mut self, var: &TypeVarID) -> Ty2 {
        self.table.probe_value(VarKey(var.id))
    }

    pub fn unify(&mut self, a: TypeVarID, b: TypeVarID, generation: u32) {
        if a == b {
            return;
        }

        let canonical_kind = if a.is_canonical() {
            Some((a.kind.clone(), a.expr_id))
        } else if b.is_canonical() {
            Some((b.kind.clone(), b.expr_id))
        } else {
            None
        };

        self.table.union(VarKey(a.id), VarKey(b.id));

        let found = self.table.find(VarKey(a.id));

        #[cfg(debug_assertions)]
        {
            if found == VarKey(a.id) {
                self.history.push(UnificationEntry::Unify {
                    expr_id: a.expr_id,
                    before: Ty2::TypeVar(a.clone()),
                    after: Ty2::TypeVar(b.clone()),
                    generation,
                })
            } else {
                self.history.push(UnificationEntry::Unify {
                    expr_id: b.expr_id,
                    before: Ty2::TypeVar(b.clone()),
                    after: Ty2::TypeVar(a.clone()),
                    generation,
                })
            }
        }

        if let Some((kind, expr_id)) = canonical_kind {
            let root = self.table.find(VarKey(a.id));
            self.kinds[root.0 as usize] = (kind, expr_id);
        }
    }

    pub fn kind(&self, var: TypeVarID) -> TypeVarKind {
        self.kinds[var.id as usize].clone().0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tracks_history() {
        let source = "
        func x(a) { a }
        func y(a) { a }
        func z(a) { a }
        x(y(z(123)))
        ";
        let checked = crate::check(source).unwrap();

        assert_eq!(checked.nth(3).unwrap(), Ty2::Int);
        // dump_unification_dot(
        //     &checked.type_var_context.history,
        //     "unification.dot",
        //     &checked.meta,
        //     &source.to_string(),
        // )
        // .unwrap();
    }
}
