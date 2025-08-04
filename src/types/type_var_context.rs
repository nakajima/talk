use std::collections::BTreeSet;

use ena::unify::{EqUnifyValue, InPlace, InPlaceUnificationTable, Snapshot, UnifyKey, UnifyValue};
use tracing::trace_span;

use crate::{
    builtins,
    type_checker::TypeError,
    types::{
        row::{ClosedRow, Row, RowVar},
        ty::{Primitive, Ty},
        type_var::{TypeVar, TypeVarKind},
    },
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct VarKey(u32); // Only used with ena

impl UnifyValue for Ty {
    type Error = TypeError;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, TypeError> {
        match (lhs, rhs) {
            (Ty::Var(lhs), Ty::Var(rhs)) => {
                if lhs.kind == TypeVarKind::None && rhs.kind != TypeVarKind::None {
                    return Ok(Ty::Var(*rhs));
                }

                if lhs.kind != TypeVarKind::None && rhs.kind == TypeVarKind::None {
                    return Ok(Ty::Var(*lhs));
                }

                if lhs.id > rhs.id {
                    Ok(Ty::Var(*lhs))
                } else {
                    Ok(Ty::Var(*rhs))
                }
            }
            (Ty::Var(_), ty) | (ty, Ty::Var(_)) => Ok(ty.clone()),
            _ => {
                tracing::trace!("unify_values: {lhs:?} <> {rhs:?}");
                Ok(lhs.clone())
            }
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

impl EqUnifyValue for ClosedRow {}

impl UnifyKey for RowVar {
    type Value = Option<ClosedRow>;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "TypeVar"
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeVarContext {
    table: InPlaceUnificationTable<VarKey>,
    row_table: InPlaceUnificationTable<RowVar>,
}

impl TypeVarContext {
    pub fn import_builtins(&mut self) {
        for builtin in builtins::builtins() {
            for var in builtin.unbound_vars {
                let key = self
                    .table
                    .new_key(Ty::Var(TypeVar::new(self.next_id(), TypeVarKind::None)));

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

        tracing::trace!("applying type var defaults to {roots:?}");

        for root in roots {
            tracing::trace!("{:?}", self.table.probe_value(root));
            match self.table.probe_value(root) {
                Ty::Var(type_var) => match type_var.kind {
                    TypeVarKind::IntLiteral => {
                        self.unify_var_ty(type_var, Ty::Primitive(Primitive::Int))?
                    }
                    TypeVarKind::FloatLiteral => {
                        self.unify_var_ty(type_var, Ty::Primitive(Primitive::Float))?
                    }
                    _ => continue,
                },
                _ => continue,
            }
        }

        Ok(())
    }

    pub fn resolve(&mut self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(var) => {
                let new_ty = self.table.probe_value(VarKey(var.id));
                match new_ty {
                    Ty::Var(new_var) if new_var == *var => new_ty, // Same var, no progress
                    Ty::Var(_) => self.resolve(&new_ty),           // Different var, keep resolving
                    _ => self.resolve(&new_ty),
                }
            }
            Ty::Func { params, returns } => Ty::Func {
                params: params.iter().map(|p| self.resolve(p)).collect(),
                returns: Box::new(self.resolve(returns)),
            },
            Ty::Primitive(..) => ty.clone(),
            Ty::Product(row) => match row {
                Row::Open(row_var) => Ty::Product(Row::Open(self.row_table.find(*row_var))),
                Row::Closed(ClosedRow { fields, values }) => Ty::Product(Row::Closed(ClosedRow {
                    fields: fields.to_vec(),
                    values: values.iter().map(|v| self.resolve(v)).collect(),
                })),
            },
            #[allow(clippy::todo)]
            Ty::Sum(..) => todo!(),
            #[allow(clippy::todo)]
            Ty::Label(label, value) => Ty::Label(label.clone(), Box::new(self.resolve(value))),
        }
    }

    pub fn new_row_var(&mut self) -> RowVar {
        self.row_table.new_key(None)
    }

    pub fn new_var(&mut self, default: TypeVarKind) -> TypeVar {
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

    pub fn unify_var_ty(&mut self, mut type_var: TypeVar, mut ty: Ty) -> Result<(), TypeError> {
        tracing::trace!("unify: {type_var:?} <> {ty:?}");

        if type_var.kind == TypeVarKind::Canonical {
            return Err(TypeError::Unknown(
                "Cannot unify canonical generic parameter".to_string(),
            ));
        }

        if let Ty::Var(ty_var) = &mut ty
            && ty_var.kind != TypeVarKind::None
        {
            // Copy the default over
            type_var.kind = ty_var.kind;
        }

        self.table.unify_var_value(VarKey(type_var.id), ty)
    }

    pub fn unify_ty_ty(&mut self, lhs: &Ty, rhs: &Ty) -> Result<(), TypeError> {
        let lhs = self.resolve(lhs);
        let rhs = self.resolve(rhs);
        let _s = trace_span!("unify", lhs = format!("{lhs:?}"), rhs = format!("{rhs:?}")).entered();

        match (&lhs, &rhs) {
            (Ty::Var(lhs_var), Ty::Var(rhs_var)) => {
                let picked = Ty::unify_values(&lhs, &rhs)?;
                self.unify_var_ty(if picked == lhs { *rhs_var } else { *lhs_var }, picked)
            }
            (Ty::Var(var), ty) | (ty, Ty::Var(var)) => self.unify_var_ty(*var, ty.clone()),
            (
                Ty::Func {
                    params: lhs_params,
                    returns: lhs_returns,
                },
                Ty::Func {
                    params: rhs_params,
                    returns: rhs_returns,
                },
            ) => {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    self.unify_ty_ty(lhs, rhs)?;
                }

                self.unify_ty_ty(lhs_returns, rhs_returns)?;

                Ok(())
            }
            _ => {
                if lhs == rhs {
                    Ok(())
                } else {
                    Err(TypeError::Mismatch(lhs.to_string(), rhs.to_string()))
                }
            }
        }
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
