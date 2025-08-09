use std::{collections::BTreeSet, fmt::Display};

use ena::unify::{EqUnifyValue, InPlace, InPlaceUnificationTable, Snapshot, UnifyKey, UnifyValue};
use tracing::trace_span;

use crate::{
    builtins,
    type_checker::TypeError,
    types::{
        row::{ClosedRow, Row},
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
                if lhs.kind.is_more_specific_than(&rhs.kind) {
                    return Ok(Ty::Var(*lhs));
                }

                if rhs.kind.is_more_specific_than(&lhs.kind) {
                    return Ok(Ty::Var(*rhs));
                }

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

impl UnifyValue for Row {
    type Error = TypeError;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, TypeError> {
        match (lhs, rhs) {
            (Row::Open(lhs), Row::Open(rhs)) => {
                // Choose the older one
                if lhs.0 > rhs.0 {
                    Ok(Row::Open(*rhs))
                } else {
                    Ok(Row::Open(*lhs))
                }
            }
            (Row::Open(..), row @ Row::Closed(..)) | (row @ Row::Closed(..), Row::Open(..)) => {
                Ok(row.clone())
            }
            (Row::Closed(lhs), Row::Closed(rhs)) if lhs.values.len() == rhs.values.len() => {
                let mut new_values = vec![];
                for (lhs_value, rhs_value) in lhs.values.iter().zip(&rhs.values) {
                    new_values.push(Ty::unify_values(lhs_value, rhs_value)?);
                }

                Ok(Row::Closed(ClosedRow {
                    fields: lhs.fields.clone(),
                    values: new_values,
                }))
            }
            _ => Err(TypeError::Unknown(format!(
                "Cannot unify rows: {lhs:?} <> {rhs:?}"
            ))),
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

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct RowVar(u32);

impl RowVar {
    pub fn new(id: u32) -> Self {
        Self(id)
    }
}

impl Display for RowVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl UnifyKey for RowVar {
    type Value = Row;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(i: u32) -> Self {
        RowVar(i)
    }

    fn tag() -> &'static str {
        "RowKey"
    }
}

impl EqUnifyValue for ClosedRow {}

#[derive(Debug, Default)]
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
        let after = match ty {
            Ty::Var(var) => {
                let new_ty = self.table.probe_value(VarKey(var.id));
                match new_ty {
                    Ty::Var(new_var) if new_var == *var => new_ty, // Same var, no progress
                    Ty::Var(_) => self.resolve(&new_ty),           // Different var, keep resolving
                    _ => self.resolve(&new_ty),
                }
            }
            Ty::Func {
                params,
                returns,
                generic_constraints,
            } => Ty::Func {
                params: params.iter().map(|p| self.resolve(p)).collect(),
                returns: Box::new(self.resolve(returns)),
                generic_constraints: generic_constraints.clone(), // TODO: might need to resolve types in constraints
            },
            Ty::Primitive(..) => ty.clone(),
            Ty::Nominal {
                name,
                properties,
                methods,
                type_params,
                instantiations,
            } => Ty::Nominal {
                name: name.clone(),
                properties: self.resolve_row(properties),
                methods: self.resolve_row(methods),
                type_params: type_params.clone(),
                instantiations: instantiations.clone(), // TODO: might need to resolve types in instantiations
            },
            Ty::Product(row) => Ty::Product(self.resolve_row(row)),
            #[allow(clippy::todo)]
            Ty::Sum(..) => todo!(),
            #[allow(clippy::todo)]
            Ty::Label(label, value) => Ty::Label(label.clone(), Box::new(self.resolve(value))),
        };

        if ty != &after {
            tracing::trace!("resolve ty: before: {ty:?} after: {after:?}");
        }

        after
    }

    pub fn resolve_row(&mut self, row: &Row) -> Row {
        let after = match row {
            Row::Open(row_var) => {
                let resolved_row = self.row_table.probe_value(*row_var);
                if matches!(resolved_row, Row::Closed(_)) {
                    self.resolve_row(&resolved_row)
                } else {
                    resolved_row
                }
            }
            Row::Closed(ClosedRow { fields, values }) => Row::Closed(ClosedRow {
                fields: fields.to_vec(),
                values: values.iter().map(|v| self.resolve(v)).collect(),
            }),
        };

        if row != &after {
            tracing::trace!("resolve row: before: {row:?} after: {after:?}");
        }

        after
    }

    pub fn new_row_var(&mut self) -> RowVar {
        let var = RowVar(self.row_table.len() as u32);
        let _ = self.row_table.new_key(Row::Open(var));
        var
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

    pub fn unify_row_var(&mut self, row_var: RowVar, row: Row) -> Result<(), TypeError> {
        if self.resolve_row(&Row::Open(row_var)) == self.resolve_row(&row) {
            return Ok(());
        }

        tracing::trace!("unify_row_var: {row_var:?}, row: {row:?}");

        self.row_table.unify_var_value(row_var, row)?;

        Ok(())
    }

    pub fn unify_var_ty(&mut self, mut type_var: TypeVar, mut ty: Ty) -> Result<(), TypeError> {
        if self.resolve(&Ty::Var(type_var)) == self.resolve(&ty) {
            return Ok(());
        }

        if occurs(type_var, &ty, self) {
            tracing::error!("Occurs check failed for {type_var:?} in {ty:?}");
            return Err(TypeError::OccursConflict);
        }

        tracing::trace!("unify: {type_var:?} <> {ty:?}");

        // Check if this type var is already bound to something
        let current = self.table.probe_value(VarKey(type_var.id));
        match &current {
            Ty::Var(v) if v.id == type_var.id => {
                // Not yet bound, proceed with unification
            }
            _ => {
                // Already bound, need to unify with the existing value
                return self.unify_ty_ty(&current, &ty);
            }
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
                    ..
                },
                Ty::Func {
                    params: rhs_params,
                    returns: rhs_returns,
                    ..
                },
            ) => {
                if lhs_params.len() != rhs_params.len() {
                    return Err(TypeError::ArgumentError(format!(
                        "Function parameter count mismatch: {} vs {}",
                        lhs_params.len(),
                        rhs_params.len()
                    )));
                }
                
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

fn occurs(tv: TypeVar, ty: &Ty, ctx: &mut TypeVarContext) -> bool {
    match ctx.resolve(ty) {
        Ty::Var(tv2) => tv == tv2,
        Ty::Func {
            params, returns, ..
        } => params.iter().any(|p| occurs(tv, p, ctx)) || occurs(tv, &returns, ctx),
        Ty::Product(Row::Closed(cr)) | Ty::Sum(Row::Closed(cr)) => {
            cr.values.iter().any(|v| occurs(tv, v, ctx))
        }
        _ => false,
    }
}
