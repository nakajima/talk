use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Display,
    hash::{DefaultHasher, Hash, Hasher},
};

use ena::unify::{EqUnifyValue, InPlace, InPlaceUnificationTable, Snapshot, UnifyKey, UnifyValue};
use tracing::trace_span;

use crate::{
    builtins,
    type_checker::TypeError,
    types::{
        constraint::Constraint,
        constraint_set::ConstraintSet,
        row::{ClosedRow, Row},
        ty::{InferredDefinition, Primitive, Ty, TypeParameter},
        type_var::{TypeVar, TypeVarKind},
        visitors::{
            definition_visitor::{TypeScheme, TypeSchemeKind},
            inference_visitor::{NominalRowSet, Substitutions},
        },
    },
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct VarKey(u32); // Only used with ena

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct RowVarKey(u32); // Only used with ena

impl UnifyValue for Ty {
    type Error = TypeError;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, TypeError> {
        match (lhs, rhs) {
            #[allow(clippy::panic)]
            (Ty::RawScheme(_), _) | (_, Ty::RawScheme(_)) => {
                panic!("Cannot unify raw scheme: {lhs:?}, {rhs:?}");
            }
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
                tracing::trace!("unify_values: {lhs} ⊔ {rhs}");
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
pub enum RowVarKind {
    Canonical,
    Instantiated,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct RowVar(pub u32, pub RowVarKind);

impl RowVar {
    pub fn new(id: u32, kind: RowVarKind) -> Self {
        Self(id, kind)
    }

    pub fn is_canonical(&self) -> bool {
        self.1 == RowVarKind::Canonical
    }
}

impl From<RowVar> for RowVarKey {
    fn from(val: RowVar) -> Self {
        RowVarKey(val.0)
    }
}

impl Default for RowVar {
    fn default() -> Self {
        RowVar(u32::MAX, RowVarKind::Canonical)
    }
}

impl Display for RowVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl UnifyKey for RowVarKey {
    type Value = Row;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(i: u32) -> Self {
        RowVarKey(i)
    }

    fn tag() -> &'static str {
        "RowKey"
    }
}

impl EqUnifyValue for ClosedRow {}

impl Display for TypeParameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl UnifyKey for TypeParameter {
    type Value = ();

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(i: u32) -> Self {
        TypeParameter(i)
    }

    fn tag() -> &'static str {
        "TypeParameter"
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum InstantiationKey {
    Key(u64),
}

impl InstantiationKey {
    pub fn one<A: std::hash::Hash>(a: &A) -> Self {
        let mut hasher = DefaultHasher::new();
        a.hash(&mut hasher);
        InstantiationKey::Key(hasher.finish())
    }

    pub fn two<A: std::hash::Hash, B: std::hash::Hash>(a: &A, b: &B) -> Self {
        let mut hasher = DefaultHasher::new();
        a.hash(&mut hasher);
        b.hash(&mut hasher);
        InstantiationKey::Key(hasher.finish())
    }
}

#[derive(Debug, Default)]
pub struct TypeVarContext {
    table: InPlaceUnificationTable<VarKey>,
    row_table: InPlaceUnificationTable<RowVarKey>,
    type_params_table: InPlaceUnificationTable<TypeParameter>,
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
                    TypeVarKind::BoolLiteral => {
                        self.unify_var_ty(type_var, Ty::Primitive(Primitive::Bool))?
                    }
                    TypeVarKind::Void => {
                        self.unify_var_ty(type_var, Ty::Primitive(Primitive::Void))?
                    }
                    _ => continue,
                },
                _ => continue,
            }
        }

        Ok(())
    }

    fn type_parameter_substitutions(
        &mut self,
        type_parameters: &[TypeParameter],
        kind: TypeVarKind,
    ) -> BTreeMap<TypeParameter, TypeVar> {
        type_parameters
            .iter()
            .map(|param| (*param, self.new_var(kind)))
            .collect()
    }

    pub(crate) fn instantiate(
        &mut self,
        scheme: &TypeScheme<InferredDefinition>,
        constraints: &mut ConstraintSet,
    ) -> Result<(Ty, Substitutions), TypeError> {
        tracing::debug!("instantiating scheme: {scheme}");

        let (instantiated, substitutions) = match scheme {
            TypeScheme {
                kind:
                    TypeSchemeKind::Nominal {
                        name,
                        quantified_vars,
                        canonical_rows,
                        ..
                    },
                ..
            } => {
                let type_parameter_substitutions =
                    self.type_parameter_substitutions(quantified_vars, TypeVarKind::Instantiated);
                let row_substitutions = self.row_var_substitutions(canonical_rows);
                let substitutions = Substitutions {
                    type_parameters: type_parameter_substitutions.clone(),
                    rows: row_substitutions.clone(),
                };

                for type_parameter in type_parameter_substitutions.keys() {
                    for constraint in
                        constraints.instantiate_type_parameter(*type_parameter, &substitutions)?
                    {
                        tracing::trace!(
                            "instantiated type parameter ({type_parameter}) constraint: {constraint}"
                        );
                        constraints.add(constraint);
                    }
                }

                for row_var in row_substitutions.keys() {
                    for constraint in constraints.instantiate_row_var(*row_var, &substitutions)? {
                        tracing::trace!(
                            "instantiated row var ({row_var:?}) constraint: {constraint}"
                        );
                        constraints.add(constraint);
                    }
                }

                #[allow(clippy::unwrap_used)]
                let nominal_ty = Ty::Nominal {
                    name: name.clone(),
                    properties: Row::Open(
                        *substitutions.get_row(&canonical_rows.properties).unwrap(),
                    ),
                    methods: Row::Open(*substitutions.get_row(&canonical_rows.methods).unwrap()),
                };

                // Return a Metatype wrapping the nominal, using the correct meta row vars
                #[allow(clippy::unwrap_used)]
                let metatype = Ty::Metatype {
                    ty: Box::new(nominal_ty),
                    properties: Row::Open(
                        *substitutions
                            .get_row(&canonical_rows.meta_properties)
                            .unwrap(),
                    ),
                    methods: Row::Open(
                        *substitutions.get_row(&canonical_rows.meta_methods).unwrap(),
                    ),
                };

                (metatype, substitutions)
            }
            TypeScheme {
                kind:
                    TypeSchemeKind::Func {
                        quantified_vars,
                        params,
                        returns,
                    },
                ..
            } => {
                let substitutions = Substitutions {
                    type_parameters: self
                        .type_parameter_substitutions(quantified_vars, TypeVarKind::Instantiated),
                    rows: Default::default(),
                };

                let params = params.clone().substituting(&substitutions)?;
                let returns = returns.substituting(&substitutions)?;

                (
                    Ty::Func {
                        params,
                        returns: Box::new(returns),
                    },
                    substitutions,
                )
            }
            _ => todo!(),
        };

        tracing::trace!("substitutions: {substitutions:#?}");

        Ok((instantiated, substitutions))
    }

    fn row_var_substitutions(
        &mut self,
        canonical_rows: &NominalRowSet,
    ) -> BTreeMap<RowVar, RowVar> {
        let mut result = BTreeMap::new();
        result.insert(
            canonical_rows.properties,
            self.new_row_var(RowVarKind::Instantiated),
        );
        result.insert(
            canonical_rows.methods,
            self.new_row_var(RowVarKind::Instantiated),
        );
        result.insert(
            canonical_rows.meta_methods,
            self.new_row_var(RowVarKind::Instantiated),
        );
        result.insert(
            canonical_rows.meta_properties,
            self.new_row_var(RowVarKind::Instantiated),
        );
        result
    }

    pub fn resolve(&mut self, ty: &Ty) -> Ty {
        self.resolve_with_seen(ty, &mut Default::default())
    }

    pub fn resolve_with_seen(&mut self, ty: &Ty, seen: &mut BTreeMap<Ty, Ty>) -> Ty {
        if let Some(seen_ty) = seen.get(ty) {
            return seen_ty.clone();
        }

        seen.insert(ty.clone(), ty.clone());

        let after = match ty {
            Ty::Scheme(_) | Ty::RawScheme(_) => ty.clone(),
            Ty::Metatype {
                ty,
                properties,
                methods,
            } => Ty::Metatype {
                ty: Box::new(self.resolve_with_seen(ty, seen)),
                properties: self.resolve_row_with_seen(properties, seen),
                methods: self.resolve_row_with_seen(methods, seen),
            },
            Ty::TypeParameter(_) => ty.clone(),
            Ty::Var(var) => {
                let new_ty = self.table.probe_value(VarKey(var.id));
                match new_ty {
                    Ty::Var(new_var) if new_var == *var => new_ty, // Same var, no progress
                    Ty::Var(_) => self.resolve_with_seen(&new_ty, seen), // Different var, keep resolving
                    _ => self.resolve_with_seen(&new_ty, seen),
                }
            }
            Ty::Func { params, returns } => Ty::Func {
                params: self.resolve_row_with_seen(params, seen),
                returns: Box::new(self.resolve_with_seen(returns, seen)),
            },
            Ty::Primitive(..) => ty.clone(),
            Ty::Nominal {
                name,
                properties,
                methods,
            } => {
                // Resolve rows and specialize generic params to current bindings
                let resolved_properties = self.resolve_row_with_seen(properties, seen);
                let resolved_methods = self.resolve_row_with_seen(methods, seen);

                Ty::Nominal {
                    name: name.clone(),
                    properties: resolved_properties,
                    methods: resolved_methods,
                }
            }
            Ty::Product(row) => Ty::Product(self.resolve_row_with_seen(row, seen)),
            #[allow(clippy::todo)]
            Ty::Sum(..) => todo!(),
            #[allow(clippy::todo)]
            Ty::Label(label, value) => {
                Ty::Label(label.clone(), Box::new(self.resolve_with_seen(value, seen)))
            }
        };

        seen.insert(ty.clone(), after.clone());

        if ty != &after {
            tracing::trace!("resolve ty: before: {ty} after: {after}");
        }

        after
    }

    pub fn resolve_row_with_seen(&mut self, row: &Row, seen: &mut BTreeMap<Ty, Ty>) -> Row {
        let after = match row {
            Row::Open(row_var) => {
                if matches!(row_var.1, RowVarKind::Canonical) {
                    return row.clone();
                }

                let resolved_row = self.row_table.probe_value(RowVarKey(row_var.0));
                if matches!(resolved_row, Row::Closed(_)) {
                    self.resolve_row_with_seen(&resolved_row, seen)
                } else {
                    resolved_row
                }
            }
            Row::Closed(ClosedRow { fields, values }) => Row::Closed(ClosedRow {
                fields: fields.to_vec(),
                values: values
                    .iter()
                    .map(|v| self.resolve_with_seen(v, seen))
                    .collect(),
            }),
        };

        if row != &after {
            tracing::trace!("resolve row: before: {row:?} after: {after:?}");
        }

        after
    }

    pub fn new_row_var(&mut self, kind: RowVarKind) -> RowVar {
        let key = RowVarKey(self.row_table.len() as u32);
        let var = RowVar::new(key.0, kind);
        let _ = self.row_table.new_key(Row::Open(var));
        var
    }

    pub fn new_var(&mut self, default: TypeVarKind) -> TypeVar {
        let type_var = TypeVar::new(self.next_id(), default);
        let _ = self.table.new_key(Ty::Var(type_var));
        type_var
    }

    pub fn new_type_param(&mut self) -> TypeParameter {
        let var = TypeParameter(self.type_params_table.len() as u32);
        let _ = self.type_params_table.new_key(());
        var
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
        let seen = &mut Default::default();
        if self.resolve_row_with_seen(&Row::Open(row_var), seen)
            == self.resolve_row_with_seen(&row, seen)
        {
            return Ok(());
        }

        tracing::trace!("unify_row_var: {row_var:?}, row: {row:?}");

        self.row_table.unify_var_value(row_var, row)?;

        Ok(())
    }

    pub fn unify_type_params(
        &mut self,
        lhs: TypeParameter,
        rhs: TypeParameter,
    ) -> Result<(), TypeError> {
        self.type_params_table.unify_var_var(lhs, rhs).ok();
        Ok(())
    }

    pub fn unify_var_ty(&mut self, mut type_var: TypeVar, mut ty: Ty) -> Result<(), TypeError> {
        let seen = &mut Default::default();

        if self.resolve_with_seen(&Ty::Var(type_var), seen) == self.resolve_with_seen(&ty, seen) {
            return Ok(());
        }

        if occurs(type_var, &ty, self) {
            tracing::error!("Occurs check failed for {type_var:?} in {ty:?}");
            return Err(TypeError::OccursConflict);
        }

        tracing::trace!("unify: {type_var:?} ⊔ {ty:?}");

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
        let seen = &mut Default::default();
        let lhs = self.resolve_with_seen(lhs, seen);
        let rhs = self.resolve_with_seen(rhs, seen);
        let _s = trace_span!("unify", lhs = format!("{lhs}"), rhs = format!("{rhs}")).entered();

        match (&lhs, &rhs) {
            (Ty::Var(lhs_var), Ty::Var(rhs_var)) => {
                let picked = Ty::unify_values(&lhs, &rhs)?;
                self.unify_var_ty(if picked == lhs { *rhs_var } else { *lhs_var }, picked)
            }
            (Ty::Var(var), ty) | (ty, Ty::Var(var)) => self.unify_var_ty(*var, ty.clone()),
            (Ty::Nominal { name: lhs_name, .. }, Ty::Nominal { name: rhs_name, .. }) => {
                // Only unify nominal types by identity (same declaration).
                if lhs_name != rhs_name {
                    return Err(TypeError::Mismatch(lhs.to_string(), rhs.to_string()));
                }
                Ok(())
            }
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
                self.unify_ty_ty(lhs_returns, rhs_returns)?;

                Ok(())
            }
            (Ty::TypeParameter(lhs), Ty::TypeParameter(rhs)) => {
                self.type_params_table.unify_var_var(*lhs, *rhs).ok();
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
        Ty::Func { returns, .. } => occurs(tv, &returns, ctx),
        Ty::Product(Row::Closed(cr)) | Ty::Sum(Row::Closed(cr)) => {
            cr.values.iter().any(|v| occurs(tv, v, ctx))
        }
        _ => false,
    }
}
