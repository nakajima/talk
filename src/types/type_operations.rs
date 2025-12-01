use std::{cell::RefCell, collections::BTreeMap, rc::Rc};

use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        infer_row::{InferRow, RowMetaId, RowParamId, RowTail, normalize_row},
        infer_ty::{InferTy, Level, Meta, MetaVarId, TypeParamId},
        solve_context::Solve,
        type_error::TypeError,
        type_session::{TypeDefKind, TypeSession},
    },
};

#[derive(Clone)]
pub struct UnificationSubstitutions {
    pub row: FxHashMap<RowMetaId, InferRow>,
    pub ty: FxHashMap<MetaVarId, InferTy>,
    pub meta_levels: Rc<RefCell<FxHashMap<Meta, Level>>>,
}

impl UnificationSubstitutions {
    pub fn extend(&mut self, substitutions: &UnificationSubstitutions) {
        self.row.extend(substitutions.row.clone());
        self.ty.extend(substitutions.ty.clone());
    }
}

#[derive(Clone, Debug, Default)]
pub struct InstantiationSubstitutions {
    pub row: FxHashMap<NodeID, IndexMap<RowParamId, RowMetaId>>,
    pub ty: FxHashMap<NodeID, IndexMap<TypeParamId, MetaVarId>>,
}

impl InstantiationSubstitutions {
    pub(super) fn ty_mappings(&self, id: &NodeID) -> IndexMap<TypeParamId, MetaVarId> {
        self.ty.get(id).cloned().unwrap_or_default()
    }

    pub(super) fn get_ty(
        &mut self,
        node_id: &NodeID,
        type_param_id: &TypeParamId,
    ) -> Option<&MetaVarId> {
        self.ty.entry(*node_id).or_default().get(type_param_id)
    }

    pub(super) fn get_row(
        &mut self,
        node_id: &NodeID,
        type_param_id: &RowParamId,
    ) -> Option<&RowMetaId> {
        self.row.entry(*node_id).or_default().get(type_param_id)
    }

    pub(super) fn insert_ty(
        &mut self,
        node_id: NodeID,
        type_param_id: TypeParamId,
        meta: MetaVarId,
    ) {
        self.ty
            .entry(node_id)
            .or_default()
            .insert(type_param_id, meta);
    }

    pub(super) fn insert_row(
        &mut self,
        node_id: NodeID,
        row_param_id: RowParamId,
        meta: RowMetaId,
    ) {
        self.row
            .entry(node_id)
            .or_default()
            .insert(row_param_id, meta);
    }
}

impl std::fmt::Debug for UnificationSubstitutions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Subs(ty: {:?}, row: {:?}", self.ty, self.row,)
    }
}

impl UnificationSubstitutions {
    pub fn new(meta_levels: Rc<RefCell<FxHashMap<Meta, Level>>>) -> Self {
        Self {
            row: Default::default(),
            ty: Default::default(),
            meta_levels,
        }
    }
}

fn occurs_in_row(id: MetaVarId, row: &InferRow) -> bool {
    match row {
        InferRow::Empty(..) => false,
        InferRow::Var(_) => false,
        InferRow::Param(_) => false,
        InferRow::Extend { row, ty, .. } => occurs_in(id, ty) || occurs_in_row(id, row),
    }
}

// Helper: occurs check
fn occurs_in(id: MetaVarId, ty: &InferTy) -> bool {
    match ty {
        InferTy::Error(..) => false,
        InferTy::Var { id: mid, .. } => *mid == id,
        InferTy::Func(a, b) => occurs_in(id, a) || occurs_in(id, b),
        InferTy::Tuple(items) => items.iter().any(|t| occurs_in(id, t)),
        InferTy::Record(row) => occurs_in_row(id, row),
        InferTy::Nominal { row, .. } => occurs_in_row(id, row),
        InferTy::Projection { base, .. } => occurs_in(id, base),
        InferTy::Param(..) => false,
        InferTy::Rigid(..) => false,
        InferTy::Primitive(..) => false,
        InferTy::Constructor { params, ret, .. } => {
            params.iter().any(|t| occurs_in(id, t)) || occurs_in(id, ret)
        }
    }
}

// Structural occurs check for row variables (doesn't follow substitutions to avoid infinite loops)
fn row_occurs_structural(
    target: RowMetaId,
    row: &InferRow,
    subs: &mut UnificationSubstitutions,
) -> bool {
    match row {
        InferRow::Empty(..) | InferRow::Param(_) => false,
        InferRow::Var(id) => *id == target,
        InferRow::Extend { row, ty, .. } => {
            row_occurs_structural(target, row, subs) || ty_occurs_structural_row(target, ty, subs)
        }
    }
}

fn ty_occurs_structural_row(
    target: RowMetaId,
    ty: &InferTy,
    subs: &mut UnificationSubstitutions,
) -> bool {
    match ty {
        InferTy::Record(row) | InferTy::Nominal { row, .. } => {
            row_occurs_structural(target, row, subs)
        }
        InferTy::Func(a, b) => {
            ty_occurs_structural_row(target, a, subs) || ty_occurs_structural_row(target, b, subs)
        }
        InferTy::Tuple(items) => items
            .iter()
            .any(|t| ty_occurs_structural_row(target, t, subs)),
        InferTy::Constructor { params, ret, .. } => {
            params
                .iter()
                .any(|p| ty_occurs_structural_row(target, p, subs))
                || ty_occurs_structural_row(target, ret, subs)
        }
        _ => false,
    }
}

fn row_occurs(
    target: RowMetaId,
    row: &InferRow,
    subs: &mut UnificationSubstitutions,
    session: &mut TypeSession,
) -> bool {
    match session.apply_row(row.clone(), subs) {
        InferRow::Empty(..) | InferRow::Param(_) => false,
        InferRow::Var(id) => id == target,
        InferRow::Extend { row, ty, .. } => {
            row_occurs(target, &row, subs, session)
                || matches!(session.apply(ty.clone(), subs), InferTy::Record(r) if row_occurs(target, &r, subs, session))
        }
    }
}

// Unify rows. Returns true if progress was made.
#[instrument(level = tracing::Level::TRACE, skip(context, session))]
fn unify_rows(
    kind: TypeDefKind,
    lhs: &InferRow,
    rhs: &InferRow,
    context: &mut impl Solve,
    session: &mut TypeSession,
) -> Result<Vec<Meta>, TypeError> {
    let mut result = vec![];
    let (mut lhs_fields, lhs_tail) =
        normalize_row(lhs.clone(), context.substitutions_mut(), session);
    let (mut rhs_fields, rhs_tail) =
        normalize_row(rhs.clone(), context.substitutions_mut(), session);

    // Check to see if one side is closed and the other is a var. If so,
    // just unify the var as the other side
    if let (closed, RowTail::Empty, _, RowTail::Var(var))
    | (_, RowTail::Var(var), closed, RowTail::Empty) =
        (&lhs_fields, &lhs_tail, &rhs_fields, &rhs_tail)
    {
        tracing::debug!("unifying closed row with row var");
        let mut acc = InferRow::Empty(kind);
        for (label, ty) in closed.iter().rev() {
            acc = InferRow::Extend {
                row: Box::new(acc),
                label: label.clone(),
                ty: ty.clone(),
            };
        }

        if row_occurs_structural(*var, &acc, context.substitutions_mut()) {
            return Err(TypeError::OccursCheck(InferTy::Record(Box::new(acc))));
        }
        context.substitutions_mut().row.insert(*var, acc);
        result.push(Meta::Row(*var));

        return Ok(result);
    }

    // unify common labels
    for k in lhs_fields.keys().cloned().collect::<Vec<_>>() {
        if let Some(rv) = rhs_fields.remove(&k) {
            let Some(lv) = lhs_fields.remove(&k) else {
                continue;
            };
            result.extend(unify(&lv, &rv, context, session)?);
        }
    }

    // helper: extend a Var tail with leftover fields (prepend over a fresh tail)
    let mut extend_var_tail =
        |tail_id: RowMetaId, fields: BTreeMap<Label, InferTy>| -> Result<Vec<Meta>, TypeError> {
            let mut result = vec![];
            if fields.is_empty() {
                return Ok(result);
            }
            let mut acc = session.new_row_meta_var(context.level());
            for (label, ty) in fields.into_iter().rev() {
                acc = InferRow::Extend {
                    row: Box::new(acc),
                    label,
                    ty,
                };
            }
            if row_occurs(tail_id, &acc, context.substitutions_mut(), session) {
                return Err(TypeError::OccursCheck(InferTy::Record(Box::new(acc))));
            }

            let can = session.canon_row(tail_id);
            context.substitutions_mut().row.insert(can, acc);
            result.push(Meta::Row(can));
            Ok(result)
        };

    // LHS leftovers must be absorbed by RHS tail
    if !lhs_fields.is_empty() {
        match rhs_tail {
            RowTail::Var(id) => {
                result.extend(extend_var_tail(id, lhs_fields)?);
            }
            RowTail::Empty => {
                return Err(TypeError::InvalidUnification(
                    InferTy::Record(Box::new(lhs.clone())).into(),
                    InferTy::Record(Box::new(rhs.clone())).into(),
                ));
            }
            RowTail::Param(_) => {
                return Err(TypeError::InvalidUnification(
                    InferTy::Record(Box::new(lhs.clone())).into(),
                    InferTy::Record(Box::new(rhs.clone())).into(),
                ));
            }
        }
    }

    // RHS leftovers must be absorbed by LHS tail
    if !rhs_fields.is_empty() {
        match lhs_tail {
            RowTail::Var(id) => {
                result.extend(extend_var_tail(id, rhs_fields)?);
            }
            RowTail::Empty => {
                return Err(TypeError::InvalidUnification(
                    InferTy::Record(Box::new(lhs.clone())).into(),
                    InferTy::Record(Box::new(rhs.clone())).into(),
                ));
            }
            RowTail::Param(_) => {
                return Err(TypeError::InvalidUnification(
                    InferTy::Record(Box::new(lhs.clone())).into(),
                    InferTy::Record(Box::new(rhs.clone())).into(),
                ));
            }
        }
    }

    // unify tails when both are metas/params (cheap)
    match (lhs_tail, rhs_tail) {
        (RowTail::Var(a), RowTail::Var(b)) if session.canon_row(a) != session.canon_row(b) => {
            let can_a = session.canon_row(a);
            let can_b = session.canon_row(b);
            session.link_row(can_a, can_b);
            result.push(Meta::Row(can_a));
            result.push(Meta::Row(can_b));
        }
        (RowTail::Param(a), RowTail::Param(b)) if a == b => {}
        (RowTail::Param(_), RowTail::Param(_)) => {
            return Err(TypeError::InvalidUnification(
                InferTy::Record(Box::new(lhs.clone())).into(),
                InferTy::Record(Box::new(rhs.clone())).into(),
            ));
        }
        _ => {}
    }

    Ok(result)
}

// Unify types. Returns true if progress was made.
pub(super) fn unify(
    lhs: &InferTy,
    rhs: &InferTy,
    context: &mut impl Solve,
    session: &mut TypeSession,
) -> Result<Vec<Meta>, TypeError> {
    let lhs = context.normalize(lhs.clone(), session);
    let rhs = context.normalize(rhs.clone(), session);
    let lhs = session.apply(lhs, context.substitutions_mut());
    let rhs = session.apply(rhs, context.substitutions_mut());

    if lhs == rhs {
        return Ok(Default::default());
    }

    let _s =
        tracing::trace_span!("unify", lhs = format!("{lhs:?}"), rhs = format!("{rhs:?}")).entered();

    let mut result = vec![];

    match (&lhs, &rhs) {
        (InferTy::Primitive(lhs), InferTy::Primitive(rhs)) => {
            if lhs == rhs {
                Ok(Default::default())
            } else {
                Err(TypeError::InvalidUnification(
                    InferTy::Primitive(*lhs).into(),
                    InferTy::Primitive(*rhs).into(),
                ))
            }
        }
        (InferTy::Tuple(lhs), InferTy::Tuple(rhs)) => {
            for (lhs, rhs) in lhs.iter().zip(rhs) {
                result.extend(unify(lhs, rhs, context, session)?);
            }
            Ok(result)
        }
        (InferTy::Rigid(lhs), InferTy::Rigid(rhs)) if lhs == rhs => Ok(Default::default()),
        (InferTy::Param(lhs), InferTy::Param(rhs)) if lhs == rhs => Ok(Default::default()),
        (
            InferTy::Constructor {
                params, box ret, ..
            },
            InferTy::Func(func_param, func_ret),
        )
        | (
            InferTy::Func(func_param, func_ret),
            InferTy::Constructor {
                params, box ret, ..
            },
        ) => unify(
            &curry(params.clone(), ret.clone()),
            &InferTy::Func(func_param.clone(), func_ret.clone()),
            context,
            session,
        ),
        (
            InferTy::Nominal {
                symbol: lhs_id,
                row: box lhs_row,
            },
            InferTy::Nominal {
                symbol: rhs_id,
                row: box rhs_row,
            },
        ) => {
            if lhs_id != rhs_id {
                return Err(TypeError::InvalidUnification(lhs.into(), rhs.into()));
            }

            let kind = match lhs_id {
                Symbol::Struct(..) => TypeDefKind::Struct,
                Symbol::Enum(..) => TypeDefKind::Enum,
                _ => TypeDefKind::Struct,
            };

            let changed = unify_rows(kind, lhs_row, rhs_row, context, session)?;
            Ok(changed)
        }
        // (Ty::TypeConstructor(lhs), Ty::TypeConstructor(rhs)) if lhs == rhs => Ok(false),
        (InferTy::Func(lhs_param, lhs_ret), InferTy::Func(rhs_param, rhs_ret)) => {
            result.extend(unify(lhs_param, rhs_param, context, session)?);
            result.extend(unify(lhs_ret, rhs_ret, context, session)?);
            Ok(result)
        }
        (
            InferTy::Var {
                id: lhs_id,
                level: _,
            },
            InferTy::Var {
                id: rhs_id,
                level: _,
            },
        ) => {
            let ra = session.canon_meta(*lhs_id);
            let rb = session.canon_meta(*rhs_id);
            if ra != rb {
                session.link_meta(ra, rb);

                tracing::info!("unifying vars {ra:?} and {rb:?}");

                // Return both metas so constraints waiting on either can be woken
                result.push(Meta::Ty(ra));
                result.push(Meta::Ty(rb));

                Ok(result)
            } else {
                Ok(Default::default())
            }
        }
        (ty, InferTy::Var { id, .. }) | (InferTy::Var { id, .. }, ty) => {
            if occurs_in(*id, ty) {
                return Err(TypeError::OccursCheck(ty.clone()));
            }

            let id = session.canon_meta(*id);

            context.substitutions_mut().ty.insert(id, ty.clone());

            result.push(Meta::Ty(id));
            Ok(result)
        }
        (InferTy::Record(lhs_row), InferTy::Record(rhs_row)) => {
            unify_rows(TypeDefKind::Struct, lhs_row, rhs_row, context, session)
        }
        // Handle Projection vs concrete type                                                                         13:48:55 [35/2876]
        (
            InferTy::Projection {
                base: box base_ty,
                associated,
                protocol_id,
            },
            other,
        )
        | (
            other,
            InferTy::Projection {
                base: box base_ty,
                associated,
                protocol_id,
            },
        ) => {
            let projection = InferTy::Projection {
                base: Box::new(base_ty.clone()),
                associated: associated.clone(),
                protocol_id: *protocol_id,
            };
            let normalized = context.normalize(projection.clone(), session);

            // If normalization resolved it (not still a Projection), unify recursively
            if !matches!(&normalized, InferTy::Projection { .. }) {
                unify(&normalized, other, context, session)
            } else {
                // Base is still unknown - error (the constraint solver will defer)
                Err(TypeError::InvalidUnification(
                    projection.into(),
                    other.clone().into(),
                ))
            }
        }

        (_, InferTy::Rigid(_)) | (InferTy::Rigid(_), _) => {
            Err(TypeError::InvalidUnification(lhs.into(), rhs.into()))
        }
        _ => {
            tracing::error!(
                "attempted to unify {:?} <> {:?}",
                session.apply(lhs.clone(), context.substitutions_mut(),),
                session.apply(rhs.clone(), context.substitutions_mut(),)
            );
            Err(TypeError::InvalidUnification(lhs.into(), rhs.into()))
        }
    }
}

pub fn curry<I: IntoIterator<Item = InferTy>>(params: I, ret: InferTy) -> InferTy {
    params
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rfold(ret, |acc, p| InferTy::Func(Box::new(p), Box::new(acc)))
}

pub(super) fn substitute_row(
    row: InferRow,
    substitutions: &FxHashMap<InferTy, InferTy>,
) -> InferRow {
    match row {
        InferRow::Empty(..) => row,
        InferRow::Var(..) => row,
        InferRow::Param(..) => row,
        InferRow::Extend { row, label, ty } => InferRow::Extend {
            row: Box::new(substitute_row(*row, substitutions)),
            label,
            ty: substitute(ty, substitutions),
        },
    }
}

pub(super) fn substitute_mult(
    ty: &[InferTy],
    substitutions: &FxHashMap<InferTy, InferTy>,
) -> Vec<InferTy> {
    ty.iter()
        .map(|t| substitute(t.clone(), substitutions))
        .collect()
}

pub(super) fn substitute(ty: InferTy, substitutions: &FxHashMap<InferTy, InferTy>) -> InferTy {
    if let Some(subst) = substitutions.get(&ty) {
        return subst.clone();
    }
    match ty {
        InferTy::Error(..) => ty,
        InferTy::Param(..) => ty,
        InferTy::Rigid(..) => ty,
        InferTy::Var { .. } => ty,
        InferTy::Primitive(..) => ty,
        InferTy::Projection {
            box base,
            associated,
            protocol_id,
        } => InferTy::Projection {
            base: substitute(base, substitutions).into(),
            associated,
            protocol_id,
        },
        InferTy::Constructor { name, params, ret } => InferTy::Constructor {
            name,
            params: params
                .into_iter()
                .map(|p| substitute(p, substitutions))
                .collect(),
            ret: Box::new(substitute(*ret, substitutions)),
        },
        InferTy::Func(params, ret) => InferTy::Func(
            Box::new(substitute(*params, substitutions)),
            Box::new(substitute(*ret, substitutions)),
        ),
        InferTy::Tuple(items) => InferTy::Tuple(
            items
                .into_iter()
                .map(|t| substitute(t, substitutions))
                .collect(),
        ),
        InferTy::Record(row) => InferTy::Record(Box::new(substitute_row(*row, substitutions))),
        InferTy::Nominal { symbol, box row } => InferTy::Nominal {
            symbol,
            row: Box::new(substitute_row(row, substitutions)),
        },
    }
}

pub(super) fn instantiate_row(
    node_id: NodeID,
    row: InferRow,
    substitutions: &InstantiationSubstitutions,
    level: Level,
) -> InferRow {
    match row {
        InferRow::Empty(..) => row,
        InferRow::Var(..) => row,
        InferRow::Param(id) => {
            if let Some(row_metas) = substitutions.row.get(&node_id)
                && let Some(row_meta) = row_metas.get(&id)
            {
                InferRow::Var(*row_meta)
            } else {
                row
            }
        }
        InferRow::Extend { row, label, ty } => InferRow::Extend {
            row: Box::new(instantiate_row(node_id, *row, substitutions, level)),
            label,
            ty: instantiate_ty(node_id, ty, substitutions, level),
        },
    }
}

pub(super) fn instantiate_ty(
    node_id: NodeID,
    ty: InferTy,
    substitutions: &InstantiationSubstitutions,
    level: Level,
) -> InferTy {
    if substitutions.row.is_empty() && substitutions.ty.is_empty() {
        return ty;
    }

    match ty {
        InferTy::Error(..) => ty,
        InferTy::Param(param) => {
            if let Some(metas) = substitutions.ty.get(&node_id)
                && let Some(meta) = metas.get(&param)
            {
                InferTy::Var { id: *meta, level }
            } else {
                ty
            }
        }
        InferTy::Rigid(..) => ty,
        InferTy::Var { .. } => ty,
        InferTy::Primitive(..) => ty,
        InferTy::Projection {
            box base,
            associated,
            protocol_id,
        } => InferTy::Projection {
            base: instantiate_ty(node_id, base, substitutions, level).into(),
            associated,
            protocol_id,
        },
        InferTy::Constructor { name, params, ret } => InferTy::Constructor {
            name,
            params: params
                .into_iter()
                .map(|p| instantiate_ty(node_id, p, substitutions, level))
                .collect(),
            ret: Box::new(instantiate_ty(node_id, *ret, substitutions, level)),
        },
        InferTy::Func(params, ret) => InferTy::Func(
            Box::new(instantiate_ty(node_id, *params, substitutions, level)),
            Box::new(instantiate_ty(node_id, *ret, substitutions, level)),
        ),
        InferTy::Tuple(items) => InferTy::Tuple(
            items
                .into_iter()
                .map(|t| instantiate_ty(node_id, t, substitutions, level))
                .collect(),
        ),
        InferTy::Record(row) => InferTy::Record(Box::new(instantiate_row(
            node_id,
            *row,
            substitutions,
            level,
        ))),
        InferTy::Nominal { symbol, box row } => InferTy::Nominal {
            symbol,
            row: Box::new(instantiate_row(node_id, row, substitutions, level)),
        },
    }
}
