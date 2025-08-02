use std::collections::{BTreeMap, HashMap};

use tracing::Level;

use crate::{
    ty::Ty,
    type_checker::TypeError,
    type_var_context::{TypeVarContext, UnificationEntry},
    type_var_id::{TypeVarID, TypeVarKind},
};

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

    pub fn merge_type_vars(
        &mut self,
        lhs: TypeVarID,
        rhs: TypeVarID,
        context: &mut TypeVarContext,
        generation: u32,
    ) {
        context.unify(lhs, rhs, generation);
    }

    pub fn apply(&mut self, ty: &Ty, depth: u32, context: &mut TypeVarContext) -> Ty {
        if depth > 20 {
            tracing::warn!("Hit 20 recursive applications for {ty:#?}, bailing.");
            return ty.clone();
        }

        // tracing::trace!("Applying:\n{:#?}\n---\n{:?}", ty);

        match ty {
            Ty::Primitive(_) => ty.clone(),
            Ty::SelfType => ty.clone(),
            Ty::Func(params, returning, generics) => {
                let applied_params = self.apply_multiple(params, depth + 1, context);
                let applied_return = self.apply(returning, depth + 1, context);
                let applied_generics = self.apply_multiple(generics, depth + 1, context);

                Ty::Func(applied_params, Box::new(applied_return), applied_generics)
            }
            Ty::TypeVar(type_var) => {
                let type_var = self.normalize(type_var, context);

                if let Some(ty) = self.get(&type_var).cloned() {
                    self.apply(&ty, depth + 1, context)
                // } else if let TypeVarID {
                //     kind: TypeVarKind::Instantiated(i),
                //     ..
                // } = type_var
                // {
                //     let parent_type_var =
                //         TypeVarID::new(i, TypeVarKind::Canonicalized(type_var.id));
                //     self.apply(&Ty::TypeVar(parent_type_var), depth + 1, context)
                // } else if let TypeVarID {
                //     kind: TypeVarKind::Canonicalized(i),
                //     ..
                // } = type_var
                // {
                //     Ty::TypeVar(TypeVarID::new(i, TypeVarKind::Instantiated(type_var.id)))
                } else {
                    Ty::TypeVar(type_var)
                }
            }
            Ty::Tuple(types) => Ty::Tuple(
                types
                    .iter()
                    .map(|variant| self.apply(variant, depth + 1, context))
                    .collect(),
            ),
            Ty::Closure { func, captures } => {
                let func = self.apply(func, depth + 1, context).into();
                Ty::Closure {
                    func,
                    captures: captures.clone(),
                }
            }
            Ty::Array(ty) => Ty::Array(self.apply(ty, depth + 1, context).into()),
            Ty::Init(struct_id, params) => {
                Ty::Init(*struct_id, self.apply_multiple(params, depth + 1, context))
            }
            Ty::Method { self_ty, func } => Ty::Method {
                self_ty: self.apply(self_ty, depth + 1, context).into(),
                func: self.apply(func, depth + 1, context).into(),
            },
            Ty::Row {
                type_var,
                constraints,
                generics,
                kind,
            } => {
                // TODO: Apply substitutions to types within constraints
                let applied_constraints = constraints.clone(); // For now, just clone
                let applied_generics = self.apply_multiple(generics, depth + 1, context);
                Ty::Row {
                    type_var: type_var.clone(),
                    constraints: applied_constraints,
                    generics: applied_generics,
                    kind: kind.clone(),
                }
            }
        }
    }

    pub fn apply_multiple(
        &mut self,
        types: &[Ty],
        depth: u32,
        context: &mut TypeVarContext,
    ) -> Vec<Ty> {
        types
            .iter()
            .map(|ty| self.apply(ty, depth, context))
            .collect()
    }

    fn normalize(&self, type_var: &TypeVarID, context: &mut TypeVarContext) -> TypeVarID {
        context.find(type_var)
    }

    pub fn unifiable(&mut self, lhs: &Ty, rhs: &Ty, context: &mut TypeVarContext) -> bool {
        let lhs = self.apply(lhs, 0, context);
        let rhs = self.apply(rhs, 0, context);

        match (&lhs, &rhs) {
            (Ty::TypeVar(_), _) | (_, Ty::TypeVar(_)) => true,
            _ => lhs == rhs,
        }
    }

    #[tracing::instrument(level = Level::TRACE, skip(self, context), fields(result))]
    pub fn unify(
        &mut self,
        lhs: &Ty,
        rhs: &Ty,
        context: &mut TypeVarContext,
        generation: u32,
    ) -> Result<(), TypeError> {
        let lhs = self.apply(lhs, 0, context);
        let rhs = self.apply(rhs, 0, context);

        if lhs == rhs {
            return Ok(());
        }

        tracing::trace!("lhs = {lhs:?}, rhs = {rhs:?}");

        //tracing::trace!(
        //    "{:?} <> {:?} = {:?} <> {:?}",
        //    lhs,
        //    rhs,
        //    self.apply(&lhs, 0, context),
        //    self.apply(&rhs, 0, context)
        //);

        match (lhs.clone(), rhs.clone()) {
            // They're the same, sick.
            (a, b) if a == b => Ok(()),

            (Ty::TypeVar(v1), Ty::TypeVar(v2)) => {
                self.merge_type_vars(v1, v2, context, generation);

                Ok(())
            }

            (Ty::TypeVar(v), ty) | (ty, Ty::TypeVar(v)) => {
                let v = self.normalize(&v, context);

                // Canonical type parameters (quantified variables) must not be unified with
                // concrete types. They should be instantiated instead at the use-site.
                if matches!(v.kind, TypeVarKind::CanonicalTypeParameter(_)) {
                    // If both sides are *the same* canonical parameter, consider it trivially unified.
                    if let Ty::TypeVar(other_v) = &ty {
                        let other_v = self.normalize(other_v, context);
                        if v == other_v {
                            return Ok(());
                        }
                    }

                    // Otherwise, we cannot unify a canonical parameter with a concrete type – that
                    // would violate its universally quantified nature.
                    return Err(TypeError::Mismatch(
                        self.apply(&lhs, 0, context).to_string(),
                        self.apply(&rhs, 0, context).to_string(),
                    ));
                }

                if self.occurs_check(&v, &ty, context) {
                    Err(TypeError::OccursConflict)
                } else {
                    context.history.push(UnificationEntry::Unify {
                        expr_id: v.expr_id,
                        before: Ty::TypeVar(v.clone()),
                        after: ty.clone(),
                        generation,
                    });
                    self.insert(v.clone(), ty.clone());
                    Ok(())
                }
            }
            (
                Ty::Func(lhs_params, lhs_returning, lhs_gen),
                Ty::Func(rhs_params, rhs_returning, rhs_gen),
            ) if lhs_params.len() == rhs_params.len() => {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    self.unify(lhs, &rhs, context, generation)?;
                }

                for (lhs, rhs) in lhs_gen.iter().zip(rhs_gen) {
                    self.unify(lhs, &rhs, context, generation)?;
                }

                self.unify(&lhs_returning, &rhs_returning, context, generation)?;

                Ok(())
            }
            (Ty::Closure { func: lhs_func, .. }, Ty::Closure { func: rhs_func, .. }) => {
                self.unify(&lhs_func, &rhs_func, context, generation)?;

                Ok(())
            }
            (
                Ty::Method {
                    func: lhs_func,
                    self_ty: lhs_self_ty,
                },
                Ty::Method {
                    func: rhs_func,
                    self_ty: rhs_self_ty,
                },
            ) => {
                // When unifying methods, we only need to unify the function types.
                // The self_ty can be different when dealing with protocol methods
                // on different concrete types that both conform to the protocol.
                self.unify(&lhs_func, &rhs_func, context, generation)?;

                // Only unify self_ty if at least one is a TypeVar (for inference)
                // or if they're the same type (for exact matches)
                match (lhs_self_ty.as_ref(), rhs_self_ty.as_ref()) {
                    (Ty::TypeVar(_), _) | (_, Ty::TypeVar(_)) => {
                        self.unify(&lhs_self_ty, &rhs_self_ty, context, generation)?;
                    }
                    (lhs, rhs) if lhs == rhs => {
                        // Already the same, no need to unify
                    }
                    _ => {
                        // Different concrete types - that's OK for protocol methods
                        // as long as the function signatures match
                    }
                }

                Ok(())
            }
            (func @ Ty::Func { .. }, Ty::Method { func: method, .. })
            | (Ty::Method { func: method, .. }, func @ Ty::Func { .. }) => {
                self.unify(&func, &method, context, generation)?;

                Ok(())
            }
            (func, Ty::Closure { func: closure, .. })
            | (Ty::Closure { func: closure, .. }, func)
                if matches!(func, Ty::Func(_, _, _)) =>
            {
                self.unify(&func, &closure, context, generation)?;

                Ok(())
            }
            // Handle Row types - check nominal_id and unify generics
            (
                Ty::Row {
                    kind: kind1,
                    generics: gen1,
                    ..
                },
                Ty::Row {
                    kind: kind2,
                    generics: gen2,
                    ..
                },
            ) if kind1 == kind2 => {
                // Unify generics
                if gen1.len() != gen2.len() {
                    return Err(TypeError::Mismatch(
                        format!("{} generics", gen1.len()),
                        format!("{} generics", gen2.len()),
                    ));
                }
                for (g1, g2) in gen1.iter().zip(gen2) {
                    self.unify(g1, &g2, context, generation)?;
                }
                Ok(())
            }
            // Handle records
            (
                Ty::Row {
                    generics: lhs_generics,
                    ..
                },
                Ty::Row {
                    generics: rhs_generics,
                    ..
                },
            ) if lhs_generics.len() == rhs_generics.len() =>
            {
                for (g1, g2) in lhs_generics.iter().zip(rhs_generics) {
                    self.unify(g1, &g2, context, generation)?;
                }

                // Get fields from constraints
                let lhs_fields_info = lhs.get_row_fields();
                let rhs_fields_info = rhs.get_row_fields();
                
                // Convert to BTreeMap<String, Ty> for comparison
                let lhs_fields: BTreeMap<String, Ty> = lhs_fields_info.iter()
                    .map(|(k, v)| (k.clone(), v.ty.clone()))
                    .collect();
                let rhs_fields: BTreeMap<String, Ty> = rhs_fields_info.iter()
                    .map(|(k, v)| (k.clone(), v.ty.clone()))
                    .collect();

                for (label, ty) in lhs_fields.iter() {
                    let Some(rhs_ty) = rhs_fields.get(label) else {
                        return Err(TypeError::Mismatch(
                            self.apply(&lhs, 0, context).to_string(),
                            self.apply(&rhs, 0, context).to_string(),
                        ));
                    };

                    self.unify(ty, rhs_ty, context, generation)?;
                }
                Ok(())
            }
            _ => Err(TypeError::Mismatch(
                self.apply(&lhs, 0, context).to_string(),
                self.apply(&rhs, 0, context).to_string(),
            )),
        }
    }

    /// Returns true if `v` occurs inside `ty`
    fn occurs_check(&mut self, v: &TypeVarID, ty: &Ty, context: &mut TypeVarContext) -> bool {
        let ty = self.apply(ty, 0, context);
        match &ty {
            Ty::TypeVar(tv) => tv == v,
            Ty::Func(params, returning, generics)
            | Ty::Closure {
                func: box Ty::Func(params, returning, generics),
                ..
            } => {
                // check each parameter and the return type
                let oh = params
                    .iter()
                    .any(|param| self.occurs_check(v, param, context))
                    || self.occurs_check(v, returning, context)
                    || generics
                        .iter()
                        .any(|generic| self.occurs_check(v, generic, context));
                if oh {
                    tracing::error!("occur check failed: {ty:?}");
                }

                oh
            }
            _ => false,
        }
    }
}

impl FromIterator<(TypeVarID, Ty)> for Substitutions {
    fn from_iter<T: IntoIterator<Item = (TypeVarID, Ty)>>(iter: T) -> Self {
        Substitutions {
            storage: HashMap::from_iter(iter),
        }
    }
}
