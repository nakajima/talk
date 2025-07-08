use std::collections::HashMap;

use tracing::Level;

use crate::{
    constraint_solver::ConstraintSolver,
    ty::Ty,
    type_checker::TypeError,
    type_var_context::TypeVarContext,
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
    ) {
        context.unify(lhs, rhs);
    }

    pub fn apply(&mut self, ty: &Ty, depth: u32, context: &mut TypeVarContext) -> Ty {
        if depth > 20 {
            tracing::error!("Hit 100 recursive applications for {ty:#?}, bailing.");
            return ty.clone();
        }

        // tracing::trace!("Applying:\n{:#?}\n---\n{:?}", ty);

        match ty {
            Ty::Pointer => ty.clone(),
            Ty::Int => ty.clone(),
            Ty::Byte => ty.clone(),
            Ty::Float => ty.clone(),
            Ty::Bool => ty.clone(),
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
            Ty::Enum(name, generics) => {
                let applied_generics = self.apply_multiple(generics, depth + 1, context);

                Ty::Enum(*name, applied_generics)
            }
            Ty::EnumVariant(enum_id, values) => {
                let applied_values = values
                    .iter()
                    .map(|variant| self.apply(variant, depth + 1, context))
                    .collect();
                Ty::EnumVariant(*enum_id, applied_values)
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
            Ty::Struct(sym, generics) => {
                Ty::Struct(*sym, self.apply_multiple(generics, depth + 1, context))
            }
            Ty::Protocol(sym, generics) => {
                Ty::Protocol(*sym, self.apply_multiple(generics, depth + 1, context))
            }
            Ty::Init(struct_id, params) => {
                Ty::Init(*struct_id, self.apply_multiple(params, depth + 1, context))
            }
            Ty::Void => ty.clone(),
        }
    }

    fn apply_multiple(
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
    ) -> Result<(), TypeError> {
        let lhs = self.apply(lhs, 0, context);
        let rhs = self.apply(rhs, 0, context);

        if lhs == rhs {
            return Ok(());
        }

        tracing::trace!("lhs = {lhs:?}, rhs = {rhs:?}");

        let res = match (lhs.clone(), rhs.clone()) {
            // They're the same, sick.
            (a, b) if a == b => Ok(()),

            (Ty::TypeVar(v1), Ty::TypeVar(v2)) => {
                self.merge_type_vars(v1, v2, context);

                Ok(())
            }

            (Ty::TypeVar(v), ty) | (ty, Ty::TypeVar(v)) => {
                let v = self.normalize(&v, context);

                if let TypeVarKind::CanonicalTypeParameter(_) = &v.kind {
                    tracing::warn!(
                        "Attempting to unify canonical type parameter {v:?} with {ty:?}. Consider instantiating."
                    );
                }

                if self.occurs_check(&v, &ty, context) {
                    Err(TypeError::OccursConflict)
                } else {
                    self.insert(v.clone(), ty.clone());
                    Ok(())
                }
            }
            (
                Ty::Func(lhs_params, lhs_returning, lhs_gen),
                Ty::Func(rhs_params, rhs_returning, rhs_gen),
            ) if lhs_params.len() == rhs_params.len() => {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    self.unify(lhs, &rhs, context)?;
                }

                for (lhs, rhs) in lhs_gen.iter().zip(rhs_gen) {
                    self.unify(lhs, &rhs, context)?;
                }

                self.unify(&lhs_returning, &rhs_returning, context)?;

                Ok(())
            }
            (Ty::Closure { func: lhs_func, .. }, Ty::Closure { func: rhs_func, .. }) => {
                self.unify(&lhs_func, &rhs_func, context)?;

                Ok(())
            }
            (func, Ty::Closure { func: closure, .. })
            | (Ty::Closure { func: closure, .. }, func)
                if matches!(func, Ty::Func(_, _, _)) =>
            {
                self.unify(&func, &closure, context)?;

                Ok(())
            }
            (Ty::Enum(_, lhs_types), Ty::Enum(_, rhs_types))
                if lhs_types.len() == rhs_types.len() =>
            {
                for (lhs, rhs) in lhs_types.iter().zip(rhs_types) {
                    self.unify(lhs, &rhs, context)?;
                }

                Ok(())
            }
            (Ty::Enum(_, enum_types), Ty::EnumVariant(_, variant_types))
            | (Ty::EnumVariant(_, variant_types), Ty::Enum(_, enum_types)) => {
                for (e_ty, v_ty) in enum_types.iter().zip(variant_types) {
                    self.unify(e_ty, &v_ty, context)?;
                }

                Ok(())
            }
            (Ty::Struct(_, lhs), Ty::Struct(_, rhs)) if lhs.len() == rhs.len() => {
                for (lhs, rhs) in lhs.iter().zip(rhs) {
                    self.unify(lhs, &rhs, context)?;
                }

                Ok(())
            }
            (Ty::Func(func_args, ret, generics), Ty::EnumVariant(enum_id, variant_args))
            | (Ty::EnumVariant(enum_id, variant_args), Ty::Func(func_args, ret, generics))
                if func_args.len() == variant_args.len() =>
            {
                let mut member_substitutions = self.clone();
                for (type_param, type_arg) in variant_args.iter().zip(generics) {
                    tracing::trace!("Member substitution: {type_param:?} -> {type_arg:?}");
                    if let Ty::TypeVar(type_var) = type_param {
                        member_substitutions.insert(type_var.clone(), type_arg.clone());
                    }
                }
                let specialized_ty = ConstraintSolver::substitute_ty_with_map(
                    &Ty::EnumVariant(enum_id, func_args),
                    self,
                );

                self.unify(&ret, &specialized_ty, context)?;

                Ok(())
            }
            _ => Err(TypeError::Mismatch(
                self.apply(&lhs, 0, context).to_string(),
                self.apply(&rhs, 0, context).to_string(),
            )),
        };

        tracing::debug!(
            "∪ {:?} <> {:?} = {:?} <> {:?}",
            lhs,
            rhs,
            self.apply(&lhs, 0, context),
            self.apply(&rhs, 0, context)
        );

        res
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
            Ty::Enum(_name, generics) => generics
                .iter()
                .any(|generic| self.occurs_check(v, generic, context)),
            Ty::EnumVariant(_enum_id, values) => values
                .iter()
                .any(|value| self.occurs_check(v, value, context)),
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
