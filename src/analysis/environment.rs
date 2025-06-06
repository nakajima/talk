use std::{
    collections::{HashMap, HashSet},
    ops::IndexMut,
};

use crate::{
    SymbolID, SymbolTable,
    parser::ExprID,
    prelude::{PRELUDE, Prelude},
    type_checker::Ty,
};

use super::{
    constraint_solver::Constraint,
    type_checker::{Scheme, TypeVarID, TypeVarKind},
    typed_expr::TypedExpr,
};

pub type Scope = HashMap<SymbolID, Scheme>;

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: String,
    pub values: Vec<Ty>,
    pub constructor_symbol: SymbolID,
}

#[derive(Debug, Clone)]
pub struct EnumDef {
    pub name: Option<SymbolID>,
    pub type_parameters: TypeParams,
    pub variants: Vec<EnumVariant>,
    pub methods: Vec<Ty>,
}

pub type TypeParams = Vec<Ty>;

#[derive(Debug, Clone)]
pub enum TypeDef {
    Enum(EnumDef),
}

pub type TypedExprs = HashMap<ExprID, TypedExpr>;

#[derive(Debug, Clone)]
pub struct Environment {
    pub typed_exprs: TypedExprs,
    pub type_var_id: TypeVarID,
    pub constraints: Vec<Constraint>,
    pub scopes: Vec<Scope>,
    pub types: HashMap<SymbolID, TypeDef>,
    pub direct_callables: HashMap<ExprID, SymbolID>,
}

impl Default for Environment {
    fn default() -> Self {
        let mut env = Self::new();
        env.import_prelude(&PRELUDE);
        env
    }
}

impl Environment {
    pub fn new() -> Self {
        Self {
            typed_exprs: HashMap::new(),
            type_var_id: TypeVarID(0, TypeVarKind::Blank),
            constraints: vec![],
            scopes: vec![SymbolTable::default_env_scope()],
            types: Default::default(),
            direct_callables: Default::default(),
        }
    }

    pub fn import_prelude(&mut self, prelude: &Prelude) {
        // Import types
        self.types.extend(prelude.types.clone());

        self.typed_exprs.extend(prelude.typed_exprs.clone());

        // Import schemes into global scope
        log::debug!("Importing schemes: {:?}", prelude.schemes);
        self.scopes[0].extend(prelude.schemes.clone());
    }

    /// Look up the scheme for `sym`, then immediately instantiate it.
    pub fn instantiate_symbol(&mut self, symbol_id: SymbolID) -> Ty {
        let scheme = self
            .scopes
            .iter()
            .rev()
            .find_map(|frame| frame.get(&symbol_id).cloned())
            .unwrap_or_else(|| panic!("missing symbol {:?} in {:?}", symbol_id, self.scopes));

        self.instantiate(scheme)
    }

    pub fn declare(&mut self, symbol_id: SymbolID, scheme: Scheme) {
        self.scopes.last_mut().unwrap().insert(symbol_id, scheme);
    }

    pub fn declare_in_parent(&mut self, symbol_id: SymbolID, scheme: Scheme) {
        log::trace!(
            "Declaring {:?} {:?} in {:?}",
            symbol_id,
            scheme,
            self.scopes
        );
        self.scopes
            .index_mut(self.scopes.len() - 2)
            .insert(symbol_id, scheme);
    }

    pub fn start_scope(&mut self) {
        self.scopes.push(Default::default());
    }

    /// Take a monotype `t` and produce a Scheme ∀αᵢ. t,
    /// quantifying exactly those vars not free elsewhere in the env.
    pub fn generalize(&self, t: &Ty) -> Scheme {
        let ftv_t = free_type_vars(t);
        let ftv_env = free_type_vars_in_env(&self.scopes);
        let unbound_vars: Vec<TypeVarID> = ftv_t.difference(&ftv_env).cloned().collect();

        Scheme {
            unbound_vars,
            ty: t.clone(),
        }
    }

    /// Instantiate a polymorphic scheme into a fresh monotype:
    /// for each α ∈ scheme.vars, generate β = new_type_variable(α.kind),
    /// and substitute α ↦ β throughout scheme.ty.
    pub fn instantiate(&mut self, scheme: Scheme) -> Ty {
        // 1) build a map old_var → fresh_var
        let mut var_map: HashMap<TypeVarID, TypeVarID> = HashMap::new();
        for old in scheme.unbound_vars {
            // preserve the original kind when making a fresh one
            let fresh = self.new_type_variable(old.1.clone());
            var_map.insert(old, fresh);
        }
        // 2) walk the type, replacing each old with its fresh
        fn walk<'a>(ty: Ty, map: &HashMap<TypeVarID, TypeVarID>) -> Ty {
            match ty {
                Ty::TypeVar(tv) => {
                    if let Some(new_tv) = map.get(&tv).cloned() {
                        Ty::TypeVar(new_tv)
                    } else {
                        Ty::TypeVar(tv)
                    }
                }
                Ty::Func(params, ret) => {
                    let new_params = params.iter().map(|p| walk(p.clone(), map)).collect();
                    let new_ret = Box::new(walk(*ret, map));
                    Ty::Func(new_params, new_ret)
                }
                Ty::Enum(name, generics) => {
                    let new_generics = generics.iter().map(|g| walk(g.clone(), map)).collect();
                    Ty::Enum(name, new_generics)
                }
                Ty::EnumVariant(name, values) => {
                    let new_values = values.iter().map(|g| walk(g.clone(), map)).collect();
                    Ty::EnumVariant(name, new_values)
                }
                Ty::Tuple(types) => Ty::Tuple(types.iter().map(|p| walk(p.clone(), map)).collect()),
                Ty::Void | Ty::Int | Ty::Float | Ty::Bool => ty.clone(),
            }
        }

        walk(scheme.ty, &var_map)
    }

    pub fn end_scope(&mut self) {
        self.scopes.pop();
    }

    #[track_caller]
    pub fn new_type_variable(&mut self, kind: TypeVarKind) -> TypeVarID {
        self.type_var_id = TypeVarID(self.type_var_id.0 + 1, kind);

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::warn!(
                "new_type_variable {:?} from {}:{}",
                Ty::TypeVar(self.type_var_id.clone()),
                loc.file(),
                loc.line()
            );
        }

        self.type_var_id.clone()
    }

    // Helper methods for enum definitions
    pub fn register_enum(&mut self, def: EnumDef) {
        self.types
            .insert(def.clone().name.unwrap(), TypeDef::Enum(def));
    }

    pub fn lookup_enum(&self, name: &SymbolID) -> Option<&EnumDef> {
        if let Some(TypeDef::Enum(def)) = self.types.get(name) {
            Some(def)
        } else {
            None
        }
    }

    /// Applies a given substitution map to a type. Does not recurse on type variables already in the map.
    pub fn substitute_ty_with_map(&self, ty: Ty, substitutions: &HashMap<TypeVarID, Ty>) -> Ty {
        match ty {
            Ty::TypeVar(ref type_var_id) => {
                if let Some(substituted_ty) = substitutions.get(type_var_id) {
                    // Important: Clone the substituted type. If it's also a TypeVar that needs further substitution,
                    // the caller (or a broader substitution application like `apply_substitutions_to_ty`) must handle it.
                    // This function only applies one layer from the provided map.
                    substituted_ty.clone()
                } else {
                    ty // Not in this substitution map, return as is.
                }
            }
            Ty::Func(params, returning) => {
                let applied_params = params
                    .iter()
                    .map(|param| self.substitute_ty_with_map(param.clone(), substitutions))
                    .collect();
                let applied_return = self.substitute_ty_with_map(*returning, substitutions);
                Ty::Func(applied_params, Box::new(applied_return))
            }
            Ty::Enum(name, generics) => {
                let applied_generics = generics
                    .iter()
                    .map(|g| self.substitute_ty_with_map(g.clone(), substitutions))
                    .collect();
                Ty::Enum(name, applied_generics)
            }
            Ty::EnumVariant(enum_id, values) => {
                let applied_values = values
                    .iter()
                    .map(|v| self.substitute_ty_with_map(v.clone(), substitutions))
                    .collect();
                Ty::EnumVariant(enum_id, applied_values)
            }
            Ty::Tuple(types) => Ty::Tuple(
                types
                    .iter()
                    .map(|param| self.substitute_ty_with_map(param.clone(), substitutions))
                    .collect(),
            ),
            Ty::Void | Ty::Int | Ty::Float | Ty::Bool => ty,
        }
    }

    /// Applies all current global substitutions from the constraint solver (if they were accessible here)
    /// For now, this is a placeholder or needs to be called from ConstraintSolver context.
    /// TypeChecker currently uses it to resolve concrete enum types before looking up variants.
    pub fn apply_substitutions_to_ty(&self, ty: Ty) -> Ty {
        // TODO: This ideally needs access to the main substitution map from ConstraintSolver.
        // For now, it's a simplified pass-through or might apply very local/temporary substitutions
        // if the `Environment` ever held such a thing (which it currently doesn't for global solving).
        // During type inference phase (before solving), this effectively does nothing to global TypeVars.
        // It's more useful if `ty` contains TypeVars that were just locally instantiated (e.g. from a scheme)
        // and `self` contains some temporary substitutions for those.
        // Given the current structure, this might be best as a simple clone or a shallow substitution
        // if `Environment` were to manage any local substitutions not yet part of global constraints.

        // For the purpose of `infer_pattern` trying to see a concrete `Ty::Enum`,
        // if `expected_ty` is a `TypeVar` that *will be* an Enum, this won't resolve it here.
        // The constraints must handle that.
        // However, if `expected_ty` *is* already `Ty::Enum(..., [TypeVar(...)])`, this function
        // won't change it much without global substitutions.

        // Let's assume for now it's just a pass-through during raw inference.
        // The `ConstraintSolver::apply` is the main substitution workhorse.
        ty
    }
}

/// Collect all type-variables occurring free in a single monotype.
pub fn free_type_vars(ty: &Ty) -> HashSet<TypeVarID> {
    let mut s = HashSet::new();
    match ty {
        Ty::TypeVar(v) => {
            s.insert(v.clone());
        }
        Ty::Func(params, ret) => {
            for param in params {
                s.extend(free_type_vars(param));
            }
            s.extend(free_type_vars(ret));
        }
        Ty::Enum(_, generics) => {
            for generic in generics {
                s.extend(free_type_vars(generic));
            }
        }
        // add more Ty variants here as you grow them:
        // Ty::Tuple(elems)  => for e in elems { s.extend(free_type_vars(e)); }
        // Ty::ADT(name, args) => for a in args { s.extend(free_type_vars(a)); }
        _ => {}
    }
    s
}

/// Collect all free type-vars in *every* in-scope Scheme,
/// *after* applying the current substitutions.  We exclude
/// each scheme's own quantified vars.
pub fn free_type_vars_in_env(scopes: &[HashMap<SymbolID, Scheme>]) -> HashSet<TypeVarID> {
    let mut s = HashSet::new();

    for frame in scopes.iter() {
        for scheme in frame.values() {
            // collect its free vars
            let mut ftv = free_type_vars(&scheme.ty);

            // remove those vars that the scheme already quantifies
            for q in &scheme.unbound_vars {
                ftv.remove(q);
            }

            // everything remaining really is free in the env
            s.extend(ftv);
        }
    }

    s
}
