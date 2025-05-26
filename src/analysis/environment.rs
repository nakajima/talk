use std::collections::{HashMap, HashSet};

use crate::{SymbolID, parser::ExprID, type_checker::Ty};

use super::{
    constraint_solver::Constraint,
    type_checker::{Scheme, TypeVarID, TypeVarKind},
    typed_expr::TypedExpr,
};

#[derive(Debug)]
pub struct Environment {
    pub types: HashMap<ExprID, TypedExpr>,
    pub type_var_id: TypeVarID,
    pub constraints: Vec<Constraint>,
    pub scopes: Vec<HashMap<SymbolID, Scheme>>,
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

impl Environment {
    pub fn new() -> Self {
        Self {
            types: HashMap::new(),
            type_var_id: TypeVarID(0, TypeVarKind::Blank),
            constraints: vec![],
            scopes: vec![Default::default()],
        }
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
        // add more Ty variants here as you grow them:
        // Ty::Tuple(elems)  => for e in elems { s.extend(free_type_vars(e)); }
        // Ty::ADT(name, args) => for a in args { s.extend(free_type_vars(a)); }
        _ => {}
    }
    s
}

/// Collect all free type-vars in *every* in-scope Scheme,
/// *after* applying the current substitutions.  We exclude
/// each scheme’s own quantified vars.
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
