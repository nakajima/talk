use std::{
    collections::{HashMap, HashSet},
    ops::IndexMut,
};

use crate::{
    NameResolved, Phase, SourceFile, SymbolID, SymbolTable,
    constraint_solver::{ConstraintSolver, Substitutions},
    parser::ExprID,
    ty::Ty,
    type_checker::TypeError,
    type_constraint::TypeConstraint,
    type_defs::{TypeDef, enum_def::EnumDef, protocol_def::ProtocolDef, struct_def::StructDef},
    type_var_id::{TypeVarID, TypeVarKind},
};

use super::{constraint_solver::Constraint, type_checker::Scheme, typed_expr::TypedExpr};

pub type Scope = HashMap<SymbolID, Scheme>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RawTypeParameter {
    pub symbol_id: SymbolID,
    pub expr_id: ExprID,
    pub placeholder: TypeVarID,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeParameter {
    pub id: SymbolID,
    pub type_var: TypeVarID,
}

pub type TypedExprs = HashMap<ExprID, TypedExpr>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Environment {
    pub typed_exprs: TypedExprs,
    pub type_var_id: TypeVarID,
    pub constraints: Vec<Constraint>,
    pub scopes: Vec<Scope>,
    pub types: HashMap<SymbolID, TypeDef>,
    pub selfs: Vec<Ty>,
    next_id: i32,
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

impl Environment {
    pub fn new() -> Self {
        Self {
            typed_exprs: HashMap::new(),
            type_var_id: TypeVarID::new(0, TypeVarKind::Blank, vec![]),
            constraints: vec![],
            scopes: vec![crate::builtins::default_env_scope()],
            types: crate::builtins::default_env_types(),
            next_id: 0,
            selfs: vec![],
        }
    }

    pub fn next_id(&mut self) -> ExprID {
        let res = self.next_id;
        self.next_id += 1;
        res
    }

    #[track_caller]
    pub fn placeholder(
        &mut self,
        expr_id: &ExprID,
        name: String,
        symbol_id: &SymbolID,
        constraints: Vec<TypeConstraint>,
    ) -> Ty {
        // 1. Create a fresh placeholder for this usage of the type name.
        let usage_placeholder = Ty::TypeVar(
            self.new_type_variable(TypeVarKind::Placeholder(name.clone()), constraints),
        );

        // 2. Generate the InstanceOf constraint.
        self.constraints.push(Constraint::InstanceOf {
            scheme: Scheme {
                ty: usage_placeholder.clone(),
                unbound_vars: vec![],
            },
            expr_id: *expr_id,
            ty: usage_placeholder.clone(),
            symbol_id: *symbol_id,
        });

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "Placeholder {usage_placeholder:?} created for {name}: {}:{}",
                loc.file(),
                loc.line()
            );
        }

        // 3. Return the placeholder.
        usage_placeholder
    }

    pub fn constraints(&self) -> Vec<Constraint> {
        self.constraints.clone()
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn constrain_equality(&mut self, id: ExprID, lhs: Ty, rhs: Ty) {
        if lhs == rhs {
            // No need to constrain equality of equal things
            return;
        }

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "constrain_equality {:?} from {}:{}\n{:?}\n{:?} ",
                id,
                loc.file(),
                loc.line(),
                lhs,
                rhs,
            );
        }
        self.constraints.push(Constraint::Equality(id, lhs, rhs))
    }

    pub fn flush_constraints<P: Phase>(
        &mut self,
        source_file: &mut SourceFile<P>,
        symbol_table: &mut SymbolTable,
    ) -> Result<HashMap<TypeVarID, Ty>, TypeError> {
        let mut solver = ConstraintSolver::new(source_file, self, symbol_table);
        let substitutions = solver.solve();
        Ok(substitutions)
    }

    pub fn constrain_unqualified_member(&mut self, id: ExprID, name: String, result_ty: Ty) {
        self.constraints
            .push(Constraint::UnqualifiedMember(id, name, result_ty))
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn constrain_member(&mut self, id: ExprID, receiver: Ty, name: String, result_ty: Ty) {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "[.] Member {:?} {} from {}:{}\n{:?}\n{:?} ",
                id,
                name,
                loc.file(),
                loc.line(),
                receiver,
                result_ty
            );
        }
        self.constraints
            .push(Constraint::MemberAccess(id, receiver, name, result_ty))
    }

    pub fn replace_typed_exprs_values(&mut self, substitutions: &Substitutions) {
        for (_, typed_expr) in self.typed_exprs.iter_mut() {
            let replaced = ConstraintSolver::<NameResolved>::substitute_ty_with_map(
                &typed_expr.ty,
                substitutions,
            );

            if typed_expr.ty == replaced {
                continue;
            }

            typed_expr.ty = replaced
        }

        for scope in self.scopes.iter_mut() {
            for scheme in scope.values_mut() {
                let replaced = ConstraintSolver::<NameResolved>::substitute_ty_with_map(
                    &scheme.ty,
                    substitutions,
                );

                if scheme.ty == replaced {
                    continue;
                }

                scheme.ty = replaced;
            }
        }
    }

    pub fn replace_constraint_values(&mut self, substitutions: &Substitutions) {
        let mut new_constraints = vec![];
        let mut new_constraint;
        for constraint in self.constraints.iter() {
            new_constraint = constraint.replacing(substitutions);
            new_constraints.push(new_constraint);
        }
        self.constraints = new_constraints;
    }

    pub fn declare(&mut self, symbol_id: SymbolID, scheme: Scheme) {
        log::info!("Declare {symbol_id:?} -> {scheme:?}");
        self.scopes.last_mut().unwrap().insert(symbol_id, scheme);
    }

    pub fn declare_in_parent(&mut self, symbol_id: SymbolID, scheme: Scheme) {
        log::info!(
            "Declaring {:?} {:?} in {:?}",
            symbol_id,
            scheme,
            self.scopes.len()
        );
        self.scopes
            .index_mut(self.scopes.len() - 2)
            .insert(symbol_id, scheme);
    }

    pub fn start_scope(&mut self) {
        self.scopes.push(Default::default());
    }

    // fn specialize(&mut self, scheme: Scheme, type_args: &[Ty]) -> Ty {
    //     let mut substitutions = HashMap::new();
    //     for (unbound_var, type_arg) in scheme.unbound_vars.iter().zip(type_args.iter()) {
    //         substitutions.insert(unbound_var.clone(), type_arg.clone());
    //     }
    //     self.substitute_ty_with_map(scheme.ty, &substitutions)
    // }

    /// Take a monotype `t` and produce a Scheme ∀αᵢ. t,
    /// quantifying exactly those vars not free elsewhere in the env.
    pub fn generalize(&self, t: &Ty, symbol_id: &SymbolID) -> Scheme {
        let ftv_t = free_type_vars(t);
        let ftv_env = free_type_vars_in_env(&self.scopes, *symbol_id);
        let unbound_vars: Vec<TypeVarID> = ftv_t.difference(&ftv_env).cloned().collect();

        Scheme {
            unbound_vars,
            ty: t.clone(),
        }
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "Instantiate {:?} from {}:{}",
                scheme,
                loc.file(),
                loc.line()
            );
        }
        self.instantiate_with_args(scheme, Default::default())
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn instantiate_with_args(&mut self, scheme: &Scheme, args: Substitutions) -> Ty {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "Instantiate {:?} from {}:{}",
                scheme,
                loc.file(),
                loc.line()
            );
        }
        // 1) build a map old_var → fresh_var
        let mut var_map: HashMap<TypeVarID, Ty> = HashMap::new();
        for old in &scheme.unbound_vars {
            if let Some(arg_ty) = args.get(old) {
                var_map.insert(old.clone(), arg_ty.clone());
                // self.constrain_equality(-1, Ty::TypeVar(fresh.clone()), arg_ty.clone());
            } else {
                let type_var = TypeVarKind::Instantiated(old.id);
                let fresh = self.new_type_variable(type_var, old.constraints.clone());
                var_map.insert(old.clone(), Ty::TypeVar(fresh));
            }
        }
        // 2) walk the type, replacing each old with its fresh
        fn walk(ty: &Ty, map: &HashMap<TypeVarID, Ty>) -> Ty {
            match ty {
                Ty::TypeVar(tv) => {
                    if let Some(new_tv) = map.get(tv).cloned() {
                        new_tv
                    } else {
                        Ty::TypeVar(tv.clone())
                    }
                }
                Ty::Func(params, ret, generics) => {
                    let new_params = params.iter().map(|p| walk(p, map)).collect();
                    let new_ret = Box::new(walk(ret, map));
                    let new_generics = generics.iter().map(|g| walk(g, map)).collect();
                    Ty::Func(new_params, new_ret, new_generics)
                }
                Ty::Init(struct_id, params) => {
                    let new_params = params.iter().map(|p| walk(p, map)).collect();
                    Ty::Init(*struct_id, new_params)
                }
                Ty::Closure { func, captures } => {
                    let func = Box::new(walk(func, map));
                    Ty::Closure {
                        func,
                        captures: captures.clone(),
                    }
                }
                Ty::Enum(name, generics) => {
                    let new_generics = generics.iter().map(|g| walk(g, map)).collect();
                    Ty::Enum(*name, new_generics)
                }
                Ty::EnumVariant(name, values) => {
                    let new_values = values.iter().map(|g| walk(g, map)).collect();
                    Ty::EnumVariant(*name, new_values)
                }
                Ty::Struct(sym, generics) => {
                    let new_generics = generics.iter().map(|g| walk(g, map)).collect();
                    Ty::Struct(*sym, new_generics)
                }
                Ty::Protocol(sym, generics) => {
                    let new_generics = generics.iter().map(|g| walk(g, map)).collect();
                    Ty::Protocol(*sym, new_generics)
                }
                Ty::Array(ty) => Ty::Array(Box::new(walk(ty, map))),
                Ty::Tuple(types) => Ty::Tuple(types.iter().map(|p| walk(p, map)).collect()),
                Ty::Void | Ty::Pointer | Ty::Int | Ty::Float | Ty::Bool => ty.clone(),
            }
        }

        walk(&scheme.ty, &var_map)
    }

    pub fn end_scope(&mut self) {
        self.scopes.pop();
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn ty_for_symbol(
        &mut self,
        id: &ExprID,
        name: String,
        symbol_id: &SymbolID,
        constraints: &[TypeConstraint],
    ) -> Ty {
        let ret = if let Ok(scheme) = self.lookup_symbol(symbol_id).cloned() {
            scheme.ty.clone()
            // self.instantiate(&scheme)
        } else {
            self.placeholder(id, name.to_string(), symbol_id, constraints.to_vec())
        };

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "ty_for_symbol {} ({:?}) = {:?} from {}:{}",
                name,
                symbol_id,
                ret,
                loc.file(),
                loc.line()
            );
        }

        ret
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn new_type_variable(
        &mut self,
        kind: TypeVarKind,
        constraints: Vec<TypeConstraint>,
    ) -> TypeVarID {
        self.type_var_id = TypeVarID::new(self.type_var_id.id + 1, kind, constraints);

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "+ {:?} from {}:{}",
                Ty::TypeVar(self.type_var_id.clone()),
                loc.file(),
                loc.line()
            );
        }

        self.type_var_id.clone()
    }

    pub fn register(&mut self, def: &TypeDef) {
        match def {
            TypeDef::Enum(def) => self.register_enum(def),
            TypeDef::Struct(def) => self.register_struct(def),
            TypeDef::Protocol(def) => self.register_protocol(def),
        }
    }

    // Helper methods for enum definitions
    pub fn register_enum(&mut self, def: &EnumDef) {
        log::info!("Registering {def:?}");
        self.declare(
            def.name.unwrap(),
            Scheme {
                ty: Ty::Enum(def.name.unwrap(), def.canonical_type_parameters()),
                unbound_vars: def.canonical_type_vars(),
            },
        );
        self.types
            .insert(def.clone().name.unwrap(), TypeDef::Enum(def.clone()));
    }

    pub fn register_struct(&mut self, def: &StructDef) {
        log::info!("Registering {def:?}");
        self.declare(
            def.symbol_id,
            Scheme {
                ty: Ty::Struct(def.symbol_id, def.canonical_type_parameters()),
                unbound_vars: def.canonical_type_vars(),
            },
        );
        self.types
            .insert(def.symbol_id, TypeDef::Struct(def.clone()));
    }

    pub fn register_protocol(&mut self, def: &ProtocolDef) {
        log::info!("Registering {def:?}");
        self.declare(
            def.symbol_id,
            Scheme {
                ty: Ty::Protocol(def.symbol_id, def.canonical_associated_types()),
                unbound_vars: def.canonical_associated_type_vars(),
            },
        );
        self.types
            .insert(def.symbol_id, TypeDef::Protocol(def.clone()));
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn lookup_symbol(&self, symbol_id: &SymbolID) -> Result<&Scheme, TypeError> {
        if let Some(scheme) = self
            .scopes
            .iter()
            .rev()
            .find_map(|frame| frame.get(symbol_id))
        {
            Ok(scheme)
        } else {
            if cfg!(debug_assertions) {
                let loc = std::panic::Location::caller();
                log::warn!(
                    "Did not find symbol {symbol_id:?}: {}:{}",
                    loc.file(),
                    loc.line()
                );
            }

            Err(TypeError::Unresolved(format!(
                "Did not find symbol {:?} in scope: {:?}",
                symbol_id, self.scopes
            )))
        }
    }

    pub fn lookup_type(&self, name: &SymbolID) -> Option<&TypeDef> {
        self.types.get(name)
    }

    pub fn lookup_type_mut(&mut self, name: &SymbolID) -> Option<&mut TypeDef> {
        self.types.get_mut(name)
    }

    pub fn is_struct_symbol(&self, symbol_id: &SymbolID) -> bool {
        matches!(self.lookup_type(symbol_id), Some(TypeDef::Struct(_)))
    }

    pub fn lookup_enum(&self, name: &SymbolID) -> Option<&EnumDef> {
        if let Some(TypeDef::Enum(def)) = self.types.get(name) {
            Some(def)
        } else {
            None
        }
    }

    pub fn lookup_enum_mut(&mut self, name: &SymbolID) -> Option<&mut EnumDef> {
        if let Some(TypeDef::Enum(def)) = self.types.get_mut(name) {
            Some(def)
        } else {
            None
        }
    }

    pub fn lookup_struct(&self, name: &SymbolID) -> Option<&StructDef> {
        if let Some(TypeDef::Struct(def)) = self.types.get(name) {
            Some(def)
        } else {
            None
        }
    }

    pub fn lookup_protocol(&self, name: &SymbolID) -> Option<&ProtocolDef> {
        if let Some(TypeDef::Protocol(def)) = self.types.get(name) {
            Some(def)
        } else {
            None
        }
    }
}

/// Collect all type-variables occurring free in a single monotype.
pub fn free_type_vars(ty: &Ty) -> HashSet<TypeVarID> {
    let mut s = HashSet::new();
    match ty {
        Ty::TypeVar(v) => {
            s.insert(v.clone());
        }
        Ty::Init(_, params) => {
            for param in params {
                s.extend(free_type_vars(param));
            }
        }
        Ty::Func(params, ret, generics) => {
            for param in params {
                s.extend(free_type_vars(param));
            }
            for generic in generics {
                s.extend(free_type_vars(generic));
            }
            s.extend(free_type_vars(ret));
        }
        Ty::Closure { func, .. } => {
            s.extend(free_type_vars(func));
        }
        Ty::Enum(_, generics) => {
            for generic in generics {
                s.extend(free_type_vars(generic));
            }
        }
        Ty::EnumVariant(_, values) => {
            for value in values {
                s.extend(free_type_vars(value));
            }
        }
        Ty::Tuple(items) => {
            for item in items {
                s.extend(free_type_vars(item));
            }
        }
        Ty::Array(ty) => {
            s.extend(free_type_vars(ty));
        }
        Ty::Struct(_, generics) => {
            for generic in generics {
                s.extend(free_type_vars(generic));
            }
        }
        Ty::Protocol(_, generics) => {
            for generic in generics {
                s.extend(free_type_vars(generic));
            }
        }
        Ty::Void | Ty::Int | Ty::Bool | Ty::Float | Ty::Pointer => {
            // These types contain no nested types, so there's nothing to do.
        }
    }
    s
}

/// Collect all free type-vars in *every* in-scope Scheme,
/// *after* applying the current substitutions.  We exclude
/// each scheme's own quantified vars.
pub fn free_type_vars_in_env(
    scopes: &[HashMap<SymbolID, Scheme>],
    ignoring: SymbolID,
) -> HashSet<TypeVarID> {
    let mut s = HashSet::new();

    for frame in scopes.iter() {
        for (symbol_id, scheme) in frame {
            if symbol_id == &ignoring {
                continue;
            }

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

#[cfg(test)]
mod generalize_tests {
    use crate::{
        SymbolID,
        environment::{Environment, Scope},
        ty::Ty,
        type_checker::Scheme,
        type_var_id::{TypeVarID, TypeVarKind},
    };
    use std::collections::HashSet;

    // Helper to create a blank type variable.
    fn new_tv(id: i32) -> TypeVarID {
        TypeVarID::new(id, TypeVarKind::Blank, vec![])
    }

    // Helper to create a Ty::TypeVar.
    fn ty_var(id: i32) -> Ty {
        Ty::TypeVar(new_tv(id))
    }

    #[test]
    fn test_generalize_in_empty_env() {
        // In an empty environment, generalize(a -> b) should produce `forall a, b. a -> b`.
        // All type variables in the type are free and should be bound.
        let env = Environment::new();
        let ty_to_generalize = Ty::Func(vec![ty_var(1)], Box::new(ty_var(2)), vec![]);

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // The scheme's unbound_vars should contain both tv1 and tv2.
        assert_eq!(scheme.ty, ty_to_generalize);
        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars.into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(1), new_tv(2)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_with_free_var_in_env() {
        // If the environment already contains a free `a`, then generalize(a -> b)
        // should produce `forall b. a -> b`. `a` should not be bound again.
        let mut env = Environment::new();
        let tv_a = new_tv(1);

        // Add a variable to the environment's scope that has `a` as a free variable.
        // For example, a variable `x: a`. The scheme for this is `Scheme { unbound_vars: [], ty: a }`.
        let mut initial_scope = Scope::new();
        initial_scope.insert(
            SymbolID(0),
            Scheme {
                unbound_vars: vec![],
                ty: Ty::TypeVar(tv_a.clone()),
            },
        );
        env.scopes = vec![initial_scope];

        let ty_to_generalize =
            Ty::Func(vec![Ty::TypeVar(tv_a.clone())], Box::new(ty_var(2)), vec![]);
        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // The scheme should only bind `b` (tv2). `a` remains free.
        assert_eq!(scheme.ty, ty_to_generalize);
        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars.into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(2)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_with_bound_var_in_env() {
        // If the environment contains `id: forall a. a -> a`, and we generalize `b -> c`,
        // the `a` from the `id` function is not free in the environment and should have no effect.
        // The result should be `forall b, c. b -> c`.
        let mut env = Environment::new();
        let tv_a = new_tv(1);

        // Create a scheme for `id: forall a. a -> a`.
        let id_scheme = Scheme {
            unbound_vars: vec![tv_a.clone()],
            ty: Ty::Func(
                vec![Ty::TypeVar(tv_a.clone())],
                Box::new(Ty::TypeVar(tv_a.clone())),
                vec![],
            ),
        };

        let mut initial_scope = Scope::new();
        initial_scope.insert(SymbolID(0), id_scheme);
        env.scopes = vec![initial_scope];

        let ty_to_generalize = Ty::Func(vec![ty_var(2)], Box::new(ty_var(3)), vec![]);
        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // The scheme should bind `b` (tv2) and `c` (tv3).
        assert_eq!(scheme.ty, ty_to_generalize);
        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars.into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(2), new_tv(3)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_no_new_variables() {
        // If we generalize a type `a` where `a` is already free in the environment,
        // the resulting scheme should bind no variables.
        let mut env = Environment::new();
        let tv_a = new_tv(1);

        let mut initial_scope = Scope::new();
        initial_scope.insert(
            SymbolID(0),
            Scheme {
                unbound_vars: vec![],
                ty: Ty::TypeVar(tv_a.clone()),
            },
        );
        env.scopes = vec![initial_scope];

        let ty_to_generalize = Ty::TypeVar(tv_a.clone());
        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // The scheme should bind nothing new.
        assert!(scheme.unbound_vars.is_empty());
        assert_eq!(scheme.ty, ty_to_generalize);
    }

    #[test]
    fn test_generalize_tuple_type() {
        // generalize((a, b)) -> forall a, b. (a, b)
        let env = Environment::new();
        let ty_to_generalize = Ty::Tuple(vec![ty_var(1), ty_var(2)]);

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars.into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(1), new_tv(2)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_array_type() {
        // generalize(Array<a>) -> forall a. Array<a>
        let env = Environment::new();
        let ty_to_generalize = Ty::Array(Box::new(ty_var(1)));

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars.into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(1)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_struct_type() {
        // generalize(Struct<a, b>) -> forall a, b. Struct<a, b>
        let env = Environment::new();
        let ty_to_generalize = Ty::Struct(SymbolID(100), vec![ty_var(1), ty_var(2)]);

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars.into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(1), new_tv(2)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    // #[test]
    // fn test_generalize_closure_captures() {
    //     // Generalize a closure type that captures a free variable.
    //     // The captured variable `b` should be generalized.
    //     let env = Environment::new();
    //     let func_ty = Box::new(Ty::Func(vec![], Box::new(Ty::Int), vec![])); // func() -> Int
    //     let ty_to_generalize = Ty::Closure {
    //         func: func_ty,
    //         captures: vec![ty_var(1)], // captures `b`
    //     };

    //     let scheme = env.generalize(&ty_to_generalize);

    //     let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars.into_iter().collect();
    //     let expected_vars: HashSet<TypeVarID> = [new_tv(1)].into_iter().collect();
    //     assert_eq!(bound_vars, expected_vars);
    // }

    #[test]
    fn test_generalize_deeply_nested_type() {
        // If env contains `a`, generalize `func() -> (Array<b>, c)`
        // should result in `forall b, c. func() -> (Array<b>, c)`
        let mut env = Environment::new();
        let tv_a = new_tv(1);

        // Put `a` into the environment as a free variable
        let mut initial_scope = Scope::new();
        initial_scope.insert(
            SymbolID(0),
            Scheme {
                unbound_vars: vec![],
                ty: Ty::TypeVar(tv_a.clone()),
            },
        );
        env.scopes = vec![initial_scope];

        let array_b = Ty::Array(Box::new(ty_var(2))); // b
        let tuple = Ty::Tuple(vec![array_b, ty_var(3)]); // c
        let ty_to_generalize = Ty::Func(vec![], Box::new(tuple), vec![]);

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // Should bind `b` and `c`, but not `a`.
        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars.into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(2), new_tv(3)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }
}
