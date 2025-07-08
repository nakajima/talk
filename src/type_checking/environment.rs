use std::collections::{BTreeMap, HashSet};

use crate::{
    SymbolID, SymbolTable,
    constraint::Constraint,
    constraint_solver::ConstraintSolver,
    parser::ExprID,
    substitutions::Substitutions,
    ty::Ty,
    type_checker::TypeError,
    type_defs::{TypeDef, enum_def::EnumDef, protocol_def::ProtocolDef, struct_def::StructDef},
    type_var_context::TypeVarContext,
    type_var_id::{TypeVarID, TypeVarKind},
};

use super::{type_checker::Scheme, typed_expr::TypedExpr};

pub type Scope = BTreeMap<SymbolID, Scheme>;

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

pub type TypedExprs = BTreeMap<ExprID, TypedExpr>;

#[derive(Debug, Clone)]
pub struct Environment {
    pub typed_exprs: TypedExprs,
    constraints: Vec<Constraint>,
    pub scopes: Vec<Scope>,
    pub types: BTreeMap<SymbolID, TypeDef>,
    pub selfs: Vec<Ty>,
    pub context: TypeVarContext,
    next_id: i32,
}

impl Default for Environment {
    fn default() -> Self {
        let mut context = TypeVarContext::default();
        context.import_builtins();

        Self {
            typed_exprs: BTreeMap::new(),
            constraints: vec![],
            scopes: vec![crate::builtins::default_env_scope()],
            types: crate::builtins::default_env_types(),
            next_id: 0,
            selfs: vec![],
            context,
        }
    }
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn next_expr_id(&mut self) -> ExprID {
        let res = self.next_id;
        self.next_id += 1;
        res
    }

    pub fn next_type_var_id(&self) -> usize {
        self.context.next_id()
    }

    #[track_caller]
    pub fn placeholder(
        &mut self,
        expr_id: &ExprID,
        name: String,
        symbol_id: &SymbolID,
        constraints: Vec<Constraint>,
    ) -> Ty {
        let type_var = self.new_type_variable(TypeVarKind::Placeholder(name.clone()));
        let usage_placeholder = Ty::TypeVar(type_var);

        self.constrain(Constraint::InstanceOf {
            scheme: Scheme::new(usage_placeholder.clone(), vec![], constraints),
            expr_id: *expr_id,
            ty: usage_placeholder.clone(),
            symbol_id: *symbol_id,
        });

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            tracing::trace!(
                "Placeholder {usage_placeholder:?} created for {name}: {}:{}",
                loc.file(),
                loc.line()
            );
        }

        usage_placeholder
    }

    pub fn constraints(&self) -> Vec<Constraint> {
        self.constraints.clone()
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn constrain(&mut self, constraint: Constraint) {
        if !constraint.needs_solving() {
            return;
        }

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            tracing::info!("⊢ {:#?} ({}:{})", constraint, loc.file(), loc.line(),);
        }

        // #[allow(clippy::panic)]
        // if constraint.contains_canonical_type_parameter() {
        //     panic!("Constraints must not contain canonical type params: {constraint:?}")
        // }

        self.constraints.push(constraint)
    }

    pub fn clear_constraints(&mut self) {
        self.constraints.clear()
    }

    #[tracing::instrument(skip(self, symbol_table))]
    pub fn flush_constraints(
        &mut self,
        symbol_table: &mut SymbolTable,
    ) -> Result<Substitutions, TypeError> {
        let mut solver = ConstraintSolver::new(self, symbol_table);
        let solution = solver.solve();

        for constraint in solution.unsolved_constraints {
            self.constrain(constraint);
        }

        Ok(solution.substitutions)
    }

    pub fn replace_typed_exprs_values(&mut self, substitutions: &mut Substitutions) {
        for (_, typed_expr) in self.typed_exprs.iter_mut() {
            let replaced = substitutions.apply(&typed_expr.ty, 0, &mut self.context); // ConstraintSolver::substitute_ty_with_map(&typed_expr.ty, substitutions);

            if typed_expr.ty == replaced {
                continue;
            }

            typed_expr.ty = replaced
        }

        for scope in self.scopes.iter_mut() {
            for scheme in scope.values_mut() {
                let replaced = substitutions.apply(&scheme.ty(), 0, &mut self.context);

                if scheme.ty() == replaced {
                    continue;
                }

                *scheme = Scheme::new(replaced, scheme.unbound_vars(), scheme.constraints())
            }
        }
    }

    pub fn replace_constraint_values(&mut self, substitutions: &mut Substitutions) {
        let mut new_constraints = vec![];
        let mut new_constraint;
        for constraint in self.constraints.iter() {
            new_constraint = constraint.replacing(substitutions, &mut self.context);
            new_constraints.push(new_constraint);
        }
        self.constraints = new_constraints;
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn declare(&mut self, symbol_id: SymbolID, scheme: Scheme) -> Result<(), TypeError> {
        let loc = std::panic::Location::caller();
        tracing::debug!(
            "λ Declare {symbol_id:?} -> {scheme:?} ({}:{})",
            loc.file(),
            loc.line()
        );

        if let Some(scheme) = self
            .scopes
            .last()
            .ok_or(TypeError::Unknown(format!(
                "Unable to declare symbol {symbol_id:?} without scope"
            )))?
            .get(&symbol_id)
        {
            tracing::warn!("Already declared {symbol_id:?} in scope: {scheme:?}");
        }

        self.scopes
            .last_mut()
            .ok_or(TypeError::Unknown(format!(
                "Unable to declare symbol {symbol_id:?} without scope"
            )))?
            .insert(symbol_id, scheme);

        Ok(())
    }

    pub fn start_scope(&mut self) {
        self.scopes.push(Default::default());
    }

    /// Take a monotype `t` and produce a Scheme ∀αᵢ. t,
    /// quantifying exactly those vars not free elsewhere in the env.
    #[tracing::instrument(level = "DEBUG", skip(self))]
    pub fn generalize(&mut self, t: &Ty, symbol_id: &SymbolID) -> Scheme {
        let ftv_t = free_type_vars(t);
        let ftv_env = free_type_vars_in_env(&self.scopes, *symbol_id);
        let unbound_vars: Vec<TypeVarID> = ftv_t.difference(&ftv_env).cloned().collect();

        // Apply constraints to generalized
        let mut constraints = vec![];
        for var in &unbound_vars {
            let collected = self
                .constraints
                .iter()
                .filter(|c| c.contains(|ty| ty == &Ty::TypeVar(var.clone())))
                .cloned()
                .collect::<Vec<Constraint>>();
            constraints.extend(collected);
        }

        Scheme::new(t.clone(), unbound_vars, constraints)
    }

    pub fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        self.instantiate_with_args(scheme, Default::default())
    }

    #[tracing::instrument(skip(self), fields(result))]
    pub fn instantiate_with_args(&mut self, scheme: &Scheme, args: Substitutions) -> Ty {
        let mut var_map = Substitutions::new();
        for old in &scheme.unbound_vars() {
            if let Some(arg_ty) = args.get(old) {
                var_map.insert(old.clone(), arg_ty.clone());
            } else {
                let fresh = self.new_type_variable(TypeVarKind::Instantiated(old.id));
                var_map.insert(old.clone(), Ty::TypeVar(fresh));
            }
        }

        for constraint in scheme.constraints() {
            let new_constraint = constraint.replacing(&mut var_map, &mut self.context);
            self.constrain(new_constraint);
        }

        walk(&scheme.ty(), &var_map)
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
        constraints: &[Constraint],
    ) -> Ty {
        let ret = if let Ok(scheme) = self.lookup_symbol(symbol_id).cloned() {
            if !constraints.is_empty() {
                tracing::warn!("-> Ditching constraints: {constraints:?}");
            }

            scheme.ty()
        } else {
            self.placeholder(id, name.to_string(), symbol_id, constraints.to_vec())
        };

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            tracing::trace!(
                "T ty_for_symbol {} ({:?}) = {:?} from {}:{}",
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
    pub fn new_type_variable(&mut self, kind: TypeVarKind) -> TypeVarID {
        let type_var_id = self.context.new_var(kind);

        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            tracing::trace!(
                "+ {:?} from {}:{}",
                Ty::TypeVar(type_var_id.clone()),
                loc.file(),
                loc.line()
            );
        }

        type_var_id
    }

    pub fn register(&mut self, def: &TypeDef) -> Result<(), TypeError> {
        #[cfg(debug_assertions)]
        if let Some(existing) = self.lookup_type(&def.symbol_id()) {
            if existing != def {
                tracing::info!("Updating {def:?}");
            }
        } else {
            tracing::info!("Registering {def:?}");
        }

        match def {
            TypeDef::Enum(def) => self.register_enum(def),
            TypeDef::Struct(def) => self.register_struct(def),
            TypeDef::Protocol(def) => self.register_protocol(def),
            TypeDef::Builtin(def) => {
                self.types
                    .insert(def.symbol_id, TypeDef::Builtin(def.clone()));
                Ok(())
            }
        }
    }

    // Helper methods for enum definitions
    pub fn register_enum(&mut self, def: &EnumDef) -> Result<(), TypeError> {
        self.declare(
            def.symbol_id,
            Scheme::new(
                Ty::Enum(def.symbol_id, def.canonical_type_parameters()),
                def.canonical_type_vars(),
                vec![],
            ),
        )?;
        self.types
            .insert(def.clone().symbol_id, TypeDef::Enum(def.clone()));
        Ok(())
    }

    pub fn register_struct(&mut self, def: &StructDef) -> Result<(), TypeError> {
        self.declare(
            def.symbol_id,
            Scheme::new(
                Ty::Struct(def.symbol_id, def.canonical_type_parameters()),
                def.canonical_type_vars(),
                vec![],
            ),
        )?;
        self.types
            .insert(def.symbol_id, TypeDef::Struct(def.clone()));

        Ok(())
    }

    pub fn register_protocol(&mut self, def: &ProtocolDef) -> Result<(), TypeError> {
        self.declare(
            def.symbol_id,
            Scheme::new(
                Ty::Protocol(def.symbol_id, def.canonical_associated_types()),
                def.canonical_associated_type_vars(),
                vec![],
            ),
        )?;
        self.types
            .insert(def.symbol_id, TypeDef::Protocol(def.clone()));

        Ok(())
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
                tracing::warn!(
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

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn lookup_symbol_mut(&mut self, symbol_id: &SymbolID) -> Result<&mut Scheme, TypeError> {
        let Some(scheme) = self
            .scopes
            .iter_mut()
            .rev()
            .find_map(|frame| frame.get_mut(symbol_id))
        else {
            if cfg!(debug_assertions) {
                let loc = std::panic::Location::caller();
                tracing::warn!(
                    "Did not find symbol {symbol_id:?}: {}:{}",
                    loc.file(),
                    loc.line()
                );
            }

            return Err(TypeError::Unresolved(format!(
                "Did not find symbol {symbol_id:?} in scope",
            )));
        };

        Ok(scheme)
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

fn walk(ty: &Ty, map: &Substitutions) -> Ty {
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
        Ty::Void | Ty::Pointer | Ty::Int | Ty::Float | Ty::Bool | Ty::SelfType | Ty::Byte => {
            ty.clone()
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
        Ty::Void | Ty::Int | Ty::Bool | Ty::Float | Ty::Pointer | Ty::SelfType | Ty::Byte => {
            // These types contain no nested types, so there's nothing to do.
        }
    }
    s
}

/// Collect all free type-vars in *every* in-scope Scheme,
/// *after* applying the current substitutions.  We exclude
/// each scheme's own quantified vars.
pub fn free_type_vars_in_env(
    scopes: &[BTreeMap<SymbolID, Scheme>],
    ignoring: SymbolID,
) -> HashSet<TypeVarID> {
    let mut s = HashSet::new();

    for frame in scopes.iter() {
        for (symbol_id, scheme) in frame {
            if symbol_id == &ignoring {
                continue;
            }

            let mut ftv = free_type_vars(&scheme.ty());

            // remove those vars that the scheme already quantifies
            for q in &scheme.unbound_vars() {
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
    fn new_tv(id: u32) -> TypeVarID {
        TypeVarID::new(id, TypeVarKind::Blank)
    }

    // Helper to create a Ty::TypeVar.
    fn ty_var(id: u32) -> Ty {
        Ty::TypeVar(new_tv(id))
    }

    #[test]
    fn test_generalize_in_empty_env() {
        // In an empty environment, generalize(a -> b) should produce `forall a, b. a -> b`.
        // All type variables in the type are free and should be bound.
        let mut env = Environment::default();
        let ty_to_generalize = Ty::Func(vec![ty_var(1)], Box::new(ty_var(2)), vec![]);

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // The scheme's unbound_vars should contain both tv1 and tv2.
        assert_eq!(scheme.ty(), ty_to_generalize);
        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars().into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(1), new_tv(2)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_with_free_var_in_env() {
        // If the environment already contains a free `a`, then generalize(a -> b)
        // should produce `forall b. a -> b`. `a` should not be bound again.
        let mut env = Environment::default();
        let tv_a = new_tv(1);

        // Add a variable to the environment's scope that has `a` as a free variable.
        // For example, a variable `x: a`. The scheme for this is `Scheme { unbound_vars: [], ty: a }`.
        let mut initial_scope = Scope::new();
        initial_scope.insert(
            SymbolID(0),
            Scheme::new(Ty::TypeVar(tv_a.clone()), vec![], vec![]),
        );
        env.scopes = vec![initial_scope];

        let ty_to_generalize =
            Ty::Func(vec![Ty::TypeVar(tv_a.clone())], Box::new(ty_var(2)), vec![]);
        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // The scheme should only bind `b` (tv2). `a` remains free.
        assert_eq!(scheme.ty(), ty_to_generalize);
        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars().into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(2)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_with_bound_var_in_env() {
        // If the environment contains `id: forall a. a -> a`, and we generalize `b -> c`,
        // the `a` from the `id` function is not free in the environment and should have no effect.
        // The result should be `forall b, c. b -> c`.
        let mut env = Environment::default();
        let tv_a = new_tv(1);

        // Create a scheme for `id: forall a. a -> a`.
        let id_scheme = Scheme::new(
            Ty::Func(
                vec![Ty::TypeVar(tv_a.clone())],
                Box::new(Ty::TypeVar(tv_a.clone())),
                vec![],
            ),
            vec![tv_a.clone()],
            vec![],
        );

        let mut initial_scope = Scope::new();
        initial_scope.insert(SymbolID(0), id_scheme);
        env.scopes = vec![initial_scope];

        let ty_to_generalize = Ty::Func(vec![ty_var(2)], Box::new(ty_var(3)), vec![]);
        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // The scheme should bind `b` (tv2) and `c` (tv3).
        assert_eq!(scheme.ty(), ty_to_generalize);
        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars().into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(2), new_tv(3)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_no_new_variables() {
        // If we generalize a type `a` where `a` is already free in the environment,
        // the resulting scheme should bind no variables.
        let mut env = Environment::default();
        let tv_a = new_tv(1);

        let mut initial_scope = Scope::new();
        initial_scope.insert(
            SymbolID(0),
            Scheme::new(Ty::TypeVar(tv_a.clone()), vec![], vec![]),
        );
        env.scopes = vec![initial_scope];

        let ty_to_generalize = Ty::TypeVar(tv_a.clone());
        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // The scheme should bind nothing new.
        assert!(scheme.unbound_vars().is_empty());
        assert_eq!(scheme.ty(), ty_to_generalize);
    }

    #[test]
    fn test_generalize_tuple_type() {
        // generalize((a, b)) -> forall a, b. (a, b)
        let mut env = Environment::default();
        let ty_to_generalize = Ty::Tuple(vec![ty_var(1), ty_var(2)]);

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars().into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(1), new_tv(2)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_array_type() {
        // generalize(Array<a>) -> forall a. Array<a>
        let mut env = Environment::default();
        let ty_to_generalize = Ty::Array(Box::new(ty_var(1)));

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars().into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(1)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }

    #[test]
    fn test_generalize_struct_type() {
        // generalize(Struct<a, b>) -> forall a, b. Struct<a, b>
        let mut env = Environment::default();
        let ty_to_generalize = Ty::Struct(SymbolID(100), vec![ty_var(1), ty_var(2)]);

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars().into_iter().collect();
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
        let mut env = Environment::default();
        let tv_a = new_tv(1);

        // Put `a` into the environment as a free variable
        let mut initial_scope = Scope::new();
        initial_scope.insert(
            SymbolID(0),
            Scheme::new(Ty::TypeVar(tv_a.clone()), vec![], vec![]),
        );
        env.scopes = vec![initial_scope];

        let array_b = Ty::Array(Box::new(ty_var(2))); // b
        let tuple = Ty::Tuple(vec![array_b, ty_var(3)]); // c
        let ty_to_generalize = Ty::Func(vec![], Box::new(tuple), vec![]);

        let scheme = env.generalize(&ty_to_generalize, &SymbolID(1));

        // Should bind `b` and `c`, but not `a`.
        let bound_vars: HashSet<TypeVarID> = scheme.unbound_vars().into_iter().collect();
        let expected_vars: HashSet<TypeVarID> = [new_tv(2), new_tv(3)].into_iter().collect();
        assert_eq!(bound_vars, expected_vars);
    }
}
