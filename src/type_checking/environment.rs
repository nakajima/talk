use std::{
    collections::{HashMap, HashSet},
    ops::IndexMut,
    path::PathBuf,
};

use crate::{
    Phase, SourceFile, SymbolID, SymbolTable,
    constraint_solver::{ConstraintSolver, Substitutions},
    parser::ExprID,
    source_file,
    ty::Ty,
    type_checker::TypeError,
};

use super::{
    constraint_solver::Constraint,
    type_checker::{Scheme, TypeVarID, TypeVarKind},
    typed_expr::TypedExpr,
};

pub type Scope = HashMap<SymbolID, Scheme>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawEnumVariant {
    pub name: String,
    pub values: Vec<ExprID>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariant {
    pub name: String,
    pub values: Vec<Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDef {
    pub name: Option<SymbolID>,
    pub type_parameters: TypeParams,
    pub raw_variants: Vec<RawEnumVariant>,
    pub variants: Vec<EnumVariant>,
    pub raw_methods: HashMap<String, RawMethod>,
    pub methods: HashMap<String, Method>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDef {
    pub symbol_id: SymbolID,
    pub name_str: String,
    pub type_parameters: TypeParams,
    pub properties: Vec<Property>,
    pub methods: HashMap<String, RawMethod>,
    pub initializers: Vec<(PathBuf, ExprID)>,
}

impl StructDef {
    pub fn new(
        symbol_id: SymbolID,
        name_str: String,
        type_parameters: TypeParams,
        properties: Vec<Property>,
        methods: HashMap<String, RawMethod>,
        initializers: Vec<(PathBuf, ExprID)>,
    ) -> Self {
        Self {
            symbol_id,
            name_str,
            type_parameters,
            properties,
            methods,
            initializers,
        }
    }

    pub fn member_ty(&self, name: &str) -> Option<&Ty> {
        // if let Some(property) = self.properties.iter().find(|p| p.name == name) {
        //     return Some(&property.ty);
        // }

        // if let Some(method) = self.methods.get(name) {
        //     return Some(&method.ty);
        // }

        None
    }

    pub fn type_repr(&self, type_parameters: &TypeParams) -> Ty {
        Ty::Struct(self.symbol_id, type_parameters.clone())
    }
}

impl EnumDef {
    pub(crate) fn tag_with_variant_for(&self, name: &str) -> (u16, &EnumVariant) {
        for (i, variant) in self.variants.iter().enumerate() {
            if variant.name == name {
                return (i as u16, variant);
            }
        }

        panic!("no variant named {:?} for {:?}", name, self.name)
    }
}

pub type TypeParams = Vec<Ty>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDef {
    Enum(EnumDef),
    Struct(StructDef),
}

pub type TypedExprs = HashMap<ExprID, TypedExpr>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Property {
    pub name: String,
    pub symbol: SymbolID,
    pub expr_id: ExprID,
}

impl Property {
    pub fn new(name: String, symbol: SymbolID, expr_id: ExprID) -> Self {
        Self {
            name,
            symbol,
            expr_id,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub name: String,
    pub ty: Ty,
}

impl Method {
    pub fn new(name: String, ty: Ty) -> Self {
        Self { name, ty }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RawMethod {
    pub name: String,
    pub expr_id: ExprID,
}

impl RawMethod {
    pub fn new(name: String, expr_id: ExprID) -> Self {
        Self { name, expr_id }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Environment {
    pub typed_exprs: TypedExprs,
    pub type_var_id: TypeVarID,
    pub constraints: Vec<Constraint>,
    pub scopes: Vec<Scope>,
    pub types: HashMap<SymbolID, TypeDef>,
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
            type_var_id: TypeVarID(0, TypeVarKind::Blank),
            constraints: vec![],
            scopes: vec![crate::builtins::default_env_scope()],
            types: crate::builtins::default_env_types(),
            next_id: 0,
        }
    }

    pub fn next_id(&mut self) -> ExprID {
        let res = self.next_id;
        self.next_id += 1;
        res
    }

    #[track_caller]
    pub fn placeholder(&mut self, expr_id: &ExprID, name: String, symbol_id: &SymbolID) -> Ty {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::warn!("placeholder created: {}:{}", loc.file(), loc.line());
        }

        // 1. Create a fresh placeholder for this usage of the type name.
        let usage_placeholder = Ty::TypeVar(self.new_type_variable(TypeVarKind::Placeholder(name)));

        // 2. Generate the InstanceOf constraint.
        self.constraints.push(Constraint::InstanceOf {
            expr_id: *expr_id,
            ty: usage_placeholder.clone(),
            symbol_id: *symbol_id,
        });

        // 3. Return the placeholder.
        usage_placeholder
    }

    pub fn constraints(&self) -> Vec<Constraint> {
        self.constraints.clone()
    }

    #[track_caller]
    pub fn constrain_equality(&mut self, id: ExprID, lhs: Ty, rhs: Ty) {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::warn!(
                "constrain_equality {:?} {:?} {:?} from {}:{}",
                id,
                lhs,
                rhs,
                loc.file(),
                loc.line()
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
        self.constraints.clear();
        Ok(substitutions)
    }

    pub fn constraint_construction(
        &mut self,
        id: ExprID,
        initializes_id: SymbolID,
        args: Vec<Ty>,
        ret: TypeVarID,
    ) {
        self.constraints.push(Constraint::InitializerCall {
            expr_id: id,
            initializes_id,
            args,
            ret,
        })
    }

    pub fn constrain_unqualified_member(&mut self, id: ExprID, name: String, result_ty: Ty) {
        self.constraints
            .push(Constraint::UnqualifiedMember(id, name, result_ty))
    }

    pub fn constrain_member(&mut self, id: ExprID, receiver: Ty, name: String, result_ty: Ty) {
        self.constraints
            .push(Constraint::MemberAccess(id, receiver, name, result_ty))
    }

    /// Look up the scheme for `sym`, then immediately instantiate it.
    fn instantiate_symbol(&mut self, symbol_id: SymbolID) -> Result<Ty, TypeError> {
        let Ok(scheme) = self.lookup_symbol(&symbol_id).cloned() else {
            log::error!(
                "Trying to instantiate unknown symbol: {:?} in {:?}",
                symbol_id,
                self.scopes
            );
            return Err(TypeError::Unknown("Unknown symbol".into()));
        };

        Ok(self.instantiate(&scheme))
    }

    pub fn replace_constraint_values(&mut self, substitutions: Substitutions) {
        let mut new_constraints = vec![];
        let mut new_constraint;
        for constraint in self.constraints.iter() {
            new_constraint = constraint.replacing(&substitutions);
            new_constraints.push(new_constraint);
        }
        self.constraints = new_constraints;
    }

    pub fn declare(&mut self, symbol_id: SymbolID, scheme: Scheme) {
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
    pub fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        // 1) build a map old_var → fresh_var
        let mut var_map: HashMap<TypeVarID, TypeVarID> = HashMap::new();
        for old in &scheme.unbound_vars {
            // preserve the original kind when making a fresh one
            let fresh = self.new_type_variable(old.1.clone());
            var_map.insert(old.clone(), fresh);
        }
        // 2) walk the type, replacing each old with its fresh
        fn walk<'a>(ty: &Ty, map: &HashMap<TypeVarID, TypeVarID>) -> Ty {
            match ty {
                Ty::TypeVar(tv) => {
                    if let Some(new_tv) = map.get(&tv).cloned() {
                        Ty::TypeVar(new_tv)
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

    pub fn ty_for_symbol(&mut self, id: &ExprID, name: String, symbol_id: &SymbolID) -> Ty {
        if let Ok(scheme) = self.lookup_symbol(&symbol_id).cloned() {
            self.instantiate(&scheme)
        } else {
            self.placeholder(id, name, &symbol_id)
        }
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

    pub fn register_struct(&mut self, def: StructDef) {
        self.types.insert(def.symbol_id, TypeDef::Struct(def));
    }

    pub fn lookup_symbol(&self, symbol_id: &SymbolID) -> Result<&Scheme, TypeError> {
        if let Some(scheme) = self
            .scopes
            .iter()
            .rev()
            .find_map(|frame| frame.get(symbol_id))
        {
            Ok(scheme)
        } else {
            Err(TypeError::Unresolved(format!(
                "Did not find symbol {:?} in scope: {:?}",
                symbol_id, self.scopes
            )))
        }
    }

    pub fn lookup_type(&self, name: &SymbolID) -> Option<&TypeDef> {
        self.types.get(name)
    }

    pub fn is_struct_symbol(&self, symbol_id: &SymbolID) -> bool {
        match self.lookup_type(symbol_id) {
            Some(TypeDef::Struct(_)) => true,
            _ => false,
        }
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
        Ty::Func(params, ret, generics) => {
            for param in params {
                s.extend(free_type_vars(param));
            }

            for generic in generics {
                s.extend(free_type_vars(generic));
            }

            s.extend(free_type_vars(ret));
        }
        Ty::Closure { func, .. } => s.extend(free_type_vars(func)),
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
