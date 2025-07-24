use std::collections::HashMap;

use crate::{
    SymbolID,
    conformance::Conformance,
    constraint_solver::ConstraintSolver,
    environment::{Environment, TypeParameter},
    expr_id::ExprID,
    substitutions::Substitutions,
    ty::Ty,
    type_checker::Scheme,
    type_var_id::TypeVarID,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Property {
    pub index: usize,
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
    pub has_default: bool,
}

impl Property {
    pub fn new(index: usize, name: String, expr_id: ExprID, ty: Ty, has_default: bool) -> Self {
        Self {
            index,
            name,
            expr_id,
            ty,
            has_default,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Initializer {
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
}

impl Method {
    pub fn new(name: String, expr_id: ExprID, ty: Ty) -> Self {
        Self { name, expr_id, ty }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariant {
    pub tag: usize,
    pub name: String,
    pub ty: Ty,
}

pub type TypeParams = Vec<TypeParameter>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeMember {
    Method(Method),
    MethodRequirement(Method),
    Property(Property),
    Initializer(Initializer),
    Variant(EnumVariant),
}

impl TypeMember {
    pub fn ty(&self) -> &Ty {
        match self {
            TypeMember::Method(method) => &method.ty,
            TypeMember::MethodRequirement(method) => &method.ty,
            TypeMember::Property(property) => &property.ty,
            TypeMember::Initializer(initializer) => &initializer.ty,
            TypeMember::Variant(variant) => &variant.ty,
        }
    }

    pub fn replace(&mut self, substitutions: &Substitutions) {
        match self {
            TypeMember::Method(method) => {
                method.ty = ConstraintSolver::substitute_ty_with_map(&method.ty, substitutions);
            }
            TypeMember::MethodRequirement(method) => {
                method.ty = ConstraintSolver::substitute_ty_with_map(&method.ty, substitutions);
            }
            TypeMember::Property(property) => {
                property.ty = ConstraintSolver::substitute_ty_with_map(&property.ty, substitutions);
            }
            TypeMember::Initializer(initializer) => {
                initializer.ty =
                    ConstraintSolver::substitute_ty_with_map(&initializer.ty, substitutions);
            }
            TypeMember::Variant(variant) => {
                variant.ty = ConstraintSolver::substitute_ty_with_map(&variant.ty, substitutions);
            }
        };
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDefKind {
    Struct,
    Protocol,
    Enum,
    // Builtins can actually be structs/protocols/enums but we want to keep
    // them handled separately since their actual definitions are builtin.
    Builtin(Ty),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDef {
    pub symbol_id: SymbolID,
    pub name_str: String,
    pub kind: TypeDefKind,
    pub type_parameters: TypeParams,
    pub members: HashMap<String, TypeMember>,
    pub conformances: Vec<Conformance>,
}

impl TypeDef {
    pub fn ty(&self) -> Ty {
        match &self.kind {
            TypeDefKind::Enum => Ty::Enum(self.symbol_id, self.canonical_type_parameters()),
            TypeDefKind::Struct => Ty::Struct(self.symbol_id, self.canonical_type_parameters()),
            TypeDefKind::Protocol => Ty::Protocol(self.symbol_id, self.canonical_type_parameters()),
            TypeDefKind::Builtin(ty) => ty.clone(),
        }
    }

    pub fn conforms_to(&self, protocol_id: &SymbolID) -> bool {
        for conformance in self.conformances.iter() {
            if &conformance.protocol_id == protocol_id {
                return true;
            }
        }

        false
    }

    pub fn canonical_type_variables(&self) -> Vec<TypeVarID> {
        self.type_parameters
            .iter()
            .map(|p| p.type_var.clone())
            .collect()
    }

    pub fn canonical_type_parameters(&self) -> Vec<Ty> {
        self.type_parameters
            .iter()
            .map(|p| Ty::TypeVar(p.type_var.clone()))
            .collect()
    }

    pub fn init_fn_name(&self) -> String {
        format!("@_{}_{}_init", self.symbol_id().0, self.name())
    }

    pub fn method_fn_name(&self, name: &str) -> String {
        format!("@_{}_{}_{name}", self.symbol_id().0, self.name())
    }

    pub fn instantiate(&self, env: &mut Environment) -> Ty {
        let scheme = Scheme::new(
            self.ty(),
            self.type_parameters()
                .iter()
                .map(|p| p.type_var.clone())
                .collect(),
            vec![],
        );

        env.instantiate(&scheme)
    }

    pub fn member_ty_with_conformances(&self, name: &str, env: &mut Environment) -> Option<Ty> {
        if let Some(member) = self.members.get(name) {
            return Some(member.ty().clone());
        }

        for conformance in self.conformances() {
            let Some(protocol_def) = env.lookup_protocol(&conformance.protocol_id) else {
                continue;
            };

            let Some(ty) = protocol_def.member_ty(name) else {
                continue;
            };

            let mut substitutions = Substitutions::new();
            for (param, arg) in protocol_def
                .type_parameters
                .iter()
                .zip(&conformance.associated_types)
            {
                substitutions.insert(param.type_var.clone(), arg.clone());
            }

            return Some(ConstraintSolver::substitute_ty_with_map(ty, &substitutions));
        }

        None
    }

    pub fn member_ty(&self, name: &str) -> Option<&Ty> {
        self.members.get(name).map(|t| t.ty())
    }

    pub fn symbol_id(&self) -> SymbolID {
        self.symbol_id
    }

    pub fn name(&self) -> &str {
        &self.name_str
    }

    pub fn conformances(&self) -> &[Conformance] {
        &self.conformances
    }

    pub fn type_parameters(&self) -> TypeParams {
        self.type_parameters.clone()
    }

    pub fn initializers(&self) -> Vec<Initializer> {
        self.members
            .values()
            .filter_map(|member| {
                if let TypeMember::Initializer(initializer) = member {
                    Some(initializer.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn find_method_requirement(&self, name: &str) -> Option<&Method> {
        if let Some(TypeMember::MethodRequirement(method)) = self.members.get(name) {
            return Some(method);
        }

        None
    }

    pub fn find_variant(&self, name: &str) -> Option<&EnumVariant> {
        if let Some(TypeMember::Variant(variant)) = self.members.get(name) {
            return Some(variant);
        }

        None
    }

    pub fn find_method(&self, method_name: &str) -> Option<&Method> {
        if let Some(TypeMember::Method(method)) = self.members.get(method_name) {
            return Some(method);
        }

        None
    }

    pub fn find_property(&self, name: &str) -> Option<&Property> {
        if let Some(TypeMember::Property(property)) = self.members.get(name) {
            return Some(property);
        }

        None
    }

    pub fn properties(&self) -> Vec<Property> {
        self.members
            .values()
            .filter_map(|member| {
                if let TypeMember::Property(property) = member {
                    Some(property.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn add_methods(&mut self, methods: Vec<Method>) {
        for method in methods {
            self.members
                .insert(method.name.clone(), TypeMember::Method(method));
        }
    }

    pub fn methods(&self) -> Vec<Method> {
        self.members
            .values()
            .filter_map(|member| {
                if let TypeMember::Method(method) = member {
                    Some(method.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn method_requirements(&self) -> Vec<Method> {
        self.members
            .values()
            .filter_map(|member| {
                if let TypeMember::MethodRequirement(method) = member {
                    Some(method.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn add_type_parameters(&mut self, params: Vec<TypeParameter>) {
        self.type_parameters.extend(params);
    }

    pub fn add_method_requirements(&mut self, methods: Vec<Method>) {
        if methods.is_empty() {
            return;
        }

        for method in methods {
            self.members
                .insert(method.name.clone(), TypeMember::MethodRequirement(method));
        }
    }

    pub fn add_initializers(&mut self, initializers: Vec<Initializer>) {
        if initializers.is_empty() {
            return;
        }

        for initializer in initializers {
            self.members.insert(
                initializer.name.clone(),
                TypeMember::Initializer(initializer),
            );
        }
    }

    pub fn add_properties(&mut self, properties: Vec<Property>) {
        if properties.is_empty() {
            return;
        }

        for property in properties {
            self.members
                .insert(property.name.clone(), TypeMember::Property(property));
        }
    }

    pub fn add_variants(&mut self, variants: Vec<EnumVariant>) {
        if variants.is_empty() {
            return;
        }

        for variants in variants {
            self.members
                .insert(variants.name.clone(), TypeMember::Variant(variants));
        }
    }

    pub fn variants(&self) -> Vec<EnumVariant> {
        self.members
            .values()
            .filter_map(|member| {
                if let TypeMember::Variant(variant) = member {
                    Some(variant.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn add_conformances(&mut self, conformances: Vec<Conformance>) {
        self.conformances.extend(conformances);
    }
}
