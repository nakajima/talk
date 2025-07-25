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
    type_var_id::{TypeVarID, TypeVarKind},
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
    /// Row variable for this type's members (for row-based type system)
    pub row_var: Option<TypeVarID>,
}

// Architecture Note:
// During type checking, type structure is represented as row constraints on type variables.
// The `members` HashMap is populated from these constraints after solving via `populate_from_rows`.
// This ensures row constraints are the single source of truth during type checking,
// while providing efficient lookup for post-type-checking phases (lowering, LSP, etc.).

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
        // Check the members HashMap (populated from rows after constraint solving)
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

    /// Legacy method - prefer add_methods_with_rows
    #[deprecated(note = "Use add_methods_with_rows instead")]
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

    /// Legacy method - prefer add_initializers_with_rows
    #[deprecated(note = "Use add_initializers_with_rows instead")]
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

    /// Legacy method - prefer add_properties_with_rows
    #[deprecated(note = "Use add_properties_with_rows instead")]
    pub fn add_properties(&mut self, properties: Vec<Property>) {
        if properties.is_empty() {
            return;
        }

        for property in properties {
            self.members
                .insert(property.name.clone(), TypeMember::Property(property));
        }
    }

    /// Legacy method - prefer add_variants_with_rows
    #[deprecated(note = "Use add_variants_with_rows instead")]
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
    
    /// Ensure this TypeDef has a row variable, creating one if needed
    pub fn ensure_row_var(&mut self, env: &mut Environment) -> TypeVarID {
        if let Some(row_var) = &self.row_var {
            row_var.clone()
        } else {
            // Create a row variable for this type
            let row_var = env.new_type_variable(
                TypeVarKind::CanonicalTypeParameter(format!("{}_row", self.name_str)),
                ExprID(0), // TODO: better expr_id
            );
            self.row_var = Some(row_var.clone());
            row_var
        }
    }
    
    /// Add properties with row constraint support
    pub fn add_properties_with_rows(
        &mut self, 
        properties: Vec<Property>,
        env: &mut Environment,
    ) {
        if properties.is_empty() {
            return;
        }
        
        // Only add row constraints - no HashMap update
        let row_var = self.ensure_row_var(env);
        
        use crate::constraint::Constraint;
        use crate::row::{RowConstraint, FieldMetadata};
        
        for property in properties {
            env.constrain(Constraint::Row {
                expr_id: property.expr_id,
                constraint: RowConstraint::HasField {
                    type_var: row_var.clone(),
                    label: property.name,
                    field_ty: property.ty,
                    metadata: FieldMetadata::RecordField {
                        index: property.index,
                        has_default: property.has_default,
                        is_mutable: false, // TODO: get from property
                    },
                },
            });
        }
    }
    
    /// Add methods with row constraint support
    pub fn add_methods_with_rows(
        &mut self,
        methods: Vec<Method>,
        env: &mut Environment,
    ) {
        if methods.is_empty() {
            return;
        }
        
        // Only add row constraints - no HashMap update
        let row_var = self.ensure_row_var(env);
        
        use crate::constraint::Constraint;
        use crate::row::{RowConstraint, FieldMetadata};
        
        for method in methods {
            env.constrain(Constraint::Row {
                expr_id: method.expr_id,
                constraint: RowConstraint::HasField {
                    type_var: row_var.clone(),
                    label: method.name,
                    field_ty: method.ty,
                    metadata: FieldMetadata::Method,
                },
            });
        }
    }
    
    /// Add initializers with row constraint support
    pub fn add_initializers_with_rows(
        &mut self,
        initializers: Vec<Initializer>,
        env: &mut Environment,
    ) {
        if initializers.is_empty() {
            return;
        }
        
        // Only add row constraints - no HashMap update
        let row_var = self.ensure_row_var(env);
        
        use crate::constraint::Constraint;
        use crate::row::{RowConstraint, FieldMetadata};
        
        for initializer in initializers {
            env.constrain(Constraint::Row {
                expr_id: initializer.expr_id,
                constraint: RowConstraint::HasField {
                    type_var: row_var.clone(),
                    label: initializer.name,
                    field_ty: initializer.ty,
                    metadata: FieldMetadata::Initializer,
                },
            });
        }
    }
    
    /// Add variants with row constraint support
    pub fn add_variants_with_rows(
        &mut self,
        variants: Vec<EnumVariant>,
        env: &mut Environment,
    ) {
        if variants.is_empty() {
            return;
        }
        
        // Only add row constraints - no HashMap update
        let row_var = self.ensure_row_var(env);
        
        use crate::constraint::Constraint;
        use crate::row::{RowConstraint, FieldMetadata};
        
        for variant in variants {
            env.constrain(Constraint::Row {
                expr_id: ExprID(0), // TODO: variants don't have expr_id
                constraint: RowConstraint::HasField {
                    type_var: row_var.clone(),
                    label: variant.name,
                    field_ty: variant.ty,
                    metadata: FieldMetadata::EnumVariant {
                        tag: variant.tag,
                    },
                },
            });
        }
    }
    
    /// Populate the members HashMap from row constraints after constraint solving
    pub fn populate_from_rows(&mut self, env: &Environment) {
        let Some(ref row_var) = self.row_var else {
            return;
        };
        
        // Clear existing members
        self.members.clear();
        
        // Collect all fields from row constraints
        for constraint in env.constraints() {
            if let crate::constraint::Constraint::Row { constraint: row_constraint, expr_id } = constraint {
                use crate::row::{RowConstraint, FieldMetadata};
                match &row_constraint {
                    RowConstraint::HasField { type_var, label, field_ty, metadata } 
                        if type_var == row_var => {
                        match metadata {
                            FieldMetadata::RecordField { index, has_default, .. } => {
                                self.members.insert(
                                    label.clone(),
                                    TypeMember::Property(Property {
                                        index: *index,
                                        name: label.clone(),
                                        expr_id,
                                        ty: field_ty.clone(),
                                        has_default: *has_default,
                                    }),
                                );
                            }
                            FieldMetadata::Method => {
                                self.members.insert(
                                    label.clone(),
                                    TypeMember::Method(Method {
                                        name: label.clone(),
                                        expr_id,
                                        ty: field_ty.clone(),
                                    }),
                                );
                            }
                            FieldMetadata::MethodRequirement => {
                                self.members.insert(
                                    label.clone(),
                                    TypeMember::MethodRequirement(Method {
                                        name: label.clone(),
                                        expr_id,
                                        ty: field_ty.clone(),
                                    }),
                                );
                            }
                            FieldMetadata::Initializer => {
                                self.members.insert(
                                    label.clone(),
                                    TypeMember::Initializer(Initializer {
                                        name: label.clone(),
                                        expr_id,
                                        ty: field_ty.clone(),
                                    }),
                                );
                            }
                            FieldMetadata::EnumVariant { tag } => {
                                self.members.insert(
                                    label.clone(),
                                    TypeMember::Variant(EnumVariant {
                                        tag: *tag,
                                        name: label.clone(),
                                        ty: field_ty.clone(),
                                    }),
                                );
                            }
                            FieldMetadata::VariantField { .. } => {
                                // Skip variant fields - they're not type members
                            }
                        }
                    }
                    RowConstraint::HasRow { type_var, row, .. } | 
                    RowConstraint::HasExactRow { type_var, row } 
                        if type_var == row_var => {
                        for (label, field) in &row.fields {
                            match &field.metadata {
                                FieldMetadata::RecordField { index, has_default, .. } => {
                                    self.members.insert(
                                        label.clone(),
                                        TypeMember::Property(Property {
                                            index: *index,
                                            name: label.clone(),
                                            expr_id,
                                            ty: field.ty.clone(),
                                            has_default: *has_default,
                                        }),
                                    );
                                }
                                FieldMetadata::Method => {
                                    self.members.insert(
                                        label.clone(),
                                        TypeMember::Method(Method {
                                            name: label.clone(),
                                            expr_id,
                                            ty: field.ty.clone(),
                                        }),
                                    );
                                }
                                FieldMetadata::MethodRequirement => {
                                    self.members.insert(
                                        label.clone(),
                                        TypeMember::MethodRequirement(Method {
                                            name: label.clone(),
                                            expr_id,
                                            ty: field.ty.clone(),
                                        }),
                                    );
                                }
                                FieldMetadata::Initializer => {
                                    self.members.insert(
                                        label.clone(),
                                        TypeMember::Initializer(Initializer {
                                            name: label.clone(),
                                            expr_id,
                                            ty: field.ty.clone(),
                                        }),
                                    );
                                }
                                FieldMetadata::EnumVariant { tag } => {
                                    self.members.insert(
                                        label.clone(),
                                        TypeMember::Variant(EnumVariant {
                                            tag: *tag,
                                            name: label.clone(),
                                            ty: field.ty.clone(),
                                        }),
                                    );
                                }
                                FieldMetadata::VariantField { .. } => {
                                    // Skip variant fields - they're not type members
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}
