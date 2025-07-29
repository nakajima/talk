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
    pub symbol_id: Option<SymbolID>,
}

impl Property {
    pub fn new(index: usize, name: String, expr_id: ExprID, ty: Ty, has_default: bool) -> Self {
        Self {
            index,
            name,
            expr_id,
            ty,
            has_default,
            symbol_id: None,
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
    pub symbol_id: Option<SymbolID>,
}

impl Method {
    pub fn new(name: String, expr_id: ExprID, ty: Ty) -> Self {
        Self {
            name,
            expr_id,
            ty,
            symbol_id: None,
        }
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
    /// Tracks which members were populated from row constraints
    /// This allows populate_from_rows to correctly update only row-managed members
    row_managed_members: std::collections::HashSet<String>,
}

// Architecture Note:
// During type checking, type structure is represented as row constraints on type variables.
// The `members` HashMap is populated from these constraints after solving via `populate_from_rows`.
// This ensures row constraints are the single source of truth during type checking,
// while providing efficient lookup for post-type-checking phases (lowering, LSP, etc.).

impl TypeDef {
    /// Create a new TypeDef with all fields initialized
    pub fn new(
        symbol_id: SymbolID,
        name_str: String,
        kind: TypeDefKind,
        type_parameters: TypeParams,
    ) -> Self {
        TypeDef {
            symbol_id,
            name_str,
            kind,
            type_parameters,
            members: HashMap::new(),
            conformances: Vec::new(),
            row_var: None,
            row_managed_members: std::collections::HashSet::new(),
        }
    }

    /// Merge row_managed_members from another TypeDef
    pub fn merge_row_managed_members(&mut self, other: &TypeDef) {
        let before = self.row_managed_members.len();
        self.row_managed_members
            .extend(other.row_managed_members.clone());
        let after = self.row_managed_members.len();
        if after > before {
            tracing::debug!(
                "Merged {} row-managed members into {} (now has {})",
                other.row_managed_members.len(),
                self.name_str,
                after
            );
        }
    }

    /// Clear row_managed_members (used when importing types)
    pub fn clear_row_managed_members(&mut self) {
        self.row_managed_members.clear();
    }

    pub fn ty(&self) -> Ty {
        match &self.kind {
            TypeDefKind::Enum => Ty::enum_type(self.symbol_id, self.canonical_type_parameters()),
            TypeDefKind::Struct => {
                // Use the struct_type helper
                Ty::struct_type(self.symbol_id, self.canonical_type_parameters())
            }
            TypeDefKind::Protocol => {
                // Use the protocol_type helper
                Ty::protocol_type(self.symbol_id, self.canonical_type_parameters())
            }
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
        // First check the members HashMap
        // This handles:
        // 1. Post-constraint-solving access (members populated from rows)
        // 2. Imported types from prelude/modules (have members pre-populated)
        // 3. Enum variants (populated in both HashMap and rows for immediate availability)
        if let Some(member) = self.members.get(name) {
            return Some(member.ty().clone());
        }

        // During type checking, also check row constraints for types being defined
        // This handles types currently being defined that use row constraints
        if let Some(row_var) = self.row_var.clone() {
            // Look through constraints to find HasField constraints for this row variable
            for constraint in env.constraints() {
                if let crate::constraint::Constraint::Row {
                    constraint: ref row_constraint,
                    ..
                } = constraint
                {
                    use crate::row::RowConstraint;
                    match row_constraint {
                        RowConstraint::HasField {
                            type_var,
                            label,
                            field_ty,
                            ..
                        } if type_var == &row_var && label == name => {
                            return Some(field_ty.clone());
                        }
                        _ => {}
                    }
                }
            }
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
    pub fn add_properties_with_rows(&mut self, properties: Vec<Property>, env: &mut Environment) {
        if properties.is_empty() {
            return;
        }

        // For types that will be exported (e.g., prelude types), we need to populate
        // the HashMap immediately so they're available across compilation units.
        for property in &properties {
            self.members.insert(
                property.name.clone(),
                TypeMember::Property(property.clone()),
            );
        }

        // Also add row constraints for row polymorphism within this compilation unit
        let row_var = self.ensure_row_var(env);

        use crate::constraint::Constraint;
        use crate::row::{FieldMetadata, RowConstraint};

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
    pub fn add_methods_with_rows(&mut self, methods: Vec<Method>, env: &mut Environment) {
        if methods.is_empty() {
            return;
        }

        // For types that will be exported (e.g., prelude types), we need to populate
        // the HashMap immediately so they're available across compilation units.
        // Row constraints are compilation-unit specific and won't be available
        // when the type is imported elsewhere.
        for method in &methods {
            self.members
                .insert(method.name.clone(), TypeMember::Method(method.clone()));
        }

        // Also add row constraints for row polymorphism within this compilation unit
        let row_var = self.ensure_row_var(env);

        use crate::constraint::Constraint;
        use crate::row::{FieldMetadata, RowConstraint};

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

        // For types that will be exported (e.g., prelude types), we need to populate
        // the HashMap immediately so they're available across compilation units.
        for initializer in &initializers {
            self.members.insert(
                initializer.name.clone(),
                TypeMember::Initializer(initializer.clone()),
            );
        }

        // Also add row constraints for row polymorphism within this compilation unit
        let row_var = self.ensure_row_var(env);

        use crate::constraint::Constraint;
        use crate::row::{FieldMetadata, RowConstraint};

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
    pub fn add_variants_with_rows(&mut self, variants: Vec<EnumVariant>, env: &mut Environment) {
        if variants.is_empty() {
            return;
        }

        // For enum variants, we need immediate availability during type checking
        // So we populate both the HashMap AND add row constraints
        for variant in &variants {
            self.members
                .insert(variant.name.clone(), TypeMember::Variant(variant.clone()));
        }

        // Also add row constraints for row polymorphism
        let row_var = self.ensure_row_var(env);

        use crate::constraint::Constraint;
        use crate::row::{FieldMetadata, RowConstraint};

        for variant in variants {
            env.constrain(Constraint::Row {
                expr_id: ExprID(0), // TODO: variants don't have expr_id
                constraint: RowConstraint::HasField {
                    type_var: row_var.clone(),
                    label: variant.name,
                    field_ty: variant.ty,
                    metadata: FieldMetadata::EnumVariant { tag: variant.tag },
                },
            });
        }
    }

    /// Populate the members HashMap from row constraints after constraint solving
    ///
    /// This method updates the members HashMap to reflect the current state of row constraints.
    /// It uses a targeted approach: only members that are defined by row constraints are
    /// removed and re-added. This preserves any members not managed by the row system,
    /// such as methods from imported types or manually added members.
    pub fn populate_from_rows(&mut self, env: &Environment) {
        let Some(row_var) = self.row_var.clone() else {
            return;
        };

        tracing::debug!(
            "populate_from_rows for {} (id={:?}) with row_var {:?}, has {} members, {} are row-managed",
            self.name_str,
            self.symbol_id,
            row_var,
            self.members.len(),
            self.row_managed_members.len()
        );

        // First, check if there are any row constraints for this type
        let mut has_row_constraints = false;
        for constraint in env.constraints() {
            if let crate::constraint::Constraint::Row {
                constraint: row_constraint,
                ..
            } = constraint
            {
                use crate::row::RowConstraint;
                match row_constraint {
                    RowConstraint::HasField { type_var, .. }
                    | RowConstraint::HasRow { type_var, .. }
                    | RowConstraint::HasExactRow { type_var, .. }
                        if type_var == row_var =>
                    {
                        has_row_constraints = true;
                        break;
                    }
                    _ => {}
                }
            }
        }

        // If we have NO row constraints, preserve existing members
        if !has_row_constraints {
            // If we have row-managed members but no constraints, this likely means
            // we're an imported type whose constraints were cleared after initial population.
            // Don't remove the members in this case.
            if !self.row_managed_members.is_empty() {
                tracing::trace!(
                    "Type {} has {} row-managed members but no constraints (likely imported), preserving members",
                    self.name_str,
                    self.row_managed_members.len()
                );
            } else {
                tracing::trace!(
                    "No row constraints for {} (has {} members), skipping populate_from_rows",
                    self.name_str,
                    self.members.len()
                );
            }
            return;
        }

        // Collect all member names that are defined by row constraints
        let mut row_defined_members = std::collections::HashSet::new();
        for constraint in env.constraints() {
            if let crate::constraint::Constraint::Row {
                constraint: row_constraint,
                ..
            } = constraint
            {
                use crate::row::RowConstraint;
                match &row_constraint {
                    RowConstraint::HasField {
                        type_var, label, ..
                    } if type_var == &row_var => {
                        row_defined_members.insert(label.clone());
                    }
                    RowConstraint::HasRow { type_var, row, .. }
                    | RowConstraint::HasExactRow { type_var, row }
                        if type_var == &row_var =>
                    {
                        for field_name in row.fields.keys() {
                            row_defined_members.insert(field_name.clone());
                        }
                    }
                    _ => {}
                }
            }
        }

        // Capture existing members to preserve symbol_ids
        let existing_members: HashMap<String, TypeMember> = self.members.clone();

        // Only remove members that are being redefined (exist in both old and new)
        let members_before = self.members.len();
        self.members.retain(|name, _| {
            !self.row_managed_members.contains(name) || !row_defined_members.contains(name)
        });
        let removed_old = members_before - self.members.len();

        // Update row_managed_members to include all current row-defined members
        self.row_managed_members = row_defined_members.clone();

        tracing::debug!(
            "Type {}: removed {} old row members, will add {} new row members, preserving {} imported row members",
            self.name_str,
            removed_old,
            row_defined_members.len(),
            self.row_managed_members.len() - row_defined_members.len()
        );

        // Collect all fields from row constraints
        for constraint in env.constraints() {
            if let crate::constraint::Constraint::Row {
                constraint: row_constraint,
                expr_id,
            } = constraint
            {
                use crate::row::{FieldMetadata, RowConstraint};
                match &row_constraint {
                    RowConstraint::HasField {
                        type_var,
                        label,
                        field_ty,
                        metadata,
                    } if type_var == &row_var => {
                        match metadata {
                            FieldMetadata::RecordField {
                                index, has_default, ..
                            } => {
                                tracing::debug!(
                                    "Adding property {} to type {}",
                                    label,
                                    self.name_str
                                );
                                // Check if we already have this property and preserve its symbol_id
                                let existing_symbol_id =
                                    existing_members.get(label).and_then(|member| match member {
                                        TypeMember::Property(prop) => prop.symbol_id,
                                        _ => None,
                                    });

                                self.members.insert(
                                    label.clone(),
                                    TypeMember::Property(Property {
                                        index: *index,
                                        name: label.clone(),
                                        expr_id,
                                        ty: field_ty.clone(),
                                        has_default: *has_default,
                                        symbol_id: existing_symbol_id,
                                    }),
                                );
                            }
                            FieldMetadata::Method => {
                                // Check if we already have this method and preserve its symbol_id
                                let existing_symbol_id =
                                    existing_members.get(label).and_then(|member| match member {
                                        TypeMember::Method(method) => method.symbol_id,
                                        _ => None,
                                    });

                                self.members.insert(
                                    label.clone(),
                                    TypeMember::Method(Method {
                                        name: label.clone(),
                                        expr_id,
                                        ty: field_ty.clone(),
                                        symbol_id: existing_symbol_id,
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
                                        symbol_id: None,
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
                            FieldMetadata::EnumCase { tag } => {
                                self.members.insert(
                                    label.clone(),
                                    TypeMember::Variant(EnumVariant {
                                        tag: *tag,
                                        name: label.clone(),
                                        ty: field_ty.clone(),
                                    }),
                                );
                            }
                        }
                    }
                    RowConstraint::HasRow { type_var, row, .. }
                    | RowConstraint::HasExactRow { type_var, row }
                        if type_var == &row_var =>
                    {
                        for (label, field) in &row.fields {
                            match &field.metadata {
                                FieldMetadata::RecordField {
                                    index, has_default, ..
                                } => {
                                    // Check if we already have this property and preserve its symbol_id
                                    let existing_symbol_id = existing_members.get(label).and_then(
                                        |member| match member {
                                            TypeMember::Property(prop) => prop.symbol_id,
                                            _ => None,
                                        },
                                    );

                                    self.members.insert(
                                        label.clone(),
                                        TypeMember::Property(Property {
                                            index: *index,
                                            name: label.clone(),
                                            expr_id,
                                            ty: field.ty.clone(),
                                            has_default: *has_default,
                                            symbol_id: existing_symbol_id,
                                        }),
                                    );
                                }
                                FieldMetadata::Method => {
                                    // Check if we already have this method and preserve its symbol_id
                                    let existing_symbol_id = existing_members.get(label).and_then(
                                        |member| match member {
                                            TypeMember::Method(method) => method.symbol_id,
                                            _ => None,
                                        },
                                    );

                                    self.members.insert(
                                        label.clone(),
                                        TypeMember::Method(Method {
                                            name: label.clone(),
                                            expr_id,
                                            ty: field.ty.clone(),
                                            symbol_id: existing_symbol_id,
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
                                            symbol_id: None,
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
                                FieldMetadata::EnumCase { tag } => {
                                    self.members.insert(
                                        label.clone(),
                                        TypeMember::Variant(EnumVariant {
                                            tag: *tag,
                                            name: label.clone(),
                                            ty: field.ty.clone(),
                                        }),
                                    );
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
