//! Row-based type definitions using the qualified types approach.
//!
//! Instead of storing members directly, types have an associated row type variable
//! with constraints that specify their members.

use crate::{
    SymbolID,
    conformance::Conformance,
    environment::{Environment, TypeParameter},
    expr_id::ExprID,
    row::{FieldMetadata, RowConstraint},
    ty::Ty,
    type_var_id::{TypeVarID, TypeVarKind},
};

/// A type definition using row-based qualified types
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RowTypeDef {
    pub symbol_id: SymbolID,
    pub name_str: String,
    pub kind: TypeDefKind,
    pub type_parameters: Vec<TypeParameter>,
    /// The row type variable representing this type's members
    pub row_var: TypeVarID,
    /// Conformances to protocols
    pub conformances: Vec<Conformance>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDefKind {
    Struct,
    Protocol,
    Enum,
    Builtin(Ty),
}

impl RowTypeDef {
    /// Create a new type definition with an associated row variable
    pub fn new(
        symbol_id: SymbolID,
        name: String,
        kind: TypeDefKind,
        type_parameters: Vec<TypeParameter>,
        env: &mut Environment,
        expr_id: ExprID,
    ) -> Self {
        // Create a row type variable for this type's members
        let row_var = env.new_type_variable(
            TypeVarKind::CanonicalTypeParameter(format!("{name}_row")),
            expr_id,
        );

        Self {
            symbol_id,
            name_str: name,
            kind,
            type_parameters,
            row_var,
            conformances: Vec::new(),
        }
    }

    /// Add a property to this type by adding a HasField constraint
    #[allow(clippy::too_many_arguments)]
    pub fn add_property(
        &self,
        env: &mut Environment,
        name: String,
        ty: Ty,
        index: usize,
        has_default: bool,
        is_mutable: bool,
        expr_id: ExprID,
    ) {
        let constraint = RowConstraint::HasField {
            type_var: self.row_var.clone(),
            label: name,
            field_ty: ty,
            metadata: FieldMetadata::RecordField {
                index,
                has_default,
                is_mutable,
            },
        };

        env.constrain(crate::constraint::Constraint::Row {
            expr_id,
            constraint,
        });
    }

    /// Add a method to this type
    pub fn add_method(&self, env: &mut Environment, name: String, ty: Ty, expr_id: ExprID) {
        let constraint = RowConstraint::HasField {
            type_var: self.row_var.clone(),
            label: name,
            field_ty: ty,
            metadata: FieldMetadata::Method,
        };

        env.constrain(crate::constraint::Constraint::Row {
            expr_id,
            constraint,
        });
    }

    /// Add a method requirement (for protocols)
    pub fn add_method_requirement(
        &self,
        env: &mut Environment,
        name: String,
        ty: Ty,
        expr_id: ExprID,
    ) {
        let constraint = RowConstraint::HasField {
            type_var: self.row_var.clone(),
            label: name,
            field_ty: ty,
            metadata: FieldMetadata::MethodRequirement,
        };

        env.constrain(crate::constraint::Constraint::Row {
            expr_id,
            constraint,
        });
    }

    /// Add an initializer
    pub fn add_initializer(&self, env: &mut Environment, name: String, ty: Ty, expr_id: ExprID) {
        let constraint = RowConstraint::HasField {
            type_var: self.row_var.clone(),
            label: name,
            field_ty: ty,
            metadata: FieldMetadata::Initializer,
        };

        env.constrain(crate::constraint::Constraint::Row {
            expr_id,
            constraint,
        });
    }

    /// Add an enum variant
    pub fn add_variant(
        &self,
        env: &mut Environment,
        name: String,
        ty: Ty,
        tag: usize,
        expr_id: ExprID,
    ) {
        let constraint = RowConstraint::HasField {
            type_var: self.row_var.clone(),
            label: name,
            field_ty: ty,
            metadata: FieldMetadata::EnumVariant { tag },
        };

        env.constrain(crate::constraint::Constraint::Row {
            expr_id,
            constraint,
        });
    }

    /// Get the type for this definition
    pub fn ty(&self) -> Ty {
        match &self.kind {
            TypeDefKind::Enum => Ty::enum_type(
                self.symbol_id,
                self.name_str.to_string(),
                self.canonical_type_parameters(),
            ),
            TypeDefKind::Struct => {
                // For now, keep using Struct for RowTypeDef
                // TODO: Extract fields from row constraints
                Ty::struct_type(
                    self.symbol_id,
                    self.name_str.to_string(),
                    self.canonical_type_parameters(),
                )
            }
            TypeDefKind::Protocol => {
                // Use the protocol_type helper
                Ty::protocol_type(
                    self.symbol_id,
                    self.name_str.to_string(),
                    self.canonical_type_parameters(),
                )
            }
            TypeDefKind::Builtin(ty) => ty.clone(),
        }
    }

    pub fn canonical_type_parameters(&self) -> Vec<Ty> {
        self.type_parameters
            .iter()
            .map(|p| Ty::TypeVar(p.type_var.clone()))
            .collect()
    }
}

/// Builder for creating row-based type definitions
pub struct RowTypeDefBuilder<'a> {
    type_def: RowTypeDef,
    env: &'a mut Environment,
}

impl<'a> RowTypeDefBuilder<'a> {
    pub fn new(
        symbol_id: SymbolID,
        name: String,
        kind: TypeDefKind,
        type_parameters: Vec<TypeParameter>,
        env: &'a mut Environment,
        expr_id: ExprID,
    ) -> Self {
        let type_def = RowTypeDef::new(symbol_id, name, kind, type_parameters, env, expr_id);
        Self { type_def, env }
    }

    pub fn with_property(
        self,
        name: String,
        ty: Ty,
        index: usize,
        has_default: bool,
        is_mutable: bool,
        expr_id: ExprID,
    ) -> Self {
        self.type_def
            .add_property(self.env, name, ty, index, has_default, is_mutable, expr_id);
        self
    }

    pub fn with_method(self, name: String, ty: Ty, expr_id: ExprID) -> Self {
        self.type_def.add_method(self.env, name, ty, expr_id);
        self
    }

    pub fn with_conformance(mut self, conformance: Conformance) -> Self {
        self.type_def.conformances.push(conformance);
        self
    }

    pub fn build(self) -> RowTypeDef {
        self.type_def
    }
}
