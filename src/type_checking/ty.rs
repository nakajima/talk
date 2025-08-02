use std::{collections::BTreeMap, fmt::Display};

use derive_visitor::Drive;

use crate::{
    SymbolID, impl_option_eq,
    row::{FieldInfo, RowConstraint},
    type_checker::{FuncParams, FuncReturning},
    type_var_id::{TypeVarID, TypeVarKind},
};

/// The kind of row type - struct, protocol, or record
#[derive(Clone, PartialEq, Debug, Drive)]
pub enum RowKind {
    /// A struct - concrete type with storage
    #[drive(skip)]
    Struct(SymbolID, String),
    /// A protocol - interface/trait type without storage
    #[drive(skip)]
    Protocol(SymbolID, String),
    /// A record - structural type (anonymous)
    #[drive(skip)]
    Record,
    /// An enum - sum type with variants
    #[drive(skip)]
    Enum(SymbolID, String),
}

impl_option_eq!(Ty);

#[derive(Clone, PartialEq, Debug, Drive)]
pub enum Primitive {
    Void,
    Int,
    Float,
    Bool,
    Byte,
    Pointer,
}

#[derive(Clone, PartialEq, Debug, Drive)]
pub enum Ty {
    Primitive(Primitive),
    Init(#[drive(skip)] SymbolID, Vec<Ty> /* params */),
    Method {
        self_ty: Box<Ty>,
        func: Box<Ty>,
    },
    Func(
        FuncParams,    /* params */
        FuncReturning, /* returning */
        Vec<Ty>,       /* generics */
    ),
    Closure {
        func: Box<Ty>, // the func
        #[drive(skip)]
        captures: Vec<SymbolID>,
    },
    TypeVar(#[drive(skip)] TypeVarID),
    Tuple(Vec<Ty>),
    Array(Box<Ty>),
    SelfType,
    // Unified row type that can represent structs, protocols, and records
    Row {
        #[drive(skip)]
        type_var: TypeVarID, // Type variable for this row
        #[drive(skip)]
        constraints: Vec<RowConstraint>, // Constraints defining the row structure
        generics: Vec<Ty>, // Generic type arguments (for nominal types)
        #[drive(skip)]
        kind: RowKind, // Distinguishes between struct/protocol/record
    },
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Primitive(primitive) => write!(f, "{primitive:?}"),
            Ty::SelfType => write!(f, "Self"),
            Ty::Init(_, params) => write!(
                f,
                "init({})",
                params
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty::Method {
                func: box Ty::Func(params, _, _),
                ..
            } => write!(
                f,
                "method({})",
                params
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty::Func(params, ty, _) => write!(
                f,
                "func({}) -> {ty}",
                params
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty::Closure { func, .. } => write!(f, "{func}"),
            Ty::TypeVar(type_var_id) => write!(f, "{type_var_id:?}"),
            Ty::Tuple(items) => write!(
                f,
                "({})",
                items
                    .iter()
                    .map(|i| format!("{i}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty::Array(ty) => write!(f, "Array<{ty}>"),
            Ty::Row {
                constraints,
                generics: _,
                kind,
                ..
            } => {
                if let RowKind::Struct(_, name)
                | RowKind::Protocol(_, name)
                | RowKind::Enum(_, name) = kind
                {
                    write!(f, "{}", name)
                } else {
                    // Structural type - display fields from constraints
                    let fields = self.get_row_fields();
                    if fields.is_empty() {
                        write!(f, "{{}}")
                    } else {
                        let field_strs: Vec<String> = fields
                            .iter()
                            .map(|(name, info)| format!("{}: {:?}", name, info.ty))
                            .collect();
                        write!(f, "{{ {} }}", field_strs.join(", "))
                    }
                }
            }
            _ => write!(f, "{self:?}"),
        }
    }
}

impl std::hash::Hash for Ty {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        format!("{self:?}").hash(state);
    }
}

impl Eq for Ty {}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
    pub const Byte: Ty = Ty::Primitive(Primitive::Byte);
    pub const Pointer: Ty = Ty::Primitive(Primitive::Pointer);
    pub const Void: Ty = Ty::Primitive(Primitive::Void);

    /// Check if this type is a protocol
    pub fn is_protocol(&self) -> bool {
        matches!(
            self,
            Ty::Row {
                kind: RowKind::Protocol(_, _),
                ..
            }
        )
    }

    pub fn string() -> Ty {
        // String is a builtin struct type
        Ty::Row {
            type_var: TypeVarID::new(0, TypeVarKind::Blank, crate::expr_id::ExprID(0)),
            constraints: vec![],
            generics: vec![],
            kind: RowKind::Struct(SymbolID::STRING, "String".into()),
        }
    }

    /// Create a struct type using Row representation
    pub fn struct_type(symbol_id: SymbolID, name: String, generics: Vec<Ty>) -> Ty {
        // Create Row type for structs
        Ty::Row {
            type_var: TypeVarID::new(0, TypeVarKind::Blank, crate::expr_id::ExprID(0)),
            constraints: vec![],
            generics,
            kind: RowKind::Struct(symbol_id, name),
        }
    }

    /// Create a protocol type using Row representation
    pub fn protocol_type(symbol_id: SymbolID, name: String, generics: Vec<Ty>) -> Ty {
        Ty::Row {
            type_var: TypeVarID::new(0, TypeVarKind::Blank, crate::expr_id::ExprID(0)),
            constraints: vec![],
            generics,
            kind: RowKind::Protocol(symbol_id, name),
        }
    }

    /// Create an enum type using Row representation
    pub fn enum_type(symbol_id: SymbolID, name: String, generics: Vec<Ty>) -> Ty {
        Ty::Row {
            type_var: TypeVarID::new(0, TypeVarKind::Blank, crate::expr_id::ExprID(0)),
            constraints: vec![],
            generics,
            kind: RowKind::Enum(symbol_id, name),
        }
    }

    pub fn optional(&self) -> Ty {
        Ty::enum_type(SymbolID::OPTIONAL, "Optional".into(), vec![self.clone()])
    }

    pub fn is_concrete(&self) -> bool {
        !matches!(self, Ty::TypeVar(_))
    }

    /// Get fields from a Row type by examining its constraints
    pub fn get_row_fields(&self) -> std::collections::BTreeMap<String, crate::row::FieldInfo> {
        let mut fields = std::collections::BTreeMap::new();

        if let Ty::Row { constraints, .. } = self {
            for constraint in constraints {
                match constraint {
                    crate::row::RowConstraint::HasField {
                        label,
                        field_ty,
                        metadata,
                        ..
                    } => {
                        fields.insert(
                            label.clone(),
                            crate::row::FieldInfo {
                                ty: field_ty.clone(),
                                expr_id: crate::parsing::expr_id::ExprID(0), // TODO: proper expr_id
                                metadata: metadata.clone(),
                            },
                        );
                    }
                    crate::row::RowConstraint::HasRow { row, .. }
                    | crate::row::RowConstraint::HasExactRow { row, .. } => {
                        for (label, field_info) in &row.fields {
                            fields.insert(label.clone(), field_info.clone());
                        }
                    }
                    _ => {}
                }
            }
        }

        fields
    }

    /// Check if a Row type has a specific field
    pub fn has_row_field(&self, label: &str) -> bool {
        if let Ty::Row { constraints, .. } = self {
            for constraint in constraints {
                match constraint {
                    crate::row::RowConstraint::HasField {
                        label: field_label, ..
                    } if field_label == label => return true,
                    crate::row::RowConstraint::HasRow { row, .. }
                    | crate::row::RowConstraint::HasExactRow { row, .. } => {
                        if row.fields.contains_key(label) {
                            return true;
                        }
                    }
                    crate::row::RowConstraint::Lacks { labels, .. } => {
                        if labels.contains(label) {
                            return false;
                        }
                    }
                    _ => {}
                }
            }
        }
        false
    }

    /// Get the type of a specific field in a Row type
    pub fn get_row_field_type(&self, label: &str) -> Option<Ty> {
        if let Ty::Row { constraints, .. } = self {
            for constraint in constraints {
                match constraint {
                    crate::row::RowConstraint::HasField {
                        label: field_label,
                        field_ty,
                        ..
                    } if field_label == label => return Some(field_ty.clone()),
                    crate::row::RowConstraint::HasRow { row, .. }
                    | crate::row::RowConstraint::HasExactRow { row, .. } => {
                        if let Some(field_info) = row.fields.get(label) {
                            return Some(field_info.ty.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        None
    }

    pub fn satisfies(&self, other: &Ty) -> bool {
        match (self, other) {
            (
                Ty::Row {
                    type_var: lhs_var,
                    constraints: lhs_constraints,
                    generics: lhs_generics,
                    kind: lhs_kind,
                },
                Ty::Row {
                    type_var: rhs_var,
                    constraints: rhs_constraints,
                    generics: rhs_generics,
                    kind: rhs_kind,
                },
            ) => {
                // Check basic structural equality
                if lhs_kind != rhs_kind || lhs_generics.len() != rhs_generics.len() {
                    return false;
                }

                // Check generics
                if !lhs_generics
                    .iter()
                    .enumerate()
                    .all(|(i, g)| g.satisfies(&rhs_generics[i]))
                {
                    return false;
                }

                // If same type var, they're equal
                if lhs_var == rhs_var {
                    return true;
                }

                // Otherwise check if lhs has all fields required by rhs
                let rhs_fields = other.get_row_fields();
                for (field_name, rhs_field) in rhs_fields {
                    if let Some(lhs_field_ty) = self.get_row_field_type(&field_name) {
                        if !lhs_field_ty.satisfies(&rhs_field.ty) {
                            return false;
                        }
                    } else {
                        return false; // lhs missing a required field
                    }
                }

                true
            }
            (_, _) => self == other,
        }
    }

    pub fn equal_to(&self, other: &Ty) -> bool {
        match (self, other) {
            (
                Ty::Row {
                    type_var: lhs_var,
                    constraints: lhs_constraints,
                    generics: lhs_generics,
                    kind: lhs_kind,
                },
                Ty::Row {
                    type_var: rhs_var,
                    constraints: rhs_constraints,
                    generics: rhs_generics,
                    kind: rhs_kind,
                },
            ) => {
                // Check basic equality
                if lhs_kind != rhs_kind || lhs_generics.len() != rhs_generics.len() {
                    return false;
                }

                if !lhs_generics
                    .iter()
                    .enumerate()
                    .all(|(i, g)| g.equal_to(&rhs_generics[i]))
                {
                    return false;
                }

                // If same type var, they're equal
                if lhs_var == rhs_var {
                    return true;
                }

                // Check exact field equality
                let lhs_fields = self.get_row_fields();
                let rhs_fields = other.get_row_fields();

                if lhs_fields.len() != rhs_fields.len() {
                    return false;
                }

                for (field_name, lhs_field) in &lhs_fields {
                    if let Some(rhs_field) = rhs_fields.get(field_name) {
                        if !lhs_field.ty.equal_to(&rhs_field.ty) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }

                true
            }
            (_, _) => self == other,
        }
    }

    pub fn replace<F: Fn(&Ty) -> bool>(&self, replacement: Ty, f: &F) -> Ty {
        match &self {
            Ty::Init(sym, items) => {
                if f(self) {
                    replacement
                } else {
                    Ty::Init(
                        *sym,
                        items
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                    )
                }
            }
            Ty::Func(items, ty, items1) => {
                if f(self) {
                    replacement
                } else {
                    Ty::Func(
                        items
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                        ty.replace(replacement.clone(), f).into(),
                        items1
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                    )
                }
            }
            Ty::Closure { func, captures } => {
                if f(self) {
                    replacement
                } else {
                    Ty::Closure {
                        func: func.replace(replacement.clone(), f).into(),
                        captures: captures.clone(),
                    }
                }
            }
            Ty::TypeVar(_) => {
                if f(self) {
                    replacement
                } else {
                    self.clone()
                }
            }
            Ty::Tuple(items) => {
                if f(self) {
                    replacement
                } else {
                    Ty::Tuple(
                        items
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                    )
                }
            }
            Ty::Array(ty) => {
                if f(self) {
                    replacement
                } else {
                    Ty::Array(ty.replace(replacement.clone(), f).into())
                }
            }
            Ty::Row {
                type_var,
                constraints,
                generics,
                kind,
            } => {
                if f(self) {
                    replacement
                } else {
                    // Replace types within constraints
                    let new_constraints = constraints
                        .iter()
                        .map(|c| match c {
                            crate::row::RowConstraint::HasField {
                                type_var,
                                label,
                                field_ty,
                                metadata,
                            } => crate::row::RowConstraint::HasField {
                                type_var: type_var.clone(),
                                label: label.clone(),
                                field_ty: field_ty.replace(replacement.clone(), f),
                                metadata: metadata.clone(),
                            },
                            // TODO: Handle other constraint types if they contain types
                            _ => c.clone(),
                        })
                        .collect();

                    Ty::Row {
                        type_var: type_var.clone(),
                        constraints: new_constraints,
                        generics: generics
                            .iter()
                            .map(|g| g.replace(replacement.clone(), f))
                            .collect(),
                        kind: kind.clone(),
                    }
                }
            }
            _ => {
                if f(self) {
                    replacement
                } else {
                    self.clone()
                }
            }
        }
    }

    /// Get the name of a type (for structs, enums, protocols)
    pub fn name(&self) -> Option<&str> {
        match self {
            Ty::Row { kind, .. } => match kind {
                RowKind::Struct(_, name) | RowKind::Enum(_, name) | RowKind::Protocol(_, name) => {
                    Some(name.as_str())
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Get the symbol ID of a type (for structs, enums, protocols)
    pub fn symbol_id(&self) -> Option<SymbolID> {
        match self {
            Ty::Row { kind, .. } => match kind {
                RowKind::Struct(id, _) | RowKind::Enum(id, _) | RowKind::Protocol(id, _) => {
                    Some(*id)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Find a variant in an enum type
    pub fn find_variant(&self, variant_name: &str) -> Option<(usize, Ty)> {
        match self {
            Ty::Row {
                kind: RowKind::Enum(..),
                constraints,
                ..
            } => {
                for constraint in constraints {
                    if let crate::row::RowConstraint::HasField {
                        label,
                        field_ty,
                        metadata,
                        ..
                    } = constraint
                    {
                        if label == variant_name {
                            if let crate::row::FieldMetadata::EnumCase { tag } = metadata {
                                return Some((*tag, field_ty.clone()));
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Get all variants of an enum type
    pub fn variants(&self) -> Vec<(String, usize, Ty)> {
        match self {
            Ty::Row {
                kind: RowKind::Enum(..),
                constraints,
                ..
            } => {
                let mut variants = Vec::new();
                for constraint in constraints {
                    if let crate::row::RowConstraint::HasField {
                        label,
                        field_ty,
                        metadata,
                        ..
                    } = constraint
                    {
                        if let crate::row::FieldMetadata::EnumCase { tag } = metadata {
                            variants.push((label.clone(), *tag, field_ty.clone()));
                        }
                    }
                }
                variants
            }
            _ => Vec::new(),
        }
    }

    /// Find a property in a struct type
    pub fn find_property(&self, property_name: &str) -> Option<Ty> {
        match self {
            Ty::Row {
                kind: RowKind::Struct(..),
                constraints,
                ..
            } => {
                for constraint in constraints {
                    if let crate::row::RowConstraint::HasField {
                        label,
                        field_ty,
                        metadata,
                        ..
                    } = constraint
                    {
                        if label == property_name {
                            if let crate::row::FieldMetadata::RecordField { .. } = metadata {
                                return Some(field_ty.clone());
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Find a method in a type  
    pub fn find_method(&self, method_name: &str) -> Option<Ty> {
        match self {
            Ty::Row { constraints, .. } => {
                for constraint in constraints {
                    if let crate::row::RowConstraint::HasField {
                        label,
                        field_ty,
                        metadata,
                        ..
                    } = constraint
                    {
                        if label == method_name {
                            if let crate::row::FieldMetadata::Method { .. } = metadata {
                                return Some(field_ty.clone());
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Get all methods of a type
    pub fn methods(&self) -> Vec<(String, Ty)> {
        match self {
            Ty::Row { constraints, .. } => {
                let mut methods = Vec::new();
                for constraint in constraints {
                    if let crate::row::RowConstraint::HasField {
                        label,
                        field_ty,
                        metadata,
                        ..
                    } = constraint
                    {
                        if let crate::row::FieldMetadata::Method { .. } = metadata {
                            methods.push((label.clone(), field_ty.clone()));
                        }
                    }
                }
                methods
            }
            _ => Vec::new(),
        }
    }

    /// Get initializers for a struct type
    pub fn initializers(&self) -> Vec<Ty> {
        match self {
            Ty::Row {
                kind: RowKind::Struct(..),
                constraints,
                ..
            } => {
                let mut inits = Vec::new();
                for constraint in constraints {
                    if let crate::row::RowConstraint::HasField {
                        label,
                        field_ty,
                        metadata,
                        ..
                    } = constraint
                    {
                        if label == "init" {
                            if let crate::row::FieldMetadata::Method { .. } = metadata {
                                inits.push(field_ty.clone());
                            }
                        }
                    }
                }
                inits
            }
            _ => Vec::new(),
        }
    }
}
