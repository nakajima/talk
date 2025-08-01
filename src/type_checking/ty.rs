use std::{collections::BTreeMap, fmt::Display};

use derive_visitor::Drive;

use crate::{
    SymbolID, impl_option_eq,
    row::FieldInfo,
    type_checker::{FuncParams, FuncReturning},
    type_var_id::TypeVarID,
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
    // Row structure is expressed through constraints on the type_var
    Row {
        type_var: TypeVarID,  // Type variable with row constraints
        generics: Vec<Ty>,    // Generic type arguments (for nominal types)
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
                type_var: _,
                generics: _,
                kind,
            } => {
                if let RowKind::Struct(_, name)
                | RowKind::Protocol(_, name)
                | RowKind::Enum(_, name) = kind
                {
                    write!(f, "{}", name)
                } else {
                    // Structural type - we'd need constraint context to display fields
                    write!(f, "{{...}}")
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
            type_var: TypeVarID::new(),
            generics: vec![],
            kind: RowKind::Struct(SymbolID::STRING, "String".into()),
        }
    }

    /// Create a struct type using Row representation
    pub fn struct_type(symbol_id: SymbolID, name: String, generics: Vec<Ty>) -> Ty {
        // Create Row type for structs
        Ty::Row {
            type_var: TypeVarID::new(),
            generics,
            kind: RowKind::Struct(symbol_id, name),
        }
    }

    /// Create a protocol type using Row representation
    pub fn protocol_type(symbol_id: SymbolID, name: String, generics: Vec<Ty>) -> Ty {
        Ty::Row {
            type_var: TypeVarID::new(),
            generics,
            kind: RowKind::Protocol(symbol_id, name),
        }
    }

    /// Create an enum type using Row representation
    pub fn enum_type(symbol_id: SymbolID, name: String, generics: Vec<Ty>) -> Ty {
        Ty::Row {
            type_var: TypeVarID::new(),
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

    pub fn satisfies(&self, other: &Ty) -> bool {
        match (self, other) {
            (
                Ty::Row {
                    type_var: lhs_var,
                    generics: lhs_generics,
                    kind: lhs_kind,
                },
                Ty::Row {
                    type_var: rhs_var,
                    generics: rhs_generics,
                    kind: rhs_kind,
                },
            ) => {
                // For constraint-based rows, we'd need access to the constraint solver
                // For now, just check structural equality
                lhs_var == rhs_var
                    && lhs_kind == rhs_kind
                    && lhs_generics.len() == rhs_generics.len()
                    && lhs_generics
                        .iter()
                        .enumerate()
                        .all(|(i, g)| g.satisfies(&rhs_generics[i]))
            }
            (_, _) => self == other,
        }
    }

    pub fn equal_to(&self, other: &Ty) -> bool {
        match (self, other) {
            (
                Ty::Row {
                    type_var: lhs_var,
                    generics: lhs_generics,
                    kind: lhs_kind,
                },
                Ty::Row {
                    type_var: rhs_var,
                    generics: rhs_generics,
                    kind: rhs_kind,
                },
            ) => {
                lhs_var == rhs_var
                    && lhs_kind == rhs_kind
                    && lhs_generics.len() == rhs_generics.len()
                    && lhs_generics
                        .iter()
                        .enumerate()
                        .all(|(i, g)| g.equal_to(&rhs_generics[i]))
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
                generics,
                kind,
            } => {
                if f(self) {
                    replacement
                } else {
                    Ty::Row {
                        type_var: type_var.clone(),
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
}
