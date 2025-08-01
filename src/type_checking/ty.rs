use std::{collections::BTreeMap, fmt::Display};

use derive_visitor::Drive;

use crate::{
    SymbolID,
    environment::Environment,
    impl_option_eq,
    type_checker::{FuncParams, FuncReturning},
    type_def::TypeDef,
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
pub enum Ty {
    Void,
    Int,
    Bool,
    Float,
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
    Byte,
    Pointer,
    SelfType,
    // Unified row type that can represent structs, protocols, and records
    Row {
        #[drive(skip)]
        fields: Vec<(String, Ty)>, // field name -> type pairs, in canonical order
        row: Option<Box<Ty>>, // Optional row variable for extensible rows
        generics: Vec<Ty>,    // Generic type arguments (for nominal types)
        #[drive(skip)]
        kind: RowKind, // Distinguishes between struct/protocol/record
    },
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Byte => write!(f, "byte"),
            Ty::Void => write!(f, "void"),
            Ty::Int => write!(f, "Int"),
            Ty::Bool => write!(f, "Bool"),
            Ty::Float => write!(f, "Float"),
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
            Ty::Pointer => write!(f, "pointer"),
            Ty::Row {
                fields,
                row,
                generics: _,
                kind,
            } => {
                if let RowKind::Struct(_, name)
                | RowKind::Protocol(_, name)
                | RowKind::Enum(_, name) = kind
                {
                    write!(f, "{}", name)
                } else {
                    // Structural type - display as record
                    let field_strs: Vec<String> = fields
                        .iter()
                        .map(|(name, ty)| format!("{name}: {ty}"))
                        .collect();
                    let mut result = field_strs.join(", ");
                    if let Some(row_ty) = row {
                        if !fields.is_empty() {
                            result.push_str(", ");
                        }
                        result.push_str(&format!("..{row_ty}"));
                    }
                    write!(f, "{{{result}}}")
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

impl Ty {
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
        // String is a builtin struct type without fields
        Ty::Row {
            fields: vec![], // String has no exposed fields
            row: None,
            generics: vec![],
            kind: RowKind::Struct(SymbolID::STRING, "String".into()),
        }
    }

    /// Create a struct type using Row representation
    pub fn struct_type(symbol_id: SymbolID, name: String, generics: Vec<Ty>) -> Ty {
        // Create Row type for structs
        Ty::Row {
            fields: vec![], // Fields are stored in TypeDef
            row: None,      // TODO: Get row var from TypeDef
            generics,
            kind: RowKind::Struct(symbol_id, name),
        }
    }

    /// Create a protocol type using Row representation
    pub fn protocol_type(symbol_id: SymbolID, name: String, generics: Vec<Ty>) -> Ty {
        Ty::Row {
            fields: vec![], // Protocol members are stored in TypeDef
            row: None,
            generics,
            kind: RowKind::Protocol(symbol_id, name),
        }
    }

    /// Create an enum type using Row representation
    pub fn enum_type(symbol_id: SymbolID, name: String, generics: Vec<Ty>) -> Ty {
        Ty::Row {
            fields: vec![], // Enum variants are stored in TypeDef
            row: None,
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

    pub fn equal_to(&self, other: &Ty) -> bool {
        match (self, other) {
            (
                Ty::Row {
                    fields: lhs_fields,
                    row: lhs_row,
                    generics: lhs_generics,
                    kind: lhs_kind,
                },
                Ty::Row {
                    fields: rhs_fields,
                    row: rhs_row,
                    generics: rhs_generics,
                    kind: rhs_kind,
                },
            ) => {
                if lhs_kind != rhs_kind {
                    return false;
                }

                if lhs_row != rhs_row {
                    return false;
                }

                if lhs_fields.len() != rhs_fields.len() {
                    return false;
                }

                if lhs_generics.len() != rhs_generics.len() {
                    return false;
                }

                if !lhs_generics
                    .iter()
                    .enumerate()
                    .all(|(i, g)| g.equal_to(&rhs_generics[i]))
                {
                    return false;
                }

                let lhs_fields: BTreeMap<String, Ty> = BTreeMap::from_iter(lhs_fields.clone());
                let rhs_fields: BTreeMap<String, Ty> = BTreeMap::from_iter(rhs_fields.clone());

                for (field, ty) in &lhs_fields {
                    let Some(rhs_ty) = rhs_fields.get(field) else {
                        return false;
                    };

                    if !ty.equal_to(rhs_ty) {
                        return false;
                    }
                }

                true
            }
            (_, _) => self == other,
        }
    }

    pub fn type_def<'a>(&self, env: &'a Environment) -> Option<&'a TypeDef> {
        let sym = match self {
            Ty::Row {
                kind: RowKind::Struct(sym, _) | RowKind::Enum(sym, _) | RowKind::Protocol(sym, _),
                ..
            } => *sym,
            Ty::Int => SymbolID::INT,
            Ty::Float => SymbolID::FLOAT,
            Ty::Bool => SymbolID::BOOL,
            Ty::Pointer => SymbolID::POINTER,
            _ => return None,
        };

        env.lookup_type(&sym)
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
                fields,
                row,
                generics,
                kind,
            } => {
                if f(self) {
                    replacement
                } else {
                    Ty::Row {
                        fields: fields
                            .iter()
                            .map(|(name, ty)| (name.clone(), ty.replace(replacement.clone(), f)))
                            .collect(),
                        row: row
                            .as_ref()
                            .map(|r| Box::new(r.replace(replacement.clone(), f))),
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
