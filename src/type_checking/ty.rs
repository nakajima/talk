use std::fmt::Display;

use derive_visitor::Drive;

use crate::{
    SymbolID, builtin_type_def,
    environment::Environment,
    type_checker::{FuncParams, FuncReturning},
    type_def::TypeDef,
    type_var_id::TypeVarID,
};

/// The kind of row type - struct, protocol, or record
#[derive(Clone, PartialEq, Debug, Drive)]
pub enum RowKind {
    /// A struct - concrete type with storage
    Struct,
    /// A protocol - interface/trait type without storage
    Protocol,
    /// A record - structural type (anonymous)
    Record,
}

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
    Enum(#[drive(skip)] SymbolID, Vec<Ty>), // enum name + type arguments
    EnumVariant(
        #[drive(skip)] SymbolID, /* Enum */
        Vec<Ty>,                 /* Values */
    ),
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
        #[drive(skip)]
        nominal_id: Option<SymbolID>, // Some for nominal types (structs/protocols), None for structural (records)
        generics: Vec<Ty>, // Generic type arguments (for nominal types)
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
            Ty::Enum(_, _) => write!(f, "enum"),
            Ty::EnumVariant(_, _) => write!(f, "enum variant"),
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
                nominal_id,
                generics: _,
                kind,
            } => {
                if let Some(sym) = nominal_id {
                    // Nominal type - display based on kind
                    let base_name = if let Some(builtin) = builtin_type_def(sym) {
                        builtin.name().to_string()
                    } else if sym == &SymbolID::ARRAY {
                        "Array".to_string()
                    } else if sym == &SymbolID::STRING {
                        "String".to_string()
                    } else {
                        format!("Row({sym:?})")
                    };
                    match kind {
                        RowKind::Protocol => write!(f, "{} (protocol)", base_name),
                        _ => write!(f, "{}", base_name),
                    }
                } else {
                    // Structural type - display as record
                    let field_strs: Vec<String> = fields
                        .iter()
                        .map(|(name, ty)| format!("{}: {}", name, ty))
                        .collect();
                    let mut result = field_strs.join(", ");
                    if let Some(row_ty) = row {
                        if !fields.is_empty() {
                            result.push_str(", ");
                        }
                        result.push_str(&format!("..{}", row_ty));
                    }
                    write!(f, "{{{}}}", result)
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
                kind: RowKind::Protocol,
                ..
            }
        )
    }

    pub fn string() -> Ty {
        // String is a builtin struct type without fields
        Ty::Row {
            fields: vec![], // String has no exposed fields
            row: None,
            nominal_id: Some(SymbolID::STRING),
            generics: vec![],
            kind: RowKind::Struct,
        }
    }

    /// Create a struct type using Row representation
    pub fn struct_type(symbol_id: SymbolID, generics: Vec<Ty>) -> Ty {
        // Create Row type for structs
        Ty::Row {
            fields: vec![], // Fields are stored in TypeDef
            row: None,      // TODO: Get row var from TypeDef
            nominal_id: Some(symbol_id),
            generics,
            kind: RowKind::Struct,
        }
    }

    /// Create a protocol type using Row representation
    pub fn protocol_type(symbol_id: SymbolID, generics: Vec<Ty>) -> Ty {
        Ty::Row {
            fields: vec![], // Protocol members are stored in TypeDef
            row: None,
            nominal_id: Some(symbol_id),
            generics,
            kind: RowKind::Protocol,
        }
    }

    pub fn optional(&self) -> Ty {
        Ty::Enum(SymbolID::OPTIONAL, vec![self.clone()])
    }

    pub fn some(&self) -> Ty {
        Ty::EnumVariant(SymbolID::OPTIONAL, vec![self.clone()])
    }

    pub fn is_concrete(&self) -> bool {
        !matches!(self, Ty::TypeVar(_))
    }

    pub fn type_def<'a>(&self, env: &'a Environment) -> Option<&'a TypeDef> {
        let sym = match self {
            Ty::Enum(sym, _)
            | Ty::Row {
                nominal_id: Some(sym),
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
            Ty::Enum(symbol_id, items) => {
                if f(self) {
                    replacement
                } else {
                    Ty::Enum(
                        *symbol_id,
                        items
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                    )
                }
            }
            Ty::EnumVariant(symbol_id, items) => {
                if f(self) {
                    replacement
                } else {
                    Ty::EnumVariant(
                        *symbol_id,
                        items
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                    )
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
                nominal_id,
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
                        nominal_id: *nominal_id,
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
