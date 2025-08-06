use std::{collections::BTreeMap, fmt::Display};

use derive_visitor::Drive;

use crate::{
    SymbolID, builtin_type_def,
    environment::Environment,
    impl_option_eq,
    type_checker::{FuncParams, FuncReturning},
    type_def::TypeDef,
    type_var_id::TypeVarID,
};

/// The kind of row type - struct, protocol, or record
#[derive(Clone, PartialEq, Debug, Drive)]
pub enum RowKind2 {
    /// A struct - concrete type with storage
    Struct,
    /// A protocol - interface/trait type without storage
    Protocol,
    /// A record - structural type (anonymous)
    Record,
    /// An enum - sum type with variants
    Enum,
}

impl_option_eq!(Ty2);

#[derive(Clone, PartialEq, Debug, Drive)]
pub enum Ty2 {
    Void,
    Int,
    Bool,
    Float,
    Init(#[drive(skip)] SymbolID, Vec<Ty2> /* params */),
    Method {
        self_ty: Box<Ty2>,
        func: Box<Ty2>,
    },
    Func(
        FuncParams,    /* params */
        FuncReturning, /* returning */
        Vec<Ty2>,      /* generics */
    ),
    Closure {
        func: Box<Ty2>, // the func
        #[drive(skip)]
        captures: Vec<SymbolID>,
    },
    TypeVar(#[drive(skip)] TypeVarID),
    Tuple(Vec<Ty2>),
    Array(Box<Ty2>),
    Byte,
    Pointer,
    SelfType,
    // Unified row type that can represent structs, protocols, and records
    Row {
        #[drive(skip)]
        fields: Vec<(String, Ty2)>, // field name -> type pairs, in canonical order
        row: Option<Box<Ty2>>, // Optional row variable for extensible rows
        #[drive(skip)]
        nominal_id: Option<SymbolID>, // Some for nominal types (structs/protocols), None for structural (records)
        generics: Vec<Ty2>, // Generic type arguments (for nominal types)
        #[drive(skip)]
        kind: RowKind2, // Distinguishes between struct/protocol/record
    },
}

impl Display for Ty2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty2::Byte => write!(f, "byte"),
            Ty2::Void => write!(f, "void"),
            Ty2::Int => write!(f, "Int"),
            Ty2::Bool => write!(f, "Bool"),
            Ty2::Float => write!(f, "Float"),
            Ty2::SelfType => write!(f, "Self"),
            Ty2::Init(_, params) => write!(
                f,
                "init({})",
                params
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty2::Method {
                func: box Ty2::Func(params, _, _),
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
            Ty2::Func(params, ty, _) => write!(
                f,
                "func({}) -> {ty}",
                params
                    .iter()
                    .map(|p| format!("{p}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty2::Closure { func, .. } => write!(f, "{func}"),
            Ty2::TypeVar(type_var_id) => write!(f, "{type_var_id:?}"),
            Ty2::Tuple(items) => write!(
                f,
                "({})",
                items
                    .iter()
                    .map(|i| format!("{i}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Ty2::Array(ty) => write!(f, "Array<{ty}>"),
            Ty2::Pointer => write!(f, "pointer"),
            Ty2::Row {
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
                        RowKind2::Protocol => write!(f, "{base_name} (protocol)"),
                        _ => write!(f, "{base_name}"),
                    }
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

impl std::hash::Hash for Ty2 {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        format!("{self:?}").hash(state);
    }
}

impl Eq for Ty2 {}

impl Ty2 {
    /// Check if this type is a protocol
    pub fn is_protocol(&self) -> bool {
        matches!(
            self,
            Ty2::Row {
                kind: RowKind2::Protocol,
                ..
            }
        )
    }

    pub fn string() -> Ty2 {
        // String is a builtin struct type without fields
        Ty2::Row {
            fields: vec![], // String has no exposed fields
            row: None,
            nominal_id: Some(SymbolID::STRING),
            generics: vec![],
            kind: RowKind2::Struct,
        }
    }

    /// Create a struct type using Row representation
    pub fn struct_type(symbol_id: SymbolID, generics: Vec<Ty2>) -> Ty2 {
        // Create Row type for structs
        Ty2::Row {
            fields: vec![], // Fields are stored in TypeDef
            row: None,      // TODO: Get row var from TypeDef
            nominal_id: Some(symbol_id),
            generics,
            kind: RowKind2::Struct,
        }
    }

    /// Create a protocol type using Row representation
    pub fn protocol_type(symbol_id: SymbolID, generics: Vec<Ty2>) -> Ty2 {
        Ty2::Row {
            fields: vec![], // Protocol members are stored in TypeDef
            row: None,
            nominal_id: Some(symbol_id),
            generics,
            kind: RowKind2::Protocol,
        }
    }

    /// Create an enum type using Row representation
    pub fn enum_type(symbol_id: SymbolID, generics: Vec<Ty2>) -> Ty2 {
        Ty2::Row {
            fields: vec![], // Enum variants are stored in TypeDef
            row: None,
            nominal_id: Some(symbol_id),
            generics,
            kind: RowKind2::Enum,
        }
    }

    pub fn optional(&self) -> Ty2 {
        Ty2::enum_type(SymbolID::OPTIONAL, vec![self.clone()])
    }

    pub fn is_concrete(&self) -> bool {
        !matches!(self, Ty2::TypeVar(_))
    }

    pub fn equal_to(&self, other: &Ty2) -> bool {
        match (self, other) {
            (
                Ty2::Row {
                    fields: lhs_fields,
                    row: lhs_row,
                    nominal_id: lhs_nominal_id,
                    generics: lhs_generics,
                    kind: lhs_kind,
                },
                Ty2::Row {
                    fields: rhs_fields,
                    row: rhs_row,
                    nominal_id: rhs_nominal_id,
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

                if lhs_nominal_id != rhs_nominal_id {
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

                let lhs_fields: BTreeMap<String, Ty2> = BTreeMap::from_iter(lhs_fields.clone());
                let rhs_fields: BTreeMap<String, Ty2> = BTreeMap::from_iter(rhs_fields.clone());

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
            Ty2::Row {
                nominal_id: Some(sym),
                ..
            } => *sym,
            Ty2::Int => SymbolID::INT,
            Ty2::Float => SymbolID::FLOAT,
            Ty2::Bool => SymbolID::BOOL,
            Ty2::Pointer => SymbolID::POINTER,
            _ => return None,
        };

        env.lookup_type(&sym)
    }

    pub fn replace<F: Fn(&Ty2) -> bool>(&self, replacement: Ty2, f: &F) -> Ty2 {
        match &self {
            Ty2::Init(sym, items) => {
                if f(self) {
                    replacement
                } else {
                    Ty2::Init(
                        *sym,
                        items
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                    )
                }
            }
            Ty2::Func(items, ty, items1) => {
                if f(self) {
                    replacement
                } else {
                    Ty2::Func(
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
            Ty2::Closure { func, captures } => {
                if f(self) {
                    replacement
                } else {
                    Ty2::Closure {
                        func: func.replace(replacement.clone(), f).into(),
                        captures: captures.clone(),
                    }
                }
            }
            Ty2::TypeVar(_) => {
                if f(self) {
                    replacement
                } else {
                    self.clone()
                }
            }
            Ty2::Tuple(items) => {
                if f(self) {
                    replacement
                } else {
                    Ty2::Tuple(
                        items
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                    )
                }
            }
            Ty2::Array(ty) => {
                if f(self) {
                    replacement
                } else {
                    Ty2::Array(ty.replace(replacement.clone(), f).into())
                }
            }
            Ty2::Row {
                fields,
                row,
                nominal_id,
                generics,
                kind,
            } => {
                if f(self) {
                    replacement
                } else {
                    Ty2::Row {
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
