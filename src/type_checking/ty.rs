use std::fmt::Display;

use crate::{
    SymbolID,
    environment::Environment,
    name::ResolvedName,
    type_checker::{FuncParams, FuncReturning},
    type_defs::TypeDef,
    type_var_id::TypeVarID,
};

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    Void,
    Int,
    Bool,
    Float,
    Init(SymbolID, Vec<Ty> /* params */),
    Func(
        FuncParams,    /* params */
        FuncReturning, /* returning */
        Vec<Ty>,       /* generics */
    ),
    Closure {
        func: Box<Ty>, // the func
        captures: Vec<ResolvedName>,
    },
    TypeVar(TypeVarID),
    Enum(ResolvedName, Vec<Ty>), // enum name + type arguments
    EnumVariant(ResolvedName /* Enum */, Vec<Ty> /* Values */),
    Tuple(Vec<Ty>),
    Array(Box<Ty>),
    Struct(ResolvedName, Vec<Ty> /* generics */),
    Protocol(ResolvedName, Vec<Ty> /* generics */),
    Byte,
    Pointer,
    SelfType,
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
            Ty::Struct(_, _) => write!(f, "struct"),
            Ty::Pointer => write!(f, "pointer"),
            Ty::Protocol(_, _) => write!(f, "protocol"),
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
    pub fn string() -> Ty {
        Ty::Struct(SymbolID::STRING, vec![])
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
            Ty::Struct(sym, _) | Ty::Enum(sym, _) | Ty::Protocol(sym, _) => sym,
            Ty::Int => &SymbolID::INT,
            Ty::Float => &SymbolID::FLOAT,
            Ty::Bool => &SymbolID::BOOL,
            Ty::Pointer => &SymbolID::POINTER,
            _ => return None,
        };

        env.lookup_type(sym)
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
            Ty::Struct(symbol_id, items) => {
                if f(self) {
                    replacement
                } else {
                    Ty::Struct(
                        *symbol_id,
                        items
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                    )
                }
            }
            Ty::Protocol(symbol_id, items) => {
                if f(self) {
                    replacement
                } else {
                    Ty::Protocol(
                        *symbol_id,
                        items
                            .iter()
                            .map(|t| t.replace(replacement.clone(), f))
                            .collect(),
                    )
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
