use std::fmt::Display;

use crate::{
    SymbolID,
    type_checker::{FuncParams, FuncReturning},
    type_var_id::TypeVarID,
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ty {
    Void,

    Init(SymbolID, Vec<Ty> /* params */),
    Func(
        FuncParams,    /* params */
        FuncReturning, /* returning */
        Vec<Ty>,       /* generics */
    ),
    Closure {
        func: Box<Ty>, // the func
        captures: Vec<SymbolID>,
    },
    TypeVar(TypeVarID),
    Enum(SymbolID, Vec<Ty>), // enum name + type arguments
    EnumVariant(SymbolID /* Enum */, Vec<Ty> /* Values */),
    Tuple(Vec<Ty>),
    Array(Box<Ty>),
    Struct(SymbolID, Vec<Ty> /* generics */),
    Protocol(SymbolID, Vec<Ty> /* generics */),

    ProtocolSelf,
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Void => write!(f, "void"),
            Ty::ProtocolSelf => write!(f, "Self"),
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
            Ty::Protocol(_, _) => write!(f, "protocol"),
        }
    }
}

impl std::hash::Hash for Ty {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        format!("{self:?}").hash(state);
    }
}

impl Ty {
    pub const INT: Ty = Ty::Struct(SymbolID::INT, Vec::new());
    pub const BOOL: Ty = Ty::Struct(SymbolID::BOOL, Vec::new());
    pub const FLOAT: Ty = Ty::Struct(SymbolID::FLOAT, Vec::new());
    pub const POINTER: Ty = Ty::Struct(SymbolID::POINTER, Vec::new());

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
}
