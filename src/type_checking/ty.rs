use std::fmt::Display;

use crate::{
    SymbolID,
    type_checker::{FuncParams, FuncReturning, TypeVarID},
};

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    Void,
    Int,
    Bool,
    Float,
    Init(
        SymbolID,
        Vec<Ty>, /* params */
        Vec<Ty>, /* generics */
    ),
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
    Pointer,
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Void => write!(f, "void"),
            Ty::Int => write!(f, "Int"),
            Ty::Bool => write!(f, "Bool"),
            Ty::Float => write!(f, "Float"),
            Ty::Init(_, params, _) => write!(
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
    pub fn optional(&self) -> Ty {
        Ty::Enum(SymbolID::OPTIONAL, vec![self.clone()])
    }
}
