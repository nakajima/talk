use crate::{SymbolID, expr::Name};

use super::type_checker::Ty;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BuiltinType {
    Int,
    Float,
}

impl BuiltinType {
    pub fn symbol_id(&self) -> SymbolID {
        match self {
            Self::Int => SymbolID(-1),
            Self::Float => SymbolID(-2),
        }
    }

    pub fn as_ty(&self) -> Ty {
        match self {
            Self::Int => Ty::Int,
            Self::Float => Ty::Float,
        }
    }
}

pub fn match_builtin(name: &Name) -> Option<Ty> {
    let res = match name {
        Name::Raw(t) => match t.as_str() {
            "Int" => Some(Ty::Int),
            "Float" => Some(Ty::Float),
            &_ => None,
        },
        _ => None,
    };

    res
}
