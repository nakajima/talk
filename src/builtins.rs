use crate::{SymbolID, name::Name};

use super::type_checker::Ty;

pub fn match_builtin(name: &Name) -> Option<Ty> {
    let res = match name {
        Name::Resolved(symbol, _) => match symbol {
            SymbolID(-1) => Some(Ty::Int),
            SymbolID(-2) => Some(Ty::Float),
            &_ => None,
        },
        _ => None,
    };

    res
}
