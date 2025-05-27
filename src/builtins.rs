use crate::{SymbolID, expr::Name};

use super::type_checker::Ty;

pub fn match_builtin(name: &Name) -> Option<Ty> {
    let res = match name {
        Name::Resolved(symbol) => match symbol {
            SymbolID(-1) => Some(Ty::Int),
            SymbolID(-2) => Some(Ty::Float),
            &_ => {
                println!("Unknown builtin: {:?}", symbol);
                None
            }
        },
        _ => None,
    };

    res
}
