use crate::{
    SymbolID,
    lowering::lowerer::{IRError, Lowerer, Register},
};

pub fn lower_builtin(
    symbol_id: &SymbolID,
    lowerer: &mut Lowerer,
) -> Result<Option<Register>, IRError> {
    match symbol_id {
        SymbolID(-5) => lower_array_init(lowerer),
        _ => Err(IRError::ParseError),
    }
}

fn lower_array_init(_lowerer: &mut Lowerer) -> Result<Option<Register>, IRError> {
    Ok(None)
}
