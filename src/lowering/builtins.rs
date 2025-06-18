use crate::{
    SymbolID,
    expr::Expr,
    lowering::{instr::Instr, ir_error::IRError, lowerer::Lowerer, register::Register},
    parser::ExprID,
    type_checker::Ty,
    typed_expr::TypedExpr,
};

pub fn lower_builtin(
    symbol_id: &SymbolID,
    typed_callee: &TypedExpr,
    args: &[ExprID],
    lowerer: &mut Lowerer,
) -> Result<Option<Register>, IRError> {
    match symbol_id {
        SymbolID(-5) => lower_alloc(lowerer, typed_callee, args),
        _ => Err(IRError::ParseError),
    }
}

fn lower_alloc(
    lowerer: &mut Lowerer,
    typed_callee: &TypedExpr,
    args: &[ExprID],
) -> Result<Option<Register>, IRError> {
    let dest = lowerer.allocate_register();

    let Ty::Func(_, _, type_params) = &typed_callee.ty else {
        return Err(IRError::Unknown("Did not get __alloc func".to_string()));
    };

    if args.len() != 1 {
        return Err(IRError::Unknown(format!(
            "__alloc takes an Int, got no arguments {args:?}",
        )));
    }

    let Some(Expr::CallArg { value: val, .. }) = lowerer.source_file.get(&args[0]).cloned() else {
        return Err(IRError::Unknown(format!(
            "Did not get argument for __alloc, got: {:?}",
            lowerer.source_file.get(&args[0])
        )));
    };

    let Some(typed_expr) = lowerer.source_file.typed_expr(&val) else {
        return Err(IRError::Unknown(format!(
            "__alloc takes an Int, got {:?}",
            lowerer.source_file.get(&val)
        )));
    };

    if !matches!(typed_expr.ty, Ty::Int) {
        return Err(IRError::Unknown(format!(
            "__alloc takes an Int, got {:?}",
            lowerer.source_file.get(&val)
        )));
    }

    let register = lowerer.lower_expr(&val);

    lowerer.push_instr(Instr::Alloc {
        dest,
        ty: type_params[0].to_ir(lowerer),
        count: register,
    });

    Ok(Some(dest))
}
