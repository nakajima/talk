use crate::{
    SymbolID,
    expr::Expr,
    lowering::{
        instr::Instr, ir_error::IRError, ir_type::IRType, lowerer::Lowerer, register::Register,
    },
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
        SymbolID(-6) => lower_realloc(lowerer, typed_callee, args),
        SymbolID(-8) => lower_store(lowerer, typed_callee, args),
        SymbolID(-9) => lower_load(lowerer, typed_callee, args),
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

    let Some(typed_expr) = lowerer.source_file.typed_expr(&val, lowerer.env) else {
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

fn lower_realloc(
    lowerer: &mut Lowerer,
    typed_callee: &TypedExpr,
    args: &[ExprID],
) -> Result<Option<Register>, IRError> {
    let dest = lowerer.allocate_register();

    let Ty::Func(_, _, type_params) = &typed_callee.ty else {
        return Err(IRError::Unknown("Did not get __realloc func".to_string()));
    };

    let Some(Expr::CallArg {
        value: _old_pointer,
        ..
    }) = lowerer.source_file.get(&args[0]).cloned()
    else {
        unreachable!("didn't get call arg for realloc")
    };

    let Some(Expr::CallArg {
        value: new_capacity,
        ..
    }) = lowerer.source_file.get(&args[1]).cloned()
    else {
        unreachable!("didn't get call arg for realloc")
    };

    // let old_pointer = lowerer.lower_expr(&old_pointer);
    let new_capacity = lowerer.lower_expr(&new_capacity);

    lowerer.push_instr(Instr::Alloc {
        dest,
        ty: type_params[0].to_ir(lowerer),
        count: new_capacity,
    });

    Ok(Some(dest))
}

fn lower_store(
    lowerer: &mut Lowerer,
    typed_callee: &TypedExpr,
    args: &[ExprID],
) -> Result<Option<Register>, IRError> {
    let dest = lowerer.allocate_register();

    let Ty::Func(_, _, type_params) = &typed_callee.ty else {
        return Err(IRError::Unknown("Did not get __store func".to_string()));
    };

    let Some(Expr::CallArg { value: ptr, .. }) = lowerer.source_file.get(&args[0]).cloned() else {
        unreachable!("didn't get call arg for store")
    };

    let Some(ptr) = lowerer.lower_expr(&ptr) else {
        unreachable!("didn't get ptr for store")
    };

    let Some(Expr::CallArg { value: offset, .. }) = lowerer.source_file.get(&args[1]).cloned()
    else {
        unreachable!("didn't get offset arg for store")
    };

    let Some(offset) = lowerer.lower_expr(&offset) else {
        unreachable!("didn't get offset for store")
    };

    let Some(Expr::CallArg { value, .. }) = lowerer.source_file.get(&args[2]).cloned() else {
        unreachable!("didn't get call arg for store")
    };

    let Some(value) = lowerer.lower_expr(&value) else {
        unreachable!("didn't get value");
    };

    let location = lowerer.allocate_register();
    lowerer.push_instr(Instr::GetElementPointer {
        dest: location,
        base: ptr,
        ty: IRType::Array {
            element: type_params[0].to_ir(lowerer).into(),
        },
        index: offset.into(),
    });

    lowerer.push_instr(Instr::Store {
        ty: type_params[0].to_ir(lowerer),
        val: value,
        location,
    });

    Ok(Some(dest))
}

fn lower_load(
    lowerer: &mut Lowerer,
    typed_callee: &TypedExpr,
    args: &[ExprID],
) -> Result<Option<Register>, IRError> {
    let dest = lowerer.allocate_register();

    let Ty::Func(_, _, type_params) = &typed_callee.ty else {
        return Err(IRError::Unknown("Did not get __load func".to_string()));
    };

    let Some(Expr::CallArg { value: ptr, .. }) = lowerer.source_file.get(&args[0]).cloned() else {
        unreachable!("didn't get call arg for load")
    };

    let Some(ptr) = lowerer.lower_expr(&ptr) else {
        unreachable!("didn't get ptr for load")
    };

    let Some(Expr::CallArg { value: offset, .. }) = lowerer.source_file.get(&args[1]).cloned()
    else {
        unreachable!("didn't get offset arg for load")
    };

    let Some(offset) = lowerer.lower_expr(&offset) else {
        unreachable!("didn't get offset for load")
    };

    let location = lowerer.allocate_register();
    lowerer.push_instr(Instr::GetElementPointer {
        dest: location,
        base: ptr,
        ty: IRType::Array {
            element: type_params[0].to_ir(lowerer).into(),
        },
        index: offset.into(),
    });

    lowerer.push_instr(Instr::Load {
        dest,
        ty: type_params[0].to_ir(lowerer),
        addr: location,
    });

    Ok(Some(dest))
}
