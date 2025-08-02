use std::str::FromStr;

use crate::{
    SymbolID,
    lowering::{
        instr::Instr,
        ir_error::IRError,
        ir_type::IRType,
        lowerer::{Lowerer, TypedRegister},
        register::Register,
    },
    ty::Ty2,
    typed_expr::{Expr, TypedExpr},
};

pub fn lower_builtin(
    symbol_id: &SymbolID,
    typed_callee: &TypedExpr,
    args: &[TypedRegister],
    arg_exprs: &[TypedExpr],
    lowerer: &mut Lowerer,
) -> Result<Option<Register>, IRError> {
    match symbol_id {
        SymbolID(-5) => lower_alloc(lowerer, typed_callee, args, arg_exprs),
        SymbolID(-6) => lower_realloc(lowerer, typed_callee, args, arg_exprs),
        SymbolID(-7) => lower_free(lowerer, typed_callee, args, arg_exprs),
        SymbolID(-8) => lower_store(lowerer, typed_callee, args, arg_exprs),
        SymbolID(-9) => lower_load(lowerer, typed_callee, args, arg_exprs),
        SymbolID(-11) => lower_print(lowerer, typed_callee, args, arg_exprs),
        SymbolID(-12) => lower_ir_instr(lowerer, typed_callee, args, arg_exprs),
        _ => Err(IRError::BuiltinNotFound(*symbol_id)),
    }
}

fn lower_free(
    _lowerer: &mut Lowerer,
    _typed_callee: &TypedExpr,
    _args: &[TypedRegister],
    _arg_exprs: &[TypedExpr],
) -> Result<Option<Register>, IRError> {
    tracing::warn!("TODO: lower __free");

    Ok(None)
}

fn lower_alloc(
    lowerer: &mut Lowerer,
    typed_callee: &TypedExpr,
    args: &[TypedRegister],
    _arg_exprs: &[TypedExpr],
) -> Result<Option<Register>, IRError> {
    let dest = lowerer.allocate_register();

    let Ty2::Func(_, _, type_params) = &typed_callee.ty else {
        return Err(IRError::Unknown("Did not get __alloc func".to_string()));
    };

    if args.len() != 1 {
        return Err(IRError::Unknown(format!(
            "__alloc takes an Int, got no arguments {args:?}",
        )));
    }

    let val = &args[0];

    if !matches!(val.ty, IRType::Int) {
        return Err(IRError::Unknown(format!(
            "__alloc takes an Int, got {val:?}"
        )));
    }

    lowerer.push_instr(Instr::Alloc {
        dest,
        ty: type_params[0].to_ir(lowerer),
        count: Some(val.register.into()),
    });

    Ok(Some(dest))
}

#[allow(clippy::todo)]
fn lower_realloc(
    _lowerer: &mut Lowerer,
    _typed_callee: &TypedExpr,
    _args: &[TypedRegister],
    _arg_exprs: &[TypedExpr],
) -> Result<Option<Register>, IRError> {
    todo!()
}

fn lower_print(
    lowerer: &mut Lowerer,
    _typed_callee: &TypedExpr,
    args: &[TypedRegister],
    _arg_exprs: &[TypedExpr],
) -> Result<Option<Register>, IRError> {
    if args.is_empty() {
        return Err(IRError::Unknown("No arg to print".to_string()));
    }

    lowerer.push_instr(Instr::Print {
        ty: args[0].ty.clone(),
        val: args[0].register.into(),
    });

    Ok(None)
}

fn lower_store(
    lowerer: &mut Lowerer,
    typed_callee: &TypedExpr,
    args: &[TypedRegister],
    _arg_exprs: &[TypedExpr],
) -> Result<Option<Register>, IRError> {
    let Ty2::Func(_, _, type_params) = &typed_callee.ty else {
        return Err(IRError::Unknown("Did not get __store func".to_string()));
    };

    let location = lowerer.allocate_register();
    lowerer.push_instr(Instr::GetElementPointer {
        dest: location,
        base: args[0].register,
        ty: IRType::TypedBuffer {
            element: type_params[0].to_ir(lowerer).into(),
        },
        index: args[1].register.into(),
    });

    lowerer.push_instr(Instr::Store {
        ty: type_params[0].to_ir(lowerer),
        val: args[2].register.into(),
        location,
    });

    Ok(None)
}

fn lower_load(
    lowerer: &mut Lowerer,
    typed_callee: &TypedExpr,
    args: &[TypedRegister],
    _arg_exprs: &[TypedExpr],
) -> Result<Option<Register>, IRError> {
    let dest = lowerer.allocate_register();

    let Ty2::Func(_, _, type_params) = &typed_callee.ty else {
        return Err(IRError::Unknown("Did not get __load func".to_string()));
    };

    let location = lowerer.allocate_register();
    lowerer.push_instr(Instr::GetElementPointer {
        dest: location,
        base: args[0].register,
        ty: IRType::TypedBuffer {
            element: type_params[0].to_ir(lowerer).into(),
        },
        index: args[1].register.into(),
    });

    lowerer.push_instr(Instr::Load {
        dest,
        ty: type_params[0].to_ir(lowerer),
        addr: location,
    });

    Ok(Some(dest))
}

fn lower_ir_instr(
    lowerer: &mut Lowerer,
    typed_callee: &TypedExpr,
    _args: &[TypedRegister],
    arg_exprs: &[TypedExpr],
) -> Result<Option<Register>, IRError> {
    let Ty2::Func(_, _, _) = &typed_callee.ty else {
        return Err(IRError::Unknown("Did not get __ir_instr func".to_string()));
    };

    let Expr::CallArg {
        value:
            box TypedExpr {
                expr: Expr::LiteralString(instruction_string),
                ..
            },
        ..
    } = &arg_exprs[0].expr
    else {
        unreachable!(
            "didn't get call instruction string: {:?} {typed_callee:?}",
            &arg_exprs[0]
        );
    };

    let ret_reg = lowerer.allocate_register();
    let substituted_string = instruction_string.replace("$?", &format!("{ret_reg}"));

    let instr = match Instr::from_str(&substituted_string) {
        Ok(instr) => instr,
        Err(e) => return Err(IRError::ParseError(format!("{e:?}"))),
    };

    lowerer.push_instr(instr);

    Ok(Some(ret_reg))
}
