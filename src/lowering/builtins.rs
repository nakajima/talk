use crate::{
    SymbolID,
    expr::Expr,
    lowering::{
        instr::Instr,
        lowerer::{IRError, Lowerer},
        register::Register,
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
        unreachable!()
    };

    let Expr::CallArg { value: val, .. } = lowerer.source_file.get(&args[0]).unwrap() else {
        unreachable!()
    };

    let Some(Expr::LiteralInt(val)) = lowerer.source_file.get(val) else {
        unreachable!()
    };

    lowerer.push_instr(Instr::Alloc {
        dest,
        ty: type_params[0].to_ir(lowerer),
        count: Some(str::parse(val).unwrap()),
    });

    Ok(Some(dest))
}

#[cfg(test)]
mod tests {
    use crate::{
        SymbolID, SymbolTable, assert_lowered_functions, check,
        lowering::{
            instr::Instr,
            ir_module::IRModule,
            ir_type::IRType,
            lowerer::{BasicBlock, BasicBlockID, IRError, IRFunction, Lowerer},
            register::Register,
        },
    };

    fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let typed = check(input).unwrap();
        let mut symbol_table = SymbolTable::base();
        let lowerer = Lowerer::new(typed, &mut symbol_table);
        let mut module = IRModule::new();
        lowerer.lower(&mut module)?;
        Ok(module)
    }

    #[test]
    fn lowers_alloc() {
        let lowered = lower("__alloc<Int>(4)").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::Alloc {
                            dest: Register(1),
                            ty: IRType::Int,
                            count: Some(4),
                        },
                        Instr::Ret(IRType::Int, Some(Register(1)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![])
            }],
        )
    }
}
