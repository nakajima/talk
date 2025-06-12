use crate::{
    SymbolID,
    expr::Expr,
    lowering::{
        instr::Instr,
        lowerer::{IRError, Lowerer, Register},
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
    let Ty::Func(_, _, generics) = &typed_callee.ty else {
        unreachable!()
    };
    let element_ty = generics[0].to_ir();
    let Expr::LiteralInt(val) = lowerer.source_file.get(&args[0]).unwrap() else {
        unreachable!()
    };

    lowerer.push_instr(Instr::Alloc {
        dest,
        ty: element_ty,
        count: str::parse(val).unwrap(),
    });

    Ok(Some(dest))
}

#[cfg(test)]
mod tests {
    use crate::{
        SymbolTable, assert_lowered_functions, check,
        lowering::{
            instr::Instr,
            ir_module::IRModule,
            ir_type::IRType,
            lowerer::{BasicBlock, BasicBlockID, IRError, IRFunction, Lowerer, Register},
        },
    };

    fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let typed = check(input).unwrap();
        let mut symbol_table = SymbolTable::default();
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
                            count: 4,
                            ty: IRType::Int
                        },
                        Instr::Ret(IRType::Int, Some(Register(1)))
                    ],
                }],
                env_ty: IRType::Struct(vec![])
            }],
        )
    }
}
