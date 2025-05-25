use crate::{
    expr::{Expr, FuncName},
    symbol_table::SymbolID,
    type_checker::{FuncParams, Ty},
    typed_expr::TypedExpr,
};

/// A minimal IR for our language
#[derive(Debug)]
enum Instr {
    LoadInt(i64),          // push integer constant
    LoadFloat(f64),        // push float constant
    LoadLocal(u32),        // push value of local slot
    StoreLocal(u32),       // pop and store into local slot
    Call(SymbolID, usize), // call function name with arg count
    Return,                // return top of stack
}

/// Lowers AST expressions into IR for a single function
pub struct Lowerer {
    instrs: Vec<Instr>,
}

impl Lowerer {
    pub fn lower(exprs: &[TypedExpr]) -> Vec<Instr> {
        let entry = if let Some(typed_expr) = exprs.iter().find(|expr| {
            matches!(
                expr,
                TypedExpr {
                    expr: Expr::Func(Some(FuncName::Main), _, _, _),
                    ..
                }
            )
        }) {
            typed_expr
        } else {
            &TypedExpr::new(
                Expr::Func(Some(FuncName::Main), vec![], -1, None),
                Ty::Func(vec![], Box::new(Ty::Void)),
            )
        };

        vec![]
    }
}
