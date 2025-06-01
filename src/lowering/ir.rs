use crate::{
    SourceFile, Typed,
    expr::{Expr, FuncName},
    symbol_table::SymbolID,
    type_checker::Ty,
    typed_expr::TypedExpr,
};

/// A minimal IR for our language
#[derive(Debug)]
#[allow(dead_code)]
pub enum Instr {
    LoadInt(i64),          // push integer constant
    LoadFloat(f64),        // push float constant
    LoadLocal(u32),        // push value of local slot
    StoreLocal(u32),       // pop and store into local slot
    Call(SymbolID, usize), // call function name with arg count
    Return,                // return top of stack
}

/// Lowers AST expressions into IR for a single function
#[allow(dead_code)]
pub struct Lowerer {
    instrs: Vec<Instr>,
}

#[allow(dead_code)]
impl Lowerer {
    pub fn lower(source_file: SourceFile<Typed>) -> Vec<Instr> {
        // Generate a main func if one doesn't exist
        let _entry = if let Some(typed_expr) = source_file.typed_roots().iter().find(|expr| {
            matches!(
                expr,
                TypedExpr {
                    expr: Expr::Func(Some(FuncName::Main), _, _, _, _),
                    ..
                }
            )
        }) {
            typed_expr
        } else {
            &TypedExpr::new(
                Expr::Func(Some(FuncName::Main), vec![], vec![], -1, None),
                Ty::Func(vec![], Box::new(Ty::Void)),
            )
        };

        vec![]
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn lowers() {}
}
