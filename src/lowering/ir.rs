use crate::{
    Lowered, SourceFile, SymbolID, SymbolInfo, SymbolKind, Typed,
    expr::{Expr, ExprMeta},
    name::Name,
    parser::ExprID,
    token::Token,
    token_kind::TokenKind,
    type_checker::Ty,
    typed_expr::TypedExpr,
};

#[derive(Debug, Clone)]
pub enum IRError {}

#[derive(Debug, Clone, PartialEq)]
pub struct Register(u32);

#[derive(Debug, Clone, PartialEq)]
pub enum Instr {
    ConstantInt(Register, u64),
    ConstantFloat(Register, f64),
    ConstantBool(Register, bool),
    Add(Register, Register, Register),
    Sub(Register, Register, Register),
    Mul(Register, Register, Register),
    Div(Register, Register, Register),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    Ret(Option<Register>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock {
    pub label: Option<String>,
    pub instructions: Vec<Instr>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRFunction {
    pub name: Name,
    pub blocks: Vec<BasicBlock>,
}

pub struct Lowerer {
    source_file: SourceFile<Typed>,
}

struct RegisterAllocator {
    next_id: u32,
}

impl RegisterAllocator {
    fn new() -> Self {
        Self { next_id: 0 }
    }

    fn allocate(&mut self) -> Register {
        let id = self.next_id;
        self.next_id += 1;
        Register(id)
    }
}

impl Lowerer {
    pub fn new(source_file: SourceFile<Typed>) -> Self {
        Self { source_file }
    }

    pub fn lower(mut self) -> Result<SourceFile<Lowered>, IRError> {
        let main = find_or_create_main(&mut self.source_file);

        let mut functions = vec![];

        functions.push(self.lower_function(&main));

        for root in self.source_file.typed_roots() {
            if let Expr::Func(_, _, _, _, _) = &root.expr {
                functions.push(self.lower_function(&root));
            }
        }

        Ok(self.source_file.to_lowered(functions))
    }

    fn lower_function(&self, typed_expr: &TypedExpr) -> IRFunction {
        let Expr::Func(ref name, _, _, ref body, _) = typed_expr.expr else {
            panic!("Attempted to lower non-function: {:?}", typed_expr);
        };

        let name = match name {
            Some(Name::Resolved(_, _)) => name.clone().unwrap(),
            None => {
                let name = format!("_fn_{:?}", typed_expr.ty);
                let symbol =
                    self.source_file
                        .symbol_table()
                        .add(&name, SymbolKind::CustomType, 12345);
                Name::Resolved(symbol, name)
            }
            _ => todo!(),
        };

        let mut basic_block = BasicBlock {
            label: None,
            instructions: vec![],
            terminator: Terminator::Ret(None),
        };

        let mut registers = RegisterAllocator::new();

        let Some(Expr::Block(body_exprs)) = self.source_file.get(*body) else {
            panic!("did not get body")
        };

        for (i, id) in body_exprs.iter().enumerate() {
            let expr = self
                .source_file
                .typed_expr(id)
                .unwrap_or_else(|| panic!("Did not get expr for id: {}", id));

            let reg = self.lower_expr(&expr, &mut basic_block, &mut registers);

            if i == body_exprs.len() - 1 {
                basic_block.terminator = Terminator::Ret(reg);
            }
        }

        IRFunction {
            name,
            blocks: vec![basic_block],
        }
    }

    fn lower_expr(
        &self,
        typed_expr: &TypedExpr,
        current_block: &mut BasicBlock,
        registers: &mut RegisterAllocator,
    ) -> Option<Register> {
        match &typed_expr.expr {
            Expr::LiteralInt(_)
            | Expr::LiteralFloat(_)
            | Expr::LiteralFalse
            | Expr::LiteralTrue => self.lower_literal(typed_expr, current_block, registers),
            Expr::Binary(lhs, op, rhs) => {
                self.lower_binary_op(&lhs, &op, &rhs, current_block, registers)
            }
            _ => todo!(),
        }
    }

    fn lower_literal(
        &self,
        typed_expr: &TypedExpr,
        current_block: &mut BasicBlock,
        registers: &mut RegisterAllocator,
    ) -> Option<Register> {
        let register = registers.allocate();
        match &typed_expr.expr {
            Expr::LiteralInt(val) => {
                current_block.instructions.push(Instr::ConstantInt(
                    register.clone(),
                    str::parse(val).unwrap(),
                ));
            }
            Expr::LiteralFloat(val) => {
                current_block.instructions.push(Instr::ConstantFloat(
                    register.clone(),
                    str::parse(val).unwrap(),
                ));
            }
            Expr::LiteralFalse => {
                current_block
                    .instructions
                    .push(Instr::ConstantBool(register.clone(), false));
            }
            Expr::LiteralTrue => {
                current_block
                    .instructions
                    .push(Instr::ConstantBool(register.clone(), true));
            }
            _ => unreachable!(),
        }

        Some(register)
    }

    fn lower_binary_op(
        &self,
        lhs: &ExprID,
        op: &TokenKind,
        rhs: &ExprID,
        current_block: &mut BasicBlock,
        registers: &mut RegisterAllocator,
    ) -> Option<Register> {
        let lhs_expr = self.source_file.typed_expr(lhs).unwrap();
        let rhs_expr = self.source_file.typed_expr(rhs).unwrap();
        let operand_1 = self
            .lower_expr(&lhs_expr, current_block, registers)
            .unwrap();
        let operand_2 = self
            .lower_expr(&rhs_expr, current_block, registers)
            .unwrap();
        let return_reg = registers.allocate();

        use TokenKind::*;
        let instr = match op {
            Plus => Instr::Add(return_reg.clone(), operand_1, operand_2),
            Minus => Instr::Sub(return_reg.clone(), operand_1, operand_2),
            Star => Instr::Mul(return_reg.clone(), operand_1, operand_2),
            Slash => Instr::Div(return_reg.clone(), operand_1, operand_2),
            _ => panic!("Cannot lower binary operation: {:?}", op),
        };

        current_block.instructions.push(instr);

        Some(return_reg)
    }
}
fn find_or_create_main(source_file: &mut SourceFile<Typed>) -> TypedExpr {
    for root in source_file.typed_roots() {
        if let TypedExpr {
            expr: Expr::Func(Some(Name::Resolved(_, name)), _, _, _, _),
            ..
        } = root
        {
            if name == "main" {
                return root.clone();
            }
        }
    }

    // We didn't find a main, we have to generate one
    let body = Expr::Block(source_file.root_ids());
    let body_id = source_file.add(
        body,
        ExprMeta {
            start: Token::GENERATED,
            end: Token::GENERATED,
        },
    );

    let func_expr = Expr::Func(
        Some(Name::Resolved(SymbolID::GENERATED_MAIN, "main".into())),
        vec![],
        vec![],
        body_id,
        None,
    );

    source_file.set(
        SymbolID::GENERATED_MAIN,
        SymbolInfo {
            name: "main".into(),
            kind: SymbolKind::Func,
            expr_id: SymbolID::GENERATED_MAIN.0,
        },
    );

    TypedExpr {
        expr: func_expr,
        ty: Ty::Func(vec![], Box::new(Ty::Void)),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Lowered, SourceFile, SymbolID, check,
        lowering::ir::{BasicBlock, IRError, IRFunction, Instr, Lowerer, Register, Terminator},
        name::Name,
    };

    fn lower(input: &'static str) -> Result<SourceFile<Lowered>, IRError> {
        let typed = check(input).unwrap();
        let lowerer = Lowerer::new(typed);
        lowerer.lower()
    }

    #[test]
    fn lowers_int() {
        let lowered = lower("123").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![IRFunction {
                name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                blocks: vec![BasicBlock {
                    label: None,
                    instructions: vec![Instr::ConstantInt(Register(0), 123)],
                    terminator: Terminator::Ret(Some(Register(0)))
                }]
            }]
        )
    }

    #[test]
    fn lowers_float() {
        let lowered = lower("123.").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![IRFunction {
                name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                blocks: vec![BasicBlock {
                    label: None,
                    instructions: vec![Instr::ConstantFloat(Register(0), 123.)],
                    terminator: Terminator::Ret(Some(Register(0)))
                }]
            }]
        )
    }

    #[test]
    fn lowers_bools() {
        let lowered = lower("true\nfalse").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![IRFunction {
                name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                blocks: vec![BasicBlock {
                    label: None,
                    instructions: vec![
                        Instr::ConstantBool(Register(0), true),
                        Instr::ConstantBool(Register(1), false),
                    ],
                    terminator: Terminator::Ret(Some(Register(1)))
                }]
            }]
        )
    }

    #[test]
    fn lowers_add() {
        let lowered = lower("1 + 2").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![IRFunction {
                name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                blocks: vec![BasicBlock {
                    label: None,
                    instructions: vec![
                        Instr::ConstantInt(Register(0), 1),
                        Instr::ConstantInt(Register(1), 2),
                        Instr::Add(Register(2), Register(0), Register(1))
                    ],
                    terminator: Terminator::Ret(Some(Register(2)))
                }]
            }]
        )
    }

    #[test]
    fn lowers_sub() {
        let lowered = lower("2 - 1").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![IRFunction {
                name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                blocks: vec![BasicBlock {
                    label: None,
                    instructions: vec![
                        Instr::ConstantInt(Register(0), 2),
                        Instr::ConstantInt(Register(1), 1),
                        Instr::Sub(Register(2), Register(0), Register(1))
                    ],
                    terminator: Terminator::Ret(Some(Register(2)))
                }]
            }]
        )
    }

    #[test]
    fn lowers_mul() {
        let lowered = lower("2 * 1").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![IRFunction {
                name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                blocks: vec![BasicBlock {
                    label: None,
                    instructions: vec![
                        Instr::ConstantInt(Register(0), 2),
                        Instr::ConstantInt(Register(1), 1),
                        Instr::Mul(Register(2), Register(0), Register(1))
                    ],
                    terminator: Terminator::Ret(Some(Register(2)))
                }]
            }]
        )
    }

    #[test]
    fn lowers_div() {
        let lowered = lower("2 / 1").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![IRFunction {
                name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                blocks: vec![BasicBlock {
                    label: None,
                    instructions: vec![
                        Instr::ConstantInt(Register(0), 2),
                        Instr::ConstantInt(Register(1), 1),
                        Instr::Div(Register(2), Register(0), Register(1))
                    ],
                    terminator: Terminator::Ret(Some(Register(2)))
                }]
            }]
        )
    }
}
