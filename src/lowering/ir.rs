use std::{collections::HashMap, ops::AddAssign};

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

#[derive(Debug, Clone, Copy, PartialEq)]
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
    StoreLocal(Register, Register),
    LoadLocal(Register, Register),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    Ret(Option<Register>),
    Unreachable,
}

#[derive(Default, Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub struct BasicBlockID(u32);

impl AddAssign<u32> for BasicBlockID {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock {
    pub id: BasicBlockID,
    pub label: Option<String>,
    pub instructions: Vec<Instr>,
    pub terminator: Terminator,
}

#[derive(Default)]
struct CurrentFunction {
    current_function_id: BasicBlockID,
    blocks: HashMap<BasicBlockID, BasicBlock>,
}

impl CurrentFunction {
    fn push_instr(&mut self, instr: Instr) {
        let id = &self.current_function_id;
        self.blocks.get_mut(id).unwrap().instructions.push(instr)
    }

    fn add_block(&mut self, id: &BasicBlockID, instr: BasicBlock) {
        self.blocks.insert(*id, instr);
    }

    fn current_block_mut(&mut self) -> &mut BasicBlock {
        let id = &self.current_function_id;
        self.blocks.get_mut(id).unwrap()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRFunction {
    pub name: Name,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
struct ScopeContext {
    pub registers: RegisterAllocator,
    pub symbol_registers: HashMap<SymbolID, Register>,
}

impl ScopeContext {
    pub fn new() -> Self {
        Self {
            registers: RegisterAllocator::new(),
            symbol_registers: Default::default(),
        }
    }

    fn register_symbol(&mut self, symbol_id: SymbolID, register: Register) {
        self.symbol_registers.insert(symbol_id, register);
    }

    fn lookup_symbol(&self, symbol_id: &SymbolID) -> &Register {
        &self
            .symbol_registers
            .get(symbol_id)
            .expect("No register found for symbol")
    }
}

pub struct Lowerer {
    next_block_id: BasicBlockID,
    source_file: SourceFile<Typed>,
    current_function: CurrentFunction,
}

impl Lowerer {
    pub fn new(source_file: SourceFile<Typed>) -> Self {
        Self {
            next_block_id: BasicBlockID::default(),
            source_file,
            current_function: CurrentFunction::default(),
        }
    }

    pub fn lower(mut self) -> Result<SourceFile<Lowered>, IRError> {
        let main = find_or_create_main(&mut self.source_file);

        let mut functions = vec![];

        functions.push(self.lower_function(&main));

        let typed_roots = self.source_file.typed_roots().to_owned();
        for root in typed_roots {
            if let Expr::Func(_, _, _, _, _) = &root.expr {
                functions.push(self.lower_function(&root));
            }
        }

        Ok(self.source_file.to_lowered(functions))
    }

    fn next_block_id(&mut self) -> BasicBlockID {
        let id = self.next_block_id;
        self.next_block_id += 1;
        id
    }

    fn lower_function(&mut self, typed_expr: &TypedExpr) -> IRFunction {
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

        let Some(Expr::Block(body_exprs)) = self.source_file.get(*body).cloned() else {
            panic!("did not get body")
        };

        self.new_basic_block();
        let mut context = ScopeContext::new();

        for (i, id) in body_exprs.iter().enumerate() {
            let reg = self.lower_expr(&id, &mut context);

            if i == body_exprs.len() - 1 {
                self.current_function.current_block_mut().terminator = Terminator::Ret(reg);
            }
        }

        IRFunction {
            name,
            blocks: self
                .current_function
                .blocks
                .values()
                .map(|b| b.to_owned())
                .collect(),
        }
    }

    fn lower_expr(&mut self, expr_id: &ExprID, context: &mut ScopeContext) -> Option<Register> {
        match self.source_file.get(*expr_id).unwrap().clone() {
            Expr::LiteralInt(_)
            | Expr::LiteralFloat(_)
            | Expr::LiteralFalse
            | Expr::LiteralTrue => self.lower_literal(expr_id, context),
            Expr::Binary(lhs, op, rhs) => self.lower_binary_op(&lhs, &op, &rhs, context),
            Expr::Assignment(lhs, rhs) => self.lower_assignment(&lhs, &rhs, context),
            Expr::Variable(name, _) => self.lower_variable(&name, context),
            Expr::If(cond, conseq, alt) => self.lower_if(&cond, &conseq, &alt, context),
            expr => todo!("Cannot lower {:?}", expr),
        }
    }

    fn lower_literal(&mut self, expr_id: &ExprID, context: &mut ScopeContext) -> Option<Register> {
        let register = context.registers.allocate();
        match self.source_file.get(*expr_id).unwrap() {
            Expr::LiteralInt(val) => {
                self.current_function.push_instr(Instr::ConstantInt(
                    register.clone(),
                    str::parse(val).unwrap(),
                ));
            }
            Expr::LiteralFloat(val) => {
                self.current_function.push_instr(Instr::ConstantFloat(
                    register.clone(),
                    str::parse(val).unwrap(),
                ));
            }
            Expr::LiteralFalse => {
                self.current_function
                    .push_instr(Instr::ConstantBool(register.clone(), false));
            }
            Expr::LiteralTrue => {
                self.current_function
                    .push_instr(Instr::ConstantBool(register.clone(), true));
            }
            _ => unreachable!(),
        }

        Some(register)
    }

    fn lower_binary_op(
        &mut self,
        lhs: &ExprID,
        op: &TokenKind,
        rhs: &ExprID,
        context: &mut ScopeContext,
    ) -> Option<Register> {
        let operand_1 = self.lower_expr(&lhs, context).unwrap();
        let operand_2 = self.lower_expr(&rhs, context).unwrap();
        let return_reg = context.registers.allocate();

        use TokenKind::*;
        let instr = match op {
            Plus => Instr::Add(return_reg.clone(), operand_1, operand_2),
            Minus => Instr::Sub(return_reg.clone(), operand_1, operand_2),
            Star => Instr::Mul(return_reg.clone(), operand_1, operand_2),
            Slash => Instr::Div(return_reg.clone(), operand_1, operand_2),
            _ => panic!("Cannot lower binary operation: {:?}", op),
        };

        self.current_function.push_instr(instr);

        Some(return_reg)
    }

    fn lower_assignment(
        &mut self,
        lhs: &ExprID,
        rhs: &ExprID,
        context: &mut ScopeContext,
    ) -> Option<Register> {
        let rhs = self
            .lower_expr(rhs, context)
            .expect("Did not get rhs for assignment");

        match self.source_file.get(*lhs).unwrap() {
            Expr::Let(Name::Resolved(symbol_id, _), _) => {
                context.register_symbol(*symbol_id, rhs);
                None
            }
            _ => todo!(),
        }
    }

    fn lower_variable(&mut self, name: &Name, context: &mut ScopeContext) -> Option<Register> {
        let Name::Resolved(symbol_id, _) = name else {
            panic!("Unresolved variable: {:?}", name)
        };

        Some(*context.lookup_symbol(symbol_id))
    }

    fn lower_if(
        &mut self,
        cond: &ExprID,
        conseq: &ExprID,
        alt: &Option<ExprID>,
        context: &mut ScopeContext,
    ) -> Option<Register> {
        let cond_reg = self
            .lower_expr(cond, context)
            .expect("Condition for if expression did not produce a value");

        let then_bb_id = self.new_basic_block();
        let mut else_bb_id_opt: Option<BasicBlockID> = None;
        let merge_bb_id = self.new_basic_block(); // All paths merge here

        None
    }

    fn new_basic_block(&mut self) -> &mut BasicBlock {
        let id = self.next_block_id();
        let block = BasicBlock {
            id,
            label: if id.0 > 0 {
                // give additional blocks default labels
                Some(format!("bb{}", id.0))
            } else {
                None
            },
            instructions: Vec::new(),
            terminator: Terminator::Unreachable, // Placeholder, must be set before block is "done"
        };

        self.current_function.add_block(&id, block);
        self.current_function.current_block_mut()
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
        lowering::ir::{
            BasicBlock, BasicBlockID, IRError, IRFunction, Instr, Lowerer, Register, Terminator,
        },
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
                    id: BasicBlockID(0),
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
                    id: BasicBlockID(0),
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
                    id: BasicBlockID(0),
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
                    id: BasicBlockID(0),
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
                    id: BasicBlockID(0),
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
                    id: BasicBlockID(0),
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
                    id: BasicBlockID(0),
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

    #[test]
    fn lowers_assignment() {
        let lowered = lower("let a = 123\na").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![IRFunction {
                name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    label: None,
                    instructions: vec![Instr::ConstantInt(Register(0), 123),],
                    terminator: Terminator::Ret(Some(Register(0)))
                }]
            }]
        )
    }
}
