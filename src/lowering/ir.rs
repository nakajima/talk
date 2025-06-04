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

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub struct Register(u32);

#[derive(Debug, Clone, PartialEq)]
pub enum RefKind {
    Func(SymbolID),
}

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
    Phi(Register, Vec<(Register, BasicBlockID)>),
    Ref(Register, RefKind),
    Call {
        dest_reg: Option<Register>,
        callee: SymbolID,
        args: Vec<Register>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    Ret(Option<Register>),
    Unreachable,
    Jump(BasicBlockID),
    JumpUnless(Register, BasicBlockID),
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

impl BasicBlock {
    fn push_instr(&mut self, instr: Instr) {
        self.instructions.push(instr)
    }
}

struct CurrentFunction {
    current_block_idx: usize,
    blocks: Vec<BasicBlock>,
    pub registers: RegisterAllocator,
    pub symbol_registers: HashMap<SymbolID, Register>,
}

impl CurrentFunction {
    #[track_caller]
    fn new() -> Self {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!("new CurrentFunction from {}:{}", loc.file(), loc.line());
        }
        Self {
            current_block_idx: 0,
            blocks: Default::default(),
            registers: RegisterAllocator::new(),
            symbol_registers: Default::default(),
        }
    }

    fn add_block(&mut self, block: BasicBlock) {
        self.blocks.push(block);
    }

    fn current_block_mut(&mut self) -> &mut BasicBlock {
        &mut self.blocks[self.current_block_idx]
    }

    fn set_current_block(&mut self, id: BasicBlockID) {
        let index = self.blocks.iter().position(|blk| blk.id == id).unwrap();
        self.current_block_idx = index;
    }

    #[track_caller]
    fn register_symbol(&mut self, symbol_id: SymbolID, register: Register) {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "register symbol {:?}: {:?} from {}:{}",
                symbol_id,
                register,
                loc.file(),
                loc.line()
            );
        }
        self.symbol_registers.insert(symbol_id, register);
    }

    fn lookup_symbol(&self, symbol_id: &SymbolID) -> &Register {
        self.symbol_registers
            .get(symbol_id)
            .unwrap_or_else(|| panic!("No register found for symbol: {:?}", symbol_id))
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
        log::trace!("new register allocator");
        Self { next_id: 0 }
    }

    fn allocate(&mut self) -> Register {
        let id = self.next_id;
        self.next_id += 1;
        Register(id)
    }
}

pub struct Lowerer {
    next_block_id: BasicBlockID,
    source_file: SourceFile<Typed>,
    current_functions: Vec<CurrentFunction>,
    lowered_functions: Vec<IRFunction>,
}

impl Lowerer {
    pub fn new(source_file: SourceFile<Typed>) -> Self {
        Self {
            next_block_id: BasicBlockID::default(),
            source_file,
            current_functions: vec![],
            lowered_functions: Default::default(),
        }
    }

    pub fn lower(mut self) -> Result<SourceFile<Lowered>, IRError> {
        let (expr_id, did_create) = find_or_create_main(&mut self.source_file);

        self.lower_function(&expr_id);

        // If we created the main function, we moved all the typed roots into its body
        // so we don't need to lower them again.
        if !did_create {
            let typed_roots = self.source_file.typed_roots().to_owned();
            for root in typed_roots {
                if let Expr::Func { .. } = &root.expr {
                    self.lower_function(&root.id);
                }
            }
        }

        Ok(self.source_file.to_lowered(self.lowered_functions))
    }

    fn next_block_id(&mut self) -> BasicBlockID {
        let id = self.next_block_id;
        self.next_block_id += 1;
        id
    }

    fn lower_function(&mut self, expr_id: &ExprID) -> SymbolID {
        let typed_expr = self
            .source_file
            .typed_expr(expr_id)
            .expect("Did not get typed expr");

        let Expr::Func {
            ref name,
            ref params,
            ref body,
            ..
        } = typed_expr.expr
        else {
            panic!(
                "Attempted to lower non-function: {:?}",
                self.source_file.get(*expr_id)
            );
        };

        self.current_functions.push(CurrentFunction::new());

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

        log::trace!("lowering {:?}", name);

        let Some(Expr::Block(body_exprs)) = self.source_file.get(*body).cloned() else {
            panic!("did not get body")
        };

        self.new_basic_block();

        for param in params {
            let Expr::Parameter(Name::Resolved(symbol, _), _) =
                self.source_file.get(*param).unwrap().clone()
            else {
                panic!("didn't get parameter")
            };

            let register = self.current_func_mut().registers.allocate();
            self.current_func_mut().register_symbol(symbol, register);
        }

        for (i, id) in body_exprs.iter().enumerate() {
            let reg = self.lower_expr(&id);

            if i == body_exprs.len() - 1 {
                self.current_block_mut().terminator = Terminator::Ret(reg);
            }
        }

        let func = IRFunction {
            name: name.clone(),
            blocks: self.current_func_mut().blocks.clone(),
        };
        self.lowered_functions.push(func.clone());
        self.current_functions.pop();

        let Name::Resolved(symbol, _) = name else {
            panic!("no symbol")
        };
        symbol
    }

    fn lower_expr(&mut self, expr_id: &ExprID) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id).unwrap().clone();
        match typed_expr.expr {
            Expr::LiteralInt(_)
            | Expr::LiteralFloat(_)
            | Expr::LiteralFalse
            | Expr::LiteralTrue => self.lower_literal(expr_id),
            Expr::Binary(lhs, op, rhs) => self.lower_binary_op(&lhs, &op, &rhs),
            Expr::Assignment(lhs, rhs) => self.lower_assignment(&lhs, &rhs),
            Expr::Variable(name, _) => self.lower_variable(&name),
            Expr::If(cond, conseq, alt) => self.lower_if(&cond, &conseq, &alt),
            Expr::Block(_) => self.lower_block(expr_id),
            Expr::Call(callee, args) => self.lower_call(callee, args, typed_expr.ty),
            Expr::Func { .. } => {
                let symbol_id = self.lower_function(expr_id);
                let reg = self.current_func_mut().registers.allocate();
                self.current_func_mut().register_symbol(symbol_id, reg);
                self.current_block_mut()
                    .push_instr(Instr::Ref(reg, RefKind::Func(symbol_id)));
                Some(reg)
            }
            expr => todo!("Cannot lower {:?}", expr),
        }
    }

    fn lower_literal(&mut self, expr_id: &ExprID) -> Option<Register> {
        let register = self.current_func_mut().registers.allocate();
        match self.source_file.get(*expr_id).unwrap().clone() {
            Expr::LiteralInt(val) => {
                self.current_block_mut().push_instr(Instr::ConstantInt(
                    register.clone(),
                    str::parse(&val).unwrap(),
                ));
            }
            Expr::LiteralFloat(val) => {
                self.current_block_mut().push_instr(Instr::ConstantFloat(
                    register.clone(),
                    str::parse(&val).unwrap(),
                ));
            }
            Expr::LiteralFalse => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantBool(register.clone(), false));
            }
            Expr::LiteralTrue => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantBool(register.clone(), true));
            }
            _ => unreachable!(),
        }

        Some(register)
    }

    fn lower_binary_op(&mut self, lhs: &ExprID, op: &TokenKind, rhs: &ExprID) -> Option<Register> {
        let operand_1 = self.lower_expr(&lhs).unwrap();
        let operand_2 = self.lower_expr(&rhs).unwrap();
        let return_reg = self.current_func_mut().registers.allocate();

        use TokenKind::*;
        let instr = match op {
            Plus => Instr::Add(return_reg.clone(), operand_1, operand_2),
            Minus => Instr::Sub(return_reg.clone(), operand_1, operand_2),
            Star => Instr::Mul(return_reg.clone(), operand_1, operand_2),
            Slash => Instr::Div(return_reg.clone(), operand_1, operand_2),
            _ => panic!("Cannot lower binary operation: {:?}", op),
        };

        self.current_block_mut().push_instr(instr);

        Some(return_reg)
    }

    fn lower_assignment(&mut self, lhs: &ExprID, rhs: &ExprID) -> Option<Register> {
        let rhs = self
            .lower_expr(rhs)
            .expect("Did not get rhs for assignment");

        match self.source_file.get(*lhs).unwrap().clone() {
            Expr::Let(Name::Resolved(symbol_id, _), _) => {
                self.current_func_mut().register_symbol(symbol_id, rhs);
                None
            }
            _ => todo!(),
        }
    }

    fn lower_block(&mut self, block_id: &ExprID) -> Option<Register> {
        let Expr::Block(exprs) = self.source_file.get(*block_id).unwrap().clone() else {
            unreachable!()
        };

        if exprs.is_empty() {
            return None;
        }

        for (i, id) in exprs.iter().enumerate() {
            let reg = self.lower_expr(id);
            if i == exprs.len() - 1 {
                return reg;
            }
        }

        None
    }

    fn lower_variable(&mut self, name: &Name) -> Option<Register> {
        let Name::Resolved(symbol_id, _) = name else {
            panic!("Unresolved variable: {:?}", name)
        };

        Some(*self.current_func_mut().lookup_symbol(symbol_id))
    }

    fn lower_if(
        &mut self,
        cond: &ExprID,
        conseq: &ExprID,
        alt: &Option<ExprID>,
    ) -> Option<Register> {
        let cond_reg = self
            .lower_expr(cond)
            .expect("Condition for if expression did not produce a value");

        let then_id = self.new_basic_block();
        let mut else_reg: Option<Register> = None;
        let else_id: Option<BasicBlockID> = if alt.is_some() {
            Some(self.new_basic_block())
        } else {
            None
        };
        let merge_id = self.new_basic_block(); // All paths merge here

        self.current_block_mut().terminator =
            Terminator::JumpUnless(cond_reg, else_id.unwrap_or(merge_id));

        self.set_current_block(then_id);
        let then_reg = self.lower_expr(conseq).unwrap();
        self.current_block_mut().terminator = Terminator::Jump(merge_id);

        if let Some(alt) = alt {
            self.set_current_block(else_id.unwrap());
            else_reg = self.lower_expr(alt);
            self.current_block_mut().terminator = Terminator::Jump(merge_id);
        }

        self.current_func_mut().set_current_block(merge_id);

        let phi_dest_reg = self.current_func_mut().registers.allocate();

        self.current_block_mut().push_instr(Instr::Phi(
            phi_dest_reg.clone(),
            vec![
                (then_reg, then_id),                   // Value from 'then' path came from then_bb
                (else_reg.unwrap(), else_id.unwrap()), // Value from 'else' path came from else_bb
            ],
        ));

        Some(phi_dest_reg)
    }

    fn lower_call(&mut self, callee: ExprID, args: Vec<ExprID>, ty: Ty) -> Option<Register> {
        let mut arg_registers = vec![];
        for arg in args {
            if let Some(arg_reg) = self.lower_expr(&arg) {
                arg_registers.push(arg_reg);
            } else {
                // This would happen if an argument expression doesn't produce a value.
                // Depending on your language, this might be an error or indicate a void arg,
                // though void args are uncommon.
                panic!("Argument expression did not produce a value for call");
            }
        }

        let callee_typed_expr = self.source_file.typed_expr(&callee).unwrap();
        let func_symbol_id = match &callee_typed_expr.expr {
            Expr::Variable(Name::Resolved(symbol_id, _), _) => {
                // Check if the type of this variable is indeed a function
                if !matches!(callee_typed_expr.ty, Ty::Func(_, _)) {
                    panic!(
                        "Attempting to call a non-function variable: {:?}",
                        callee_typed_expr
                    );
                }
                *symbol_id
            }
            // Later, you might handle other forms of callees, like Expr::Member for methods,
            // or expressions that evaluate to function pointers/closures.
            _ => panic!(
                "Unsupported callee expression type: {:?}",
                callee_typed_expr.expr
            ),
        };

        // 3. Allocate Destination Register for Return Value (if not void)
        let dest_reg: Option<Register>;
        match ty {
            Ty::Void => {
                // Assuming you have a Ty::Void or similar
                dest_reg = None;
            }
            _ => {
                // Any other type means it returns a value
                dest_reg = Some(self.current_func_mut().registers.allocate());
            }
        }

        self.current_block_mut().push_instr(Instr::Call {
            dest_reg: dest_reg, // clone if Register is Copy, else it's fine
            callee: func_symbol_id,
            args: arg_registers,
        });

        // 5. Return the destination register
        dest_reg
    }

    fn current_func_mut(&mut self) -> &mut CurrentFunction {
        self.current_functions.last_mut().unwrap()
    }

    fn current_block_mut(&mut self) -> &mut BasicBlock {
        self.current_func_mut().current_block_mut()
    }

    fn set_current_block(&mut self, id: BasicBlockID) {
        self.current_func_mut().set_current_block(id);
    }

    fn new_basic_block(&mut self) -> BasicBlockID {
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

        self.current_func_mut().add_block(block);
        id
    }
}

fn find_or_create_main(source_file: &mut SourceFile<Typed>) -> (ExprID, bool) {
    for root in source_file.typed_roots() {
        if let TypedExpr {
            expr:
                Expr::Func {
                    name: Some(Name::Resolved(_, name)),
                    ..
                },
            ..
        } = root
        {
            if name == "main" {
                return (root.id, false);
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

    let func_expr = Expr::Func {
        name: Some(Name::Resolved(SymbolID::GENERATED_MAIN, "main".into())),
        generics: vec![],
        params: vec![],
        body: body_id,
        ret: None,
    };

    source_file.set_typed_expr(
        SymbolID::GENERATED_MAIN.0,
        TypedExpr {
            id: SymbolID::GENERATED_MAIN.0,
            expr: func_expr.clone(),
            ty: Ty::Func(vec![], Box::new(Ty::Void)),
        },
    );

    source_file.add(
        func_expr.clone(),
        ExprMeta {
            start: Token::GENERATED,
            end: Token::GENERATED,
        },
    );

    source_file.set(
        SymbolID::GENERATED_MAIN,
        SymbolInfo {
            name: "main".into(),
            kind: SymbolKind::Func,
            expr_id: SymbolID::GENERATED_MAIN.0,
        },
    );

    (SymbolID::GENERATED_MAIN.0, true)
}

#[cfg(test)]
mod tests {
    use crate::{
        Lowered, SourceFile, SymbolID, check,
        lowering::ir::{
            BasicBlock, BasicBlockID, IRError, IRFunction, Instr, Lowerer, RefKind, Register,
            Terminator,
        },
        name::Name,
    };

    fn lower(input: &'static str) -> Result<SourceFile<Lowered>, IRError> {
        let typed = check(input).unwrap();
        let lowerer = Lowerer::new(typed);
        lowerer.lower()
    }

    #[test]
    fn lowers_nested_function() {
        let lowered = lower("func foo() { 123 }").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![
                IRFunction {
                    name: Name::Resolved(SymbolID::at(1), "foo".into()),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(1),
                        label: Some("bb1".into()),
                        instructions: vec![Instr::ConstantInt(Register(0), 123)],
                        terminator: Terminator::Ret(Some(Register(0)))
                    }]
                },
                IRFunction {
                    name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        label: None,
                        instructions: vec![Instr::Ref(Register(0), RefKind::Func(SymbolID(5)))],
                        terminator: Terminator::Ret(Some(Register(0)))
                    }]
                },
            ]
        )
    }

    #[test]
    fn lowers_calls() {
        let lowered = lower("func foo(x) { x }\n foo(123)").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![
                IRFunction {
                    name: Name::Resolved(SymbolID::at(1), "foo".into()),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(1),
                        label: Some("bb1".into()),
                        instructions: vec![],
                        terminator: Terminator::Ret(Some(Register(0)))
                    }]
                },
                IRFunction {
                    name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        label: None,
                        instructions: vec![
                            Instr::Ref(Register(0), RefKind::Func(SymbolID(5))),
                            Instr::ConstantInt(Register(1), 123),
                            Instr::Call {
                                dest_reg: Some(Register(2)),
                                callee: SymbolID::at(1),
                                args: vec![Register(1)]
                            }
                        ],
                        terminator: Terminator::Ret(Some(Register(2)))
                    }]
                },
            ]
        )
    }

    #[test]
    fn lowers_func_with_params() {
        let lowered = lower("func foo(x) { x }").unwrap();
        assert_eq!(
            lowered.functions(),
            vec![
                IRFunction {
                    name: Name::Resolved(SymbolID::at(1), "foo".into()),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(1),
                        label: Some("bb1".into()),
                        instructions: vec![],
                        terminator: Terminator::Ret(Some(Register(0)))
                    }]
                },
                IRFunction {
                    name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        label: None,
                        instructions: vec![Instr::Ref(Register(0), RefKind::Func(SymbolID(5)))],
                        terminator: Terminator::Ret(Some(Register(0)))
                    }]
                },
            ]
        )
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

    #[test]
    fn lowers_if_expr_with_else() {
        let lowered = lower(
            "
            if true {
                123
            } else {
                456
            }

            789
       ",
        )
        .unwrap();

        let expected = vec![IRFunction {
            name: Name::Resolved(SymbolID::GENERATED_MAIN, "main".into()),
            blocks: vec![
                // if block
                BasicBlock {
                    id: BasicBlockID(0),
                    label: None,
                    instructions: vec![Instr::ConstantBool(Register(0), true)],
                    terminator: Terminator::JumpUnless(Register(0), BasicBlockID(2)),
                },
                // consequence block
                BasicBlock {
                    id: BasicBlockID(1),
                    label: Some("bb1".into()),
                    instructions: vec![Instr::ConstantInt(Register(1), 123)],
                    terminator: Terminator::Jump(BasicBlockID(3)),
                },
                // else block
                BasicBlock {
                    id: BasicBlockID(2),
                    label: Some("bb2".into()),
                    instructions: vec![Instr::ConstantInt(Register(2), 456)],
                    terminator: Terminator::Jump(BasicBlockID(3)),
                },
                // converge block
                BasicBlock {
                    id: BasicBlockID(3),
                    label: Some("bb3".into()),
                    instructions: vec![
                        Instr::Phi(
                            Register(3),
                            vec![
                                (Register(1), BasicBlockID(1)),
                                (Register(2), BasicBlockID(2)),
                            ],
                        ),
                        Instr::ConstantInt(Register(4), 789),
                    ],
                    terminator: Terminator::Ret(Some(Register(4))),
                },
            ],
        }];

        assert_eq!(
            lowered.functions(),
            expected,
            "{:#?} \n ========== {:#?}",
            lowered.functions(),
            expected
        );
    }
}
