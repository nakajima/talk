use std::fmt::Display;

use itertools::Itertools;

use crate::{
    ir::{
        basic_block::{BasicBlock, BasicBlockId, Phi},
        function::Function,
        instruction::{CmpOperator, Instruction},
        ir_ty::IrTy,
        program::Program,
        register::Register,
        terminator::Terminator,
    },
    label::Label,
    name_resolution::symbol::Symbol,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Reference {
    Func(Symbol),
    Register { frame: usize, register: Register },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Record(Option<Symbol>, Vec<Value>),
    Func(Symbol),
    Void,
    Ref(Reference),
    RawPtr(usize),
    Buffer(Vec<u8>),
    Uninit,
}

#[allow(clippy::panic)]
#[allow(clippy::should_implement_trait)]
impl Value {
    pub fn add(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Int(lhs + rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Float(lhs + rhs),
            _ => panic!("can't add {self:?} and {other:?}"),
        }
    }
    pub fn sub(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Int(lhs - rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Float(lhs - rhs),
            _ => panic!("can't sub {self:?} and {other:?}"),
        }
    }
    pub fn mul(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Int(lhs * rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Float(lhs * rhs),
            _ => panic!("can't mul {self:?} and {other:?}"),
        }
    }
    pub fn div(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Int(lhs / rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Float(lhs / rhs),
            _ => panic!("can't div {self:?} and {other:?}"),
        }
    }
    pub fn gt(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Bool(lhs > rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Bool(lhs > rhs),
            _ => panic!("can't compare {self:?} > {other:?}"),
        }
    }
    pub fn gte(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Bool(lhs >= rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Bool(lhs >= rhs),
            _ => panic!("can't compare {self:?} > {other:?}"),
        }
    }
    pub fn lt(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Bool(lhs < rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Bool(lhs < rhs),
            _ => panic!("can't compare {self:?} > {other:?}"),
        }
    }
    pub fn lte(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Bool(lhs <= rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Bool(lhs <= rhs),
            _ => panic!("can't compare {self:?} > {other:?}"),
        }
    }
    pub fn eq(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Bool(lhs == rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Bool(lhs == rhs),
            (Self::Bool(lhs), Self::Bool(rhs)) => Self::Bool(lhs == rhs),
            _ => panic!("can't compare {self:?} == {other:?}"),
        }
    }
    pub fn ne(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Bool(lhs != rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Bool(lhs != rhs),
            (Self::Bool(lhs), Self::Bool(rhs)) => Self::Bool(lhs != rhs),
            _ => panic!("can't compare {self:?} > {other:?}"),
        }
    }
}

impl BasicBlock<IrTy> {
    fn next_ir(&self, idx: usize) -> IR {
        if idx >= self.phis.len() + self.instructions.len() {
            return IR::Term(self.terminator.clone());
        }

        if idx >= self.phis.len() {
            return IR::Instr(self.instructions[idx - self.phis.len()].clone());
        }

        IR::Phi(self.phis[idx].clone())
    }
}

#[derive(Debug)]
pub struct Frame {
    dest: Register,
    ret: Option<Symbol>,
    registers: Vec<Value>,
    pc: usize,
    current_block: usize,
    prev_block: Option<usize>,
}

impl Frame {
    pub fn new(dest: Register, ret: Option<Symbol>) -> Self {
        Self {
            ret,
            dest,
            registers: Default::default(),
            pc: 0,
            current_block: 0,
            prev_block: None,
        }
    }
}

enum IR {
    Phi(Phi<IrTy>),
    Instr(Instruction<IrTy>),
    Term(Terminator<IrTy>),
}

impl Display for IR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IR::Phi(phi) => write!(f, "{phi}"),
            IR::Instr(instr) => write!(f, "{instr}"),
            IR::Term(term) => write!(f, "{term}"),
        }
    }
}

#[derive(Default)]
pub struct Heap {
    mem: Vec<Value>,
    next_addr: usize,
}

pub struct Interpreter {
    program: Program,
    frames: Vec<Frame>,
    current_func: Option<Function<IrTy>>,
    main_result: Option<Value>,
    heap: Heap,
}

#[allow(clippy::unwrap_used)]
#[allow(clippy::expect_used)]
#[allow(clippy::panic)]
impl Interpreter {
    pub fn new(program: Program) -> Self {
        if std::env::var("SHOW_IR").is_ok() {
            println!("{program}");
        }

        Self {
            program,
            frames: Default::default(),
            current_func: None,
            main_result: None,
            heap: Default::default(),
        }
    }

    pub fn run(mut self) -> Value {
        #[allow(clippy::expect_used)]
        let entrypoint = self
            .program
            .entrypoint()
            .expect("No entrypoint found for program.");

        self.call(entrypoint.name.symbol().unwrap(), vec![], Register::MAIN);

        while !self.frames.is_empty() {
            self.next();
        }

        self.main_result.unwrap_or(Value::Void)
    }

    pub fn call(&mut self, function: Symbol, args: Vec<Value>, dest: Register) {
        let caller_name = self.current_func.as_ref().map(|f| f.name.symbol().unwrap());
        if let Some(callee_func) = self.current_func.take() {
            self.program
                .functions
                .insert(callee_func.name.symbol().unwrap(), callee_func);
        }

        let func = self
            .program
            .functions
            .shift_remove(&function)
            .unwrap_or_else(|| {
                panic!(
                    "did not find function: {:?} {:?}",
                    function,
                    self.program
                        .functions
                        .iter()
                        .map(|f| &f.1.name)
                        .collect_vec()
                )
            });
        let mut frame = Frame::new(dest, caller_name);
        frame.registers.resize(func.register_count, Value::Uninit);
        for (i, arg) in args.into_iter().enumerate() {
            frame.registers[i] = arg;
        }
        self.frames.push(frame);
        self.current_func = Some(func);

        tracing::trace!("{:?}", self.frames.last().unwrap());
    }

    pub fn next(&mut self) {
        let next_instruction = self.next_instr();

        tracing::trace!("{next_instruction}");

        match next_instruction {
            IR::Phi(phi) => {
                let prev = self.frames.last().unwrap().prev_block.unwrap();
                let source = phi
                    .sources
                    .items
                    .iter()
                    .find(|s| s.from_id == BasicBlockId(prev as u32))
                    .unwrap();
                let val = self.val(source.value.clone());
                self.write_register(&phi.dest, val);
            }
            IR::Term(Terminator::Ret { val, .. }) => {
                let val = self.val(val);
                let frame = self.frames.pop().unwrap();

                self.write_register(&frame.dest, val);

                let Some(func) = self.current_func.take() else {
                    unreachable!("but where did the frame come from");
                };

                self.program
                    .functions
                    .insert(func.name.symbol().unwrap(), func);

                if let Some(ret) = frame.ret {
                    let ret_func = self.program.functions.shift_remove(&ret).unwrap();
                    self.current_func = Some(ret_func);
                }
            }
            IR::Term(Terminator::Unreachable) => panic!("Reached unreachable"),
            IR::Term(Terminator::Branch { cond, conseq, alt }) => {
                let cond_val = self.val(cond);
                let next_block = if cond_val == Value::Bool(true) {
                    conseq
                } else {
                    alt
                };

                self.jump(next_block);
            }
            IR::Term(Terminator::Jump { to }) => self.jump(to),
            IR::Instr(Instruction::Constant { dest, val, .. }) => {
                let val = self.val(val);
                self.write_register(&dest, val);
            }
            IR::Instr(Instruction::Add { dest, a, b, .. }) => {
                let result = self.val(a).add(self.val(b));
                self.write_register(&dest, result);
            }
            IR::Instr(Instruction::Sub { dest, a, b, .. }) => {
                let result = self.val(a).sub(self.val(b));
                self.write_register(&dest, result);
            }
            IR::Instr(Instruction::Mul { dest, a, b, .. }) => {
                let result = self.val(a).mul(self.val(b));
                self.write_register(&dest, result);
            }
            IR::Instr(Instruction::Div { dest, a, b, .. }) => {
                let result = self.val(a).div(self.val(b));
                self.write_register(&dest, result);
            }
            IR::Instr(Instruction::Call {
                dest, callee, args, ..
            }) => {
                let func = self.func(callee);
                let args = args.items.iter().map(|v| self.val(v.clone())).collect();
                self.call(func, args, dest);
            }
            IR::Instr(Instruction::Struct {
                dest, record, sym, ..
            }) => {
                let fields = record.items.iter().map(|v| self.val(v.clone())).collect();
                self.write_register(&dest, Value::Record(Some(sym), fields));
            }
            IR::Instr(Instruction::Record { dest, record, .. }) => {
                let fields = record.items.iter().map(|v| self.val(v.clone())).collect();
                self.write_register(&dest, Value::Record(None, fields));
            }
            IR::Instr(Instruction::GetField {
                dest,
                record,
                field,
                ..
            }) => {
                let Label::Positional(idx) = field else {
                    panic!("did not get positional index for record field: {field:?}");
                };

                let Value::Record(_, fields) = self.read_register(&record) else {
                    panic!("did not get record from {record:?}");
                };

                self.write_register(&dest, fields[idx].clone());
            }
            IR::Instr(Instruction::SetField {
                dest,
                val,
                record,
                field,
                ..
            }) => {
                let Label::Positional(idx) = field else {
                    panic!("did not get positional index for record field");
                };

                let Value::Record(sym, mut fields) = self.read_register(&record) else {
                    panic!("did not get record from {record:?}");
                };

                fields[idx] = self.val(val);
                self.write_register(&dest, Value::Record(sym, fields));
            }
            IR::Instr(Instruction::Ref { dest, val, .. }) => {
                let val = match val {
                    super::value::Value::Func(name) => Reference::Func(name.symbol().unwrap()),
                    super::value::Value::Reg(reg) => Reference::Register {
                        frame: self.frames.len(),
                        register: reg.into(),
                    },
                    _ => unimplemented!("don't know how to take ref of {val:?}"),
                };

                self.write_register(&dest, Value::Ref(val));
            }
            IR::Instr(Instruction::Cmp {
                dest, lhs, rhs, op, ..
            }) => {
                let val = match op {
                    CmpOperator::Greater => self.val(lhs).gt(self.val(rhs)),
                    CmpOperator::GreaterEquals => self.val(lhs).gte(self.val(rhs)),
                    CmpOperator::Less => self.val(lhs).lt(self.val(rhs)),
                    CmpOperator::LessEquals => self.val(lhs).lte(self.val(rhs)),
                    CmpOperator::Equals => self.val(lhs).eq(self.val(rhs)),
                    CmpOperator::NotEquals => self.val(lhs).ne(self.val(rhs)),
                };

                self.write_register(&dest, val);
            }
            IR::Instr(Instruction::_Print { val }) => match self.val(val) {
                Value::Int(val) => println!("{val}"),
                Value::Float(val) => println!("{val}"),
                Value::Bool(val) => println!("{val}"),
                Value::Record(sym, values) => {
                    if sym == Some(Symbol::String) {}

                    println!("{sym:?}{values:?}")
                }
                Value::Func(symbol) => println!("fn({symbol:?})"),
                Value::Void => println!("void"),
                Value::RawPtr(val) => println!("rawptr({val})"),
                Value::Ref(reference) => println!("{reference:?}"),
                Value::Uninit => println!("UNINIT"),
                Value::Buffer(bytes) => println!("buf({bytes:?})"),
            },
            IR::Instr(Instruction::Alloc { dest, ty, count }) => {}
            IR::Instr(Instruction::Free { .. } | Instruction::Load { .. }) => unimplemented!(),
        }
    }

    #[inline]
    fn next_instr(&mut self) -> IR {
        let frame = self.frames.last_mut().unwrap();
        let func = self.current_func.as_ref().unwrap();
        let block = &func.blocks[frame.current_block];
        let ir = block.next_ir(frame.pc);

        frame.pc += 1;

        ir
    }

    fn jump(&mut self, basic_block_id: BasicBlockId) {
        let frame = self.frames.last_mut().unwrap();
        frame.prev_block = Some(frame.current_block);
        frame.current_block = basic_block_id.0 as usize;
        frame.pc = 0;
    }

    fn write_register(&mut self, register: &Register, val: Value) {
        if register == &Register::MAIN {
            self.main_result = Some(val);
            return;
        }

        let frame = self.frames.last_mut().unwrap();
        frame.registers[register.0 as usize] = val;
    }

    fn read_register(&self, register: &Register) -> Value {
        let frame = self.frames.last().unwrap();
        frame
            .registers
            .get(register.0 as usize)
            .expect("No value in register")
            .clone()
    }

    fn func(&self, val: super::value::Value) -> Symbol {
        match val {
            super::value::Value::Reg(reg) => {
                let Value::Func(symbol) = self.read_register(&Register(reg)) else {
                    panic!(
                        "didn't get func symbol from {val:?}: {:?}",
                        self.read_register(&Register(reg))
                    );
                };

                symbol
            }
            super::value::Value::Func(name) => name.symbol().unwrap(),
            _ => panic!("cannot get func from {val:?}"),
        }
    }

    fn val(&mut self, val: super::value::Value) -> Value {
        match val {
            super::value::Value::Reg(reg) => self.read_register(&Register(reg)),
            super::value::Value::Int(v) => Value::Int(v),
            super::value::Value::Float(v) => Value::Float(v),
            super::value::Value::Func(v) => Value::Func(v.symbol().unwrap()),
            super::value::Value::Void => Value::Void,
            super::value::Value::Bool(v) => Value::Bool(v),
            super::value::Value::Uninit => Value::Uninit,
            super::value::Value::RawPtr(v) => Value::RawPtr(v),
            super::value::Value::Poison => panic!("unreachable reached"),
            super::value::Value::Buffer(v) => Value::Buffer(v),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use crate::ir::lowerer_tests::tests::lower;

    use super::*;

    pub fn interpret(input: &str) -> Value {
        let program = lower(input);
        let interpreter = Interpreter::new(program);
        interpreter.run()
    }

    #[test]
    pub fn empty_is_void() {
        assert_eq!(interpret(""), Value::Void);
    }

    #[test]
    pub fn int() {
        assert_eq!(interpret("123"), Value::Int(123));
    }

    #[test]
    pub fn float() {
        assert_eq!(interpret("1.23"), Value::Float(1.23));
    }

    #[test]
    pub fn add() {
        assert_eq!(interpret("1 + 2"), Value::Int(3));
        assert_eq!(interpret("1.0 + 2.0"), Value::Float(3.0));
    }

    #[test]
    pub fn sub() {
        assert_eq!(interpret("1 - 2"), Value::Int(-1));
        assert_eq!(interpret("1.0 - 2.0"), Value::Float(-1.0));
    }

    #[test]
    pub fn mul() {
        assert_eq!(interpret("2 * 3"), Value::Int(6));
        assert_eq!(interpret("2.0 * 3.0"), Value::Float(6.0));
    }

    #[test]
    pub fn div() {
        assert_eq!(interpret("4 / 2"), Value::Int(2));
        assert_eq!(interpret("1.0 / 2.0"), Value::Float(0.5));
    }

    #[test]
    pub fn record_literal() {
        assert_eq!(interpret("{ fizz: 123, buzz: 1.23 }.fizz"), Value::Int(123));
        assert_eq!(
            interpret("{ fizz: 123, buzz: 1.23 }.buzz"),
            Value::Float(1.23)
        );
    }

    #[test]
    pub fn struct_field() {
        assert_eq!(
            interpret("struct Person { let fizz: Int } ; Person(fizz: 123).fizz"),
            Value::Int(123)
        );
    }

    #[test]
    pub fn generic_struct_field() {
        assert_eq!(
            interpret("struct Fizz<T> { let buzz: T } ; Fizz(buzz: 123).buzz"),
            Value::Int(123)
        );
        assert_eq!(
            interpret("struct Fizz<T> { let buzz: T } ; Fizz(buzz: 1.23).buzz"),
            Value::Float(1.23)
        );
    }

    #[test]
    pub fn add_method() {
        assert_eq!(
            interpret(
                "func add(x) { x + 1 }

            add(2)
            "
            ),
            Value::Int(3)
        );
    }

    #[test]
    pub fn matching() {
        assert_eq!(
            interpret(
                "
                match 789 {
                    123 -> 1,
                    456 -> 2,
                    789 -> 3
                }
                "
            ),
            Value::Int(3)
        );
    }

    #[test]
    pub fn fib() {
        assert_eq!(
            interpret(
                "
                func fib(n) {
                    if n <= 1 { return n }

                    return fib(n - 2) + fib(n - 1)
                }

                fib(7) 
                "
            ),
            Value::Int(13)
        );
    }

    #[test]
    fn interprets_comparisons() {
        assert_eq!(interpret("1 < 2"), Value::Bool(true));
        assert_eq!(interpret("1 <= 2"), Value::Bool(true));
        assert_eq!(interpret("2 < 1"), Value::Bool(false));
        assert_eq!(interpret("2 <= 1"), Value::Bool(false));
        assert_eq!(interpret("2 <= 2"), Value::Bool(true));

        assert_eq!(interpret("1 > 2"), Value::Bool(false));
        assert_eq!(interpret("1 >= 2"), Value::Bool(false));
        assert_eq!(interpret("2 > 1"), Value::Bool(true));
        assert_eq!(interpret("2 >= 1"), Value::Bool(true));
        assert_eq!(interpret("2 >= 2"), Value::Bool(true));
    }

    #[test]
    fn interprets_not() {
        assert_eq!(interpret("!false"), Value::Bool(true));
        assert_eq!(interpret("!true"), Value::Bool(false));
    }

    #[test]
    fn interprets_or() {
        assert_eq!(interpret("true || false"), Value::Bool(true));
        assert_eq!(interpret("false || true"), Value::Bool(true));
        assert_eq!(interpret("true || true"), Value::Bool(true));
        assert_eq!(interpret("false || false"), Value::Bool(false));
    }

    #[test]
    fn interprets_and() {
        assert_eq!(interpret("true && true"), Value::Bool(true));
        assert_eq!(interpret("true && false"), Value::Bool(false));
        assert_eq!(interpret("false && true"), Value::Bool(false));
        assert_eq!(interpret("false && false"), Value::Bool(false));
    }

    #[test]
    fn interprets_if_expr() {
        assert_eq!(
            interpret(
                "
        let a = if false {
          1 + 2
        } else {
          3 + 4
        }

        a
       "
            ),
            Value::Int(7)
        );
    }
}
