use std::fmt::Display;

use crate::{
    ir::{
        function::Function, instruction::Instruction, ir_ty::IrTy, program::Program,
        register::Register, terminator::Terminator,
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
    Record(Vec<Value>),
    Func(Symbol),
    Void,
    Ref(Reference),
    Uninit,
}

impl Value {
    fn add(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Int(lhs + rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Float(lhs + rhs),
            _ => panic!("can't add {self:?} and {other:?}"),
        }
    }
    fn sub(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Int(lhs - rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Float(lhs - rhs),
            _ => panic!("can't sub {self:?} and {other:?}"),
        }
    }
    fn mul(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Int(lhs * rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Float(lhs * rhs),
            _ => panic!("can't mul {self:?} and {other:?}"),
        }
    }
    fn div(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Int(lhs / rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Float(lhs / rhs),
            _ => panic!("can't div {self:?} and {other:?}"),
        }
    }
}

#[derive(Debug)]
pub struct Frame {
    dest: Register,
    ret: Option<Symbol>,
    registers: Vec<Value>,
    pc: usize,
    current_block: usize,
}

impl Frame {
    pub fn new(dest: Register, ret: Option<Symbol>) -> Self {
        Self {
            ret,
            dest,
            registers: Default::default(),
            pc: 0,
            current_block: 0,
        }
    }
}

enum IR {
    Instr(Instruction<IrTy, Label>),
    Term(Terminator<IrTy>),
}

impl Display for IR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IR::Instr(instr) => write!(f, "{instr}"),
            IR::Term(term) => write!(f, "{term}"),
        }
    }
}

pub struct Interpreter {
    program: Program,
    frames: Vec<Frame>,
    current_func: Option<Function<IrTy, Label>>,
    main_result: Option<Value>,
}

impl Interpreter {
    pub fn new(program: Program) -> Self {
        Self {
            program,
            frames: Default::default(),
            current_func: None,
            main_result: None,
        }
    }

    pub fn run(mut self) -> Value {
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

        let func = self.program.functions.shift_remove(&function).unwrap();
        let mut frame = Frame::new(dest, caller_name);
        frame.registers.resize(func.register_count, Value::Uninit);
        for (i, arg) in args.into_iter().enumerate() {
            frame.registers[i] = arg;
        }
        self.frames.push(frame);
        self.current_func = Some(func);
    }

    pub fn next(&mut self) {
        let next_instruction = self.next_instr();

        tracing::trace!("{next_instruction}");
        tracing::trace!("{:?}", self.frames.last().unwrap());

        match next_instruction {
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
            IR::Term(Terminator::Branch { .. }) => todo!(),
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
            IR::Instr(Instruction::Record { dest, record, .. }) => {
                let fields = record.items.iter().map(|v| self.val(v.clone())).collect();
                self.write_register(&dest, Value::Record(fields));
            }
            IR::Instr(Instruction::GetField {
                dest,
                record,
                field,
                ..
            }) => {
                let Label::Positional(idx) = field else {
                    panic!("did not get positional index for record field");
                };

                let Value::Record(fields) = self.read_register(&record) else {
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

                let Value::Record(mut fields) = self.read_register(&record) else {
                    panic!("did not get record from {record:?}");
                };

                fields[idx] = self.val(val);
                self.write_register(&dest, Value::Record(fields));
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
        }
    }

    #[inline]
    fn next_instr(&mut self) -> IR {
        let frame = self.frames.last_mut().unwrap();
        let func = self.current_func.as_ref().unwrap();
        let block = &func.blocks[frame.current_block];
        let result = if frame.pc >= block.instructions.len() {
            IR::Term(block.terminator.clone())
        } else {
            IR::Instr(block.instructions[frame.pc].clone())
        };

        frame.pc += 1;

        result
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
                    panic!("didn't get func symbol from {val:?}");
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
}
