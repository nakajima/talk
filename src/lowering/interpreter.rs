use std::collections::HashMap;

use crate::lowering::{
    instr::Instr,
    lowerer::{BasicBlock, BasicBlockID, IRFunction, IRProgram, RefKind, Register},
};

#[derive(Debug)]
pub enum InterpreterError {
    NoMainFunc,
    CalleeNotFound,
    PredecessorNotFound,
    TypeError(Value, Value),
    UnreachableReached,
}

#[derive(Debug)]
struct StackFrame {
    pred: Option<BasicBlockID>,
    function: IRFunction,
    block_idx: usize,
    pc: usize,
    registers: HashMap<Register, Value>,
}

pub struct IRInterpreter {
    program: IRProgram,
    stack: Vec<StackFrame>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Enum { tag: u16, values: Vec<Value> },
    Void,
}

impl Value {
    fn add(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    fn sub(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    fn mul(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    fn div(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a / b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }
}

impl IRInterpreter {
    pub fn new(program: IRProgram) -> Self {
        Self {
            program,
            stack: vec![],
        }
    }

    pub fn run(&mut self) -> Result<Value, InterpreterError> {
        if let Some(main) = self.load_function("@main") {
            self.execute_function(main, vec![])
        } else {
            Err(InterpreterError::NoMainFunc)
        }
    }

    pub fn step(&mut self) -> Result<Option<Value>, InterpreterError> {
        let instr = {
            let frame = &mut self.stack.last().expect("Stack underflow");
            let block = &frame.function.blocks[frame.block_idx];
            block.instructions[frame.pc].clone()
        };

        if let Some(retval) = self.execute_instr(instr)? {
            return Ok(Some(retval));
        }

        Ok(None)
    }

    fn execute_function(
        &mut self,
        function: IRFunction,
        args: Vec<Value>,
    ) -> Result<Value, InterpreterError> {
        // let blocks = function.blocks.clone();
        self.stack.push(StackFrame {
            pred: None,
            block_idx: 0,
            pc: 0,
            function,
            registers: Default::default(),
        });

        for (i, arg) in args.iter().enumerate() {
            self.set_register_value(&Register(i as u32), arg.clone());
        }

        loop {
            match self.step() {
                Ok(res) => {
                    if let Some(res) = res {
                        return Ok(res);
                    }
                }
                Err(err) => return Err(err),
            }
        }
    }

    fn execute_instr(&mut self, instr: Instr) -> Result<Option<Value>, InterpreterError> {
        log::trace!("PC: {:?}", self.stack.last().unwrap().pc);
        log::trace!("{:?}", instr);

        match instr {
            Instr::ConstantInt(register, val) => {
                self.set_register_value(&register, Value::Int(val));
            }
            Instr::ConstantFloat(register, val) => {
                self.set_register_value(&register, Value::Float(val));
            }
            Instr::ConstantBool(register, val) => {
                self.set_register_value(&register, Value::Bool(val));
            }
            Instr::Add(dest, _, op1, op2) => {
                let op1 = self.register_value(&op1);
                let op2 = self.register_value(&op2);

                self.set_register_value(&dest, op1.add(&op2)?);
            }
            Instr::Sub(dest, _, op1, op2) => {
                let op1 = self.register_value(&op1);
                let op2 = self.register_value(&op2);

                self.set_register_value(&dest, op1.sub(&op2)?);
            }
            Instr::Mul(dest, _, op1, op2) => {
                let op1 = self.register_value(&op1);
                let op2 = self.register_value(&op2);

                self.set_register_value(&dest, op1.mul(&op2)?);
            }
            Instr::Div(dest, _, op1, op2) => {
                let op1 = self.register_value(&op1);
                let op2 = self.register_value(&op2);

                self.set_register_value(&dest, op1.div(&op2)?);
            }
            Instr::StoreLocal(_, _, _) => todo!(),
            Instr::LoadLocal(_, _, _) => todo!(),
            Instr::Phi(dest, _, predecessors) => {
                let frame = self.stack.last_mut().expect("stack underflow");

                for (reg, pred) in &predecessors {
                    if frame.pred == Some(*pred) {
                        println!("Phi check {:?}: {:?} ({:?})", reg, pred, frame.pred);
                        self.set_register_value(&dest, self.register_value(reg));
                        self.stack.last_mut().unwrap().pc += 1;
                        return Ok(None);
                    }
                }

                log::error!("Phi failed from {:?}: {:?}", predecessors, frame.pred);

                return Err(InterpreterError::PredecessorNotFound);
            }
            Instr::Ref(_dest, _, RefKind::Func(name)) => {
                let _func = self.load_function(&name);
            }
            Instr::Call {
                dest_reg,
                callee,
                args,
                ..
            } => {
                let Some(callee) = self.load_function(&callee) else {
                    return Err(InterpreterError::CalleeNotFound);
                };

                let res = self.execute_function(
                    callee,
                    args.iter().map(|r| self.register_value(r)).collect(),
                )?;

                if let Some(dest_reg) = dest_reg {
                    self.set_register_value(&dest_reg, res);
                }
            }
            Instr::JumpUnless(cond, jump_to) => {
                if Value::Bool(false) == self.register_value(&cond) {
                    let id = self.current_basic_block().id;
                    let frame = self.stack.last_mut().expect("stack underflow");
                    frame.pred = Some(id);
                    frame.block_idx = jump_to.0 as usize;
                    frame.pc = 0;
                    return Ok(None);
                }
            }
            Instr::Ret(Some((_, reg))) => {
                let retval = self.register_value(&reg);
                self.stack.pop();
                return Ok(Some(retval));
            }
            Instr::Ret(None) => {
                self.stack.pop();
                return Ok(Some(Value::Void));
            }
            Instr::Jump(jump_to) => {
                let id = self.current_basic_block().id;
                let frame = self.stack.last_mut().unwrap();
                frame.pred = Some(id);
                frame.pc = 0;
                frame.block_idx = jump_to.0 as usize;
                return Ok(None);
            }
            Instr::JumpIf(cond, jump_to) => {
                if Value::Bool(true) == self.register_value(&cond) {
                    let id = self.current_basic_block().id;
                    let frame = self.stack.last_mut().expect("stack underflow");
                    frame.pred = Some(id);
                    frame.block_idx = jump_to.0 as usize;
                    frame.pc = 0;
                    return Ok(None);
                }
            }
            Instr::Eq(dest, _, op1, op2) => {
                self.set_register_value(
                    &dest,
                    Value::Bool(self.register_value(&op1) == self.register_value(&op2)),
                );
            }
            Instr::TagVariant(dest, _, tag, values) => {
                self.set_register_value(
                    &dest,
                    Value::Enum {
                        tag,
                        values: values.iter().map(|r| self.register_value(r)).collect(),
                    },
                );
            }
            Instr::GetEnumTag(dest, enum_reg) => {
                let Value::Enum { tag, .. } = self.register_value(&enum_reg) else {
                    panic!("did not find enum in register #{:?}", enum_reg);
                };

                self.set_register_value(&dest, Value::Int(tag as i64));
            }
            Instr::GetEnumValue(dest, _, enum_reg, _tag, value) => {
                // Tag would be useful if we needed to know about memory layout but since we're
                // just using objects who cares
                let Value::Enum { values, .. } = self.register_value(&enum_reg) else {
                    panic!("did not find enum in register #{:?}", enum_reg);
                };

                self.set_register_value(&dest, values[value as usize].clone());
            }
            Instr::Unreachable => return Err(InterpreterError::UnreachableReached),
        }

        self.stack.last_mut().unwrap().pc += 1;

        Ok(None)
    }

    fn current_basic_block(&self) -> &BasicBlock {
        let frame = self.stack.last().unwrap();
        &frame.function.blocks[frame.block_idx]
    }

    fn set_register_value(&mut self, register: &Register, value: Value) {
        log::trace!("set {:?} to {:?}", register, value);
        self.stack
            .last_mut()
            .expect("Stack underflow")
            .registers
            .insert(*register, value);
    }

    fn register_value(&self, register: &Register) -> Value {
        self.stack
            .last()
            .expect("Stack underflow")
            .registers
            .get(register)
            .unwrap_or_else(|| panic!("No value found for register: {:?}", register))
            .clone()
    }

    fn load_function(&self, name: &str) -> Option<IRFunction> {
        for func in &self.program.functions.clone() {
            if func.name == name {
                return Some(func.clone());
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        check,
        lowering::{
            interpreter::{IRInterpreter, InterpreterError, Value},
            ir_printer::print,
            lowerer::Lowerer,
        },
    };

    fn interpret(code: &'static str) -> Result<Value, InterpreterError> {
        let typed = check(code).unwrap();
        let lowerer = Lowerer::new(typed);
        let lowered = lowerer.lower().unwrap();

        println!("{}", print(&lowered));

        IRInterpreter::new(lowered).run()
    }

    #[test]
    fn interprets_int() {
        assert_eq!(Value::Int(3), interpret("3").unwrap());
    }

    #[test]
    fn interprets_float() {
        assert_eq!(Value::Float(3.), interpret("3.0").unwrap());
    }

    #[test]
    fn interprets_bool() {
        assert_eq!(Value::Bool(true), interpret("true").unwrap());
    }

    #[test]
    fn interprets_add() {
        assert_eq!(Value::Int(3), interpret("1 + 2").unwrap());
        assert_eq!(Value::Float(3.0), interpret("1. + 2.").unwrap());
        assert!(interpret("true + false").is_err());
    }

    #[test]
    fn interprets_sub() {
        assert_eq!(Value::Int(-1), interpret("1 - 2").unwrap());
        assert_eq!(Value::Float(-1.0), interpret("1. - 2.").unwrap());
        assert!(interpret("true - false").is_err());
    }

    #[test]
    fn interprets_mul() {
        assert_eq!(Value::Int(6), interpret("2 * 3").unwrap());
        assert_eq!(Value::Float(6.0), interpret("2. * 3.").unwrap());
        assert!(interpret("true * false").is_err());
    }

    #[test]
    fn interprets_div() {
        assert_eq!(Value::Int(3), interpret("6 / 2").unwrap());
        assert_eq!(Value::Float(3.0), interpret("6. / 2.").unwrap());
        assert!(interpret("true / false").is_err());
    }

    #[test]
    fn interprets_call() {
        assert_eq!(
            Value::Int(6),
            interpret(
                "
        func add(x, y) {
            x + y
        }

        add(add(1, 2), 3)
        "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_return() {
        assert_eq!(
            Value::Int(1),
            interpret(
                "
        func foo() {
            return 1
            2
        }

        foo()
        "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_simple_match() {
        assert_eq!(
            Value::Int(456),
            interpret(
                "
            match 1 {
                0 -> 123,
                1 -> 456
            }
        "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_builtin_optional() {
        assert_eq!(
            Value::Int(123),
            interpret(
                "
            match Optional.some(123) {
                .some(x) -> x,
                .none -> 0
            }
        "
            )
            .unwrap()
        );
    }
}
