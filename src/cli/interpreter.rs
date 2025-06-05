use std::collections::HashMap;

use crate::lowering::ir::{
    BasicBlockID, IRFunction, IRProgram, Instr, RefKind, Register, Terminator,
};

#[derive(Debug)]
pub enum InterpreterError {
    NoMainFunc,
    CalleeNotFound,
    PredecessorNotFound,
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
    Int(u64),
    Float(f64),
    Bool(bool),
    Void,
}

impl Value {
    fn add(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            (Value::Float(a), Value::Float(b)) => Value::Float(a + b),
            _ => panic!("Cannot {:?} + {:?}", self, other),
        }
    }

    fn sub(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a - b),
            (Value::Float(a), Value::Float(b)) => Value::Float(a - b),
            _ => panic!("Cannot {:?} - {:?}", self, other),
        }
    }

    fn mul(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a * b),
            (Value::Float(a), Value::Float(b)) => Value::Float(a * b),
            _ => panic!("Cannot {:?} * {:?}", self, other),
        }
    }

    fn div(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a / b),
            (Value::Float(a), Value::Float(b)) => Value::Float(a / b),
            _ => panic!("Cannot {:?} / {:?}", self, other),
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
        if self.block_is_terminating() {
            let terminator = {
                let frame = &mut self.stack.last().expect("Stack underflow");
                let block = &frame.function.blocks[frame.block_idx];
                block.terminator.clone()
            };

            let res = self.execute_terminator(&terminator)?;

            Ok(res)
        } else {
            let instr = {
                let frame = &mut self.stack.last().expect("Stack underflow");
                let block = &frame.function.blocks[frame.block_idx];
                block.instructions[frame.pc].clone()
            };

            self.execute_instr(instr)?;

            Ok(None)
        }
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

        let mut ret = Value::Void;

        while let Ok(res) = self.step() {
            log::warn!("{:?}", res);
            if let Some(res) = res {
                ret = res;
                break;
            }
        }

        self.stack.pop();

        Ok(ret)
    }

    // fn execute_basic_block(
    //     &mut self,
    //     block: &BasicBlock,
    //     predecessor: Option<&BasicBlockID>,
    // ) -> Result<Value, InterpreterError> {
    //     log::trace!("Executing basic block: {:?}", block);

    //     for instr in &block.instructions {
    //         self.execute_instr(instr, predecessor)?;
    //     }

    //     self.execute_terminator(&block.terminator, &block.id)
    // }

    fn execute_instr(&mut self, instr: Instr) -> Result<(), InterpreterError> {
        log::trace!("{:?}", instr);
        log::trace!("{:?}", self.stack);

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

                self.set_register_value(&dest, op1.add(&op2));
            }
            Instr::Sub(dest, _, op1, op2) => {
                let op1 = self.register_value(&op1);
                let op2 = self.register_value(&op2);

                self.set_register_value(&dest, op1.sub(&op2));
            }
            Instr::Mul(dest, _, op1, op2) => {
                let op1 = self.register_value(&op1);
                let op2 = self.register_value(&op2);

                self.set_register_value(&dest, op1.mul(&op2));
            }
            Instr::Div(dest, _, op1, op2) => {
                let op1 = self.register_value(&op1);
                let op2 = self.register_value(&op2);

                self.set_register_value(&dest, op1.div(&op2));
            }
            Instr::StoreLocal(_, _, _) => todo!(),
            Instr::LoadLocal(_, _, _) => todo!(),
            Instr::Phi(dest, _, predecessors) => {
                let frame = self.stack.last_mut().expect("stack underflow");

                for (reg, pred) in &predecessors {
                    if frame.pred == Some(*pred) {
                        self.set_register_value(&dest, self.register_value(&reg));
                        return Ok(());
                    }
                }

                log::error!("Phi failed from {:?}: {:?}", frame, predecessors);

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
                    let frame = self.stack.last_mut().expect("stack underflow");
                    frame.block_idx = jump_to.0 as usize;
                    frame.pc = 0;
                }
            }
        }

        Ok(())
    }

    fn execute_terminator(
        &mut self,
        terminator: &Terminator,
    ) -> Result<Option<Value>, InterpreterError> {
        match terminator {
            Terminator::Ret(Some((_, reg))) => {
                let retval = self.register_value(reg);
                Ok(Some(retval))
            }
            Terminator::Jump(jump_to) => {
                let frame = self.stack.last_mut().unwrap();
                frame.pc = 0;
                frame.block_idx = jump_to.0 as usize;

                Ok(None)
            }
            _ => todo!(),
        }
    }

    fn set_register_value(&mut self, register: &Register, value: Value) {
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

    fn block_is_terminating(&self) -> bool {
        let frame = self.stack.last().expect("stack underflow");
        frame.function.blocks[frame.block_idx].instructions.len() == frame.pc + 1
    }
}
