use std::usize;

use crate::{
    interpreter::{
        memory::{MEM_SIZE, Memory},
        value::Value,
    },
    lowering::{
        instr::{Callee, Instr},
        ir_error::IRError,
        ir_module::IRModule,
        ir_printer::{self},
        ir_value::IRValue,
        lowerer::{BasicBlock, BasicBlockID, IRFunction, RefKind, RegisterList},
        register::Register,
    },
    transforms::monomorphizer::Monomorphizer,
};

#[derive(Debug)]
pub enum InterpreterError {
    NoMainFunc,
    CalleeNotFound,
    PredecessorNotFound,
    TypeError(Value, Value),
    UnreachableReached,
    IRError(IRError),
    Unknown(String),
}

#[derive(Debug)]
struct StackFrame {
    pred: Option<BasicBlockID>,
    function: IRFunction,
    block_idx: usize,
    pc: usize,
    sp: usize,
}

impl StackFrame {
    pub fn _dump(&self) -> String {
        "".into()
    }
}

pub struct IRInterpreter {
    program: IRModule,
    call_stack: Vec<StackFrame>,
    memory: Memory,
}

impl IRInterpreter {
    pub fn new(program: IRModule) -> Self {
        Self {
            program,
            call_stack: vec![],
            memory: Memory::new(),
        }
    }

    pub fn run(mut self) -> Result<Value, InterpreterError> {
        log::info!("Monomorphizing module");
        self.program = Monomorphizer::new().run(self.program.clone());

        println!("{}", crate::lowering::ir_printer::print(&self.program));

        let main = self
            .program
            .functions
            .iter()
            .find(|f| f.name == "@main")
            .cloned();
        if let Some(main) = main {
            self.execute_function(main, vec![])
        } else {
            Err(InterpreterError::NoMainFunc)
        }
    }

    pub fn step(&mut self) -> Result<Option<Value>, InterpreterError> {
        let instr = {
            let frame = &mut self.call_stack.last().expect("Stack underflow");
            let block = &frame.function.blocks[frame.block_idx];
            block.instructions[frame.pc].clone()
        };

        match self.execute_instr(instr) {
            Ok(retval) => {
                if let Some(retval) = retval {
                    return Ok(Some(retval));
                }
            }
            Err(err) => {
                println!("{:?}", err);
                self.dump();
                return Err(err);
            }
        }

        Ok(None)
    }

    fn execute_function(
        &mut self,
        function: IRFunction,
        args: Vec<Value>,
    ) -> Result<Value, InterpreterError> {
        // let blocks = function.blocks.clone();
        let sp = self
            .call_stack
            .last()
            .map(|frame| frame.sp + frame.function.size as usize)
            .unwrap_or(0);

        self.call_stack.push(StackFrame {
            pred: None,
            block_idx: 0,
            pc: 0,
            sp,
            function: function.clone(),
        });

        for (i, arg) in args.iter().enumerate() {
            self.set_register_value(&Register(i as i32), arg.clone());
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
        log::trace!("PC: {:?}", self.call_stack.last().unwrap().pc);
        let frame = self.call_stack.last().unwrap();
        log::info!(
            "\n{}:{}\n{:?}\n{}\n\t{:?}",
            frame.function.name,
            frame
                .function
                .debug_info
                .get(&BasicBlockID(frame.block_idx as u32))
                .map(|i| i.get(&frame.pc))
                .map(|expr_id| format!("{:?}", expr_id))
                .unwrap_or("-".into()),
            instr,
            ir_printer::format_instruction(&instr),
            self.memory.range(frame.sp, frame.function.size as usize)
        );

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
            Instr::StoreLocal(dest, _, reg) => {
                self.set_register_value(&dest, self.register_value(&reg));
            }
            Instr::LoadLocal(_, _, _) => todo!(),
            Instr::Phi(dest, _, predecessors) => {
                let frame = self.call_stack.last_mut().expect("stack underflow");

                for (reg, pred) in &predecessors.0 {
                    if frame.pred == Some(*pred) {
                        log::trace!("Phi check {:?}: {:?} ({:?})", reg, pred, frame.pred);
                        self.set_register_value(&dest, self.register_value(reg));
                        self.call_stack.last_mut().unwrap().pc += 1;
                        return Ok(None);
                    }
                }

                log::error!("Phi failed from {:?}: {:?}", predecessors, frame.pred);

                return Err(InterpreterError::PredecessorNotFound);
            }
            Instr::Ref(dest, _, RefKind::Func(name)) => {
                let idx = self
                    .program
                    .functions
                    .iter()
                    .position(|f| f.name == name)
                    .unwrap_or_else(|| {
                        log::error!(
                            "couldn't find ref {} in {:?}",
                            name,
                            self.program
                                .functions
                                .iter()
                                .map(|f| f.name.clone())
                                .collect::<Vec<String>>()
                        );

                        usize::MAX
                    });
                self.set_register_value(&dest, Value::Func(idx));
            }
            Instr::Call {
                dest_reg,
                callee,
                args,
                ..
            } => {
                let callee = match callee {
                    Callee::Register(reg) => {
                        let callee_value = self.register_value(&reg);
                        let callee_id = match callee_value {
                            Value::Func(id) => id,
                            _ => {
                                return Err(InterpreterError::Unknown(format!(
                                    "Interpreter error: Expected a function in the callee register, but got {callee_value:?}."
                                )));
                            }
                        };

                        let Some(function_to_call) = self.load_function(callee_id) else {
                            return Err(InterpreterError::CalleeNotFound);
                        };

                        function_to_call
                    }
                    Callee::Name(name) => {
                        let Some(function_to_call) =
                            self.program.functions.iter().find(|f| f.name == name)
                        else {
                            return Err(InterpreterError::CalleeNotFound);
                        };

                        function_to_call.clone()
                    }
                };

                let arg_values = self.register_values(&args);
                let result = self.execute_function(callee, arg_values)?;
                self.set_register_value(&dest_reg, result);
            }
            Instr::Branch {
                cond,
                true_target,
                false_target,
            } => {
                let next_block = if Value::Bool(true) == self.register_value(&cond) {
                    true_target.0 as usize
                } else {
                    false_target.0 as usize
                };

                let id = self.current_basic_block().id;
                let frame = self.call_stack.last_mut().expect("stack underflow");
                frame.pred = Some(id);
                frame.block_idx = next_block;
                frame.pc = 0;
                return Ok(None);
            }
            Instr::Ret(_ret, reg) => {
                if let Some(reg) = reg {
                    let retval = match reg {
                        IRValue::Register(reg) => self.register_value(&reg),
                        IRValue::ImmediateInt(int) => Value::Int(int),
                    };

                    self.call_stack.pop();

                    return Ok(Some(retval));
                } else {
                    self.call_stack.pop();
                    return Ok(Some(Value::Void));
                }
            }
            Instr::Jump(jump_to) => {
                let id = self.current_basic_block().id;
                let frame = self.call_stack.last_mut().unwrap();
                frame.pred = Some(id);
                frame.pc = 0;
                frame.block_idx = jump_to.0 as usize;
                return Ok(None);
            }
            Instr::Eq(dest, _, op1, op2) => {
                self.set_register_value(
                    &dest,
                    Value::Bool(self.register_value(&op1) == self.register_value(&op2)),
                );
            }
            Instr::Ne(dest, _, op1, op2) => {
                self.set_register_value(
                    &dest,
                    Value::Bool(self.register_value(&op1) != self.register_value(&op2)),
                );
            }
            Instr::TagVariant(dest, _, tag, values) => {
                self.set_register_value(
                    &dest,
                    Value::Enum {
                        tag,
                        values: values
                            .0
                            .iter()
                            .map(|r| self.register_value(&r.register))
                            .collect(),
                    },
                );
            }
            Instr::GetEnumTag(dest, enum_reg) => {
                let Value::Enum { tag, .. } = self.register_value(&enum_reg) else {
                    return Err(InterpreterError::Unknown(format!(
                        "did not find enum in register #{enum_reg:?}"
                    )));
                };

                self.set_register_value(&dest, Value::Int(tag as i64));
            }
            Instr::GetEnumValue(dest, _, enum_reg, _tag, value) => {
                // Tag would be useful if we needed to know about memory layout but since we're
                // just using objects who cares
                let Value::Enum { values, .. } = self.register_value(&enum_reg) else {
                    return Err(InterpreterError::Unknown(format!(
                        "did not find enum in register #{enum_reg:?}"
                    )));
                };

                self.set_register_value(&dest, values[value as usize].clone());
            }
            Instr::Unreachable => return Err(InterpreterError::UnreachableReached),
            Instr::LessThan(dest, _irtype, a, b) => {
                self.set_register_value(
                    &dest,
                    self.register_value(&a).lt(&self.register_value(&b))?,
                );
            }
            Instr::LessThanEq(dest, _irtype, a, b) => {
                self.set_register_value(
                    &dest,
                    self.register_value(&a).lte(&self.register_value(&b))?,
                );
            }
            Instr::GreaterThan(dest, _irtype, a, b) => {
                self.set_register_value(
                    &dest,
                    self.register_value(&a).gt(&self.register_value(&b))?,
                );
            }
            Instr::GreaterThanEq(dest, _irtype, a, b) => {
                self.set_register_value(
                    &dest,
                    self.register_value(&a).gte(&self.register_value(&b))?,
                );
            }
            Instr::Alloc { dest, ty, count } => {
                let Value::Int(count) = count
                    .map(|c| self.register_value(&c))
                    .unwrap_or(Value::Int(1))
                else {
                    return Err(InterpreterError::Unknown("invalid alloc count".into()));
                };
                let ptr = self.memory.heap_alloc(&ty, count as usize);
                self.set_register_value(&dest, Value::Pointer(ptr));
            }
            Instr::Store { val, location, ty } => match self.register_value(&location) {
                Value::Pointer(ptr) => self.memory.store(ptr, self.register_value(&val), &ty),
                _ => {
                    return Err(InterpreterError::Unknown(format!(
                        "no pointer in {location}: {:?}",
                        self.register_value(&location)
                    )));
                }
            },
            Instr::Load { dest, addr, ty } => match self.register_value(&addr) {
                Value::Pointer(ptr) => {
                    let val = self.memory.load(&ptr, &ty);
                    self.set_register_value(&dest, val.clone());
                }
                _ => {
                    return Err(InterpreterError::Unknown(format!(
                        "unable to load {:?}",
                        self.register_value(&addr)
                    )));
                }
            },
            Instr::GetElementPointer {
                dest, base, index, ..
            } => {
                let index = match index {
                    IRValue::ImmediateInt(int) => int,
                    IRValue::Register(reg) => {
                        let val = self.register_value(&reg);
                        match val {
                            Value::Int(int) => int,
                            _ => return Err(InterpreterError::TypeError(val, Value::Int(123))),
                        }
                    }
                };

                let Value::Pointer(base) = self.register_value(&base) else {
                    panic!(
                        "did not get base pointer for GEP: {:?}",
                        self.register_value(&base)
                    );
                };

                let pointer = base + index as usize;
                self.set_register_value(&dest, Value::Pointer(pointer));
            }
            Instr::MakeStruct { dest, values, .. } => {
                let structure = Value::Struct(self.register_values(&values));
                self.set_register_value(&dest, structure);
            }
            Instr::GetValueOf { .. } => todo!(),
        }

        self.call_stack.last_mut().unwrap().pc += 1;

        Ok(None)
    }

    fn current_basic_block(&self) -> &BasicBlock {
        let frame = self.call_stack.last().unwrap();
        &frame.function.blocks[frame.block_idx]
    }

    fn set_register_value(&mut self, register: &Register, value: Value) {
        log::trace!("set {register:?} to {value:?}");
        let frame = self.call_stack.last_mut().expect("Stack underflow");
        let stack = self
            .memory
            .range_mut(frame.sp, frame.function.size as usize);
        stack[register.0 as usize] = Some(value);
    }

    fn register_values(&self, registers: &RegisterList) -> Vec<Value> {
        registers
            .0
            .iter()
            .map(|r| self.register_value(&r.register).clone())
            .collect()
    }

    fn register_value(&self, register: &Register) -> Value {
        let frame = self.call_stack.last().expect("Stack underflow");
        let stack = self.memory.range(frame.sp, frame.function.size as usize);
        stack[register.0 as usize]
            .clone()
            .expect("null pointer lol")
    }

    fn load_function(&self, idx: usize) -> Option<IRFunction> {
        self.program.functions.get(idx).cloned()
    }

    fn dump(&self) {
        for (i, frame) in self.call_stack.iter().rev().enumerate() {
            let stack = self.memory.range(frame.sp, frame.function.size as usize);
            println!(
                "{}:\n{}",
                i,
                stack
                    .iter()
                    .enumerate()
                    .map(|(id, v)| {
                        format!(
                            "\t{} = {}",
                            frame.sp + id,
                            match v {
                                Some(v) => format!("{:?}", v),
                                None => "-".into(),
                            }
                        )
                    })
                    .collect::<Vec<String>>()
                    .join("\n")
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use crate::{
        compiling::driver::Driver,
        interpreter::{
            interpreter::{IRInterpreter, InterpreterError},
            value::Value,
        },
    };

    fn interpret(code: &'static str) -> Result<Value, InterpreterError> {
        let mut driver = Driver::with_str(code);
        let unit = driver.lower().into_iter().next().unwrap();

        let diagnostics = unit.source_file(&PathBuf::from("-")).unwrap().diagnostics();
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let module = unit.module();

        IRInterpreter::new(module).run()
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

    #[test]
    fn interprets_recursion() {
        assert_eq!(
            Value::Int(120),
            interpret(
                "
                func factorial(n) {
                    if n == 1 {
                        return n
                    } else {
                        n * factorial(n - 1)
                    }
                }

                factorial(5)
        "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_simple_binary_ops() {
        assert_eq!(Value::Bool(true), interpret("1 < 2").unwrap());
        assert_eq!(Value::Bool(true), interpret("1 <= 2").unwrap());
        assert_eq!(Value::Bool(false), interpret("2 < 1").unwrap());
        assert_eq!(Value::Bool(false), interpret("2 <= 1").unwrap());

        assert_eq!(Value::Bool(false), interpret("1 > 2").unwrap());
        assert_eq!(Value::Bool(false), interpret("1 >= 2").unwrap());
        assert_eq!(Value::Bool(true), interpret("2 > 1").unwrap());
        assert_eq!(Value::Bool(true), interpret("2 >= 1").unwrap());

        assert_eq!(Value::Bool(true), interpret("1 == 1").unwrap());
        assert_eq!(Value::Bool(false), interpret("1 == 2").unwrap());

        assert_eq!(Value::Bool(true), interpret("1 != 2").unwrap());
        assert_eq!(Value::Bool(false), interpret("1 != 1").unwrap());
    }

    #[test]
    fn interprets_closure() {
        assert_eq!(
            Value::Int(3),
            interpret(
                "
    func makeCounter() {
			let count = 0

			return func() {
				count = count + 1
				return count
			}
		}

		let counter = makeCounter()
		counter()
    counter()
    counter()
        "
            )
            .unwrap()
        )
    }

    #[test]
    fn interprets_array_push_get() {
        assert_eq!(
            interpret(
                "
                let a = [1, 2, 3]
                a.push(4)
                a.get(3)
        "
            )
            .unwrap(),
            Value::Int(4),
        )
    }

    #[test]
    fn interprets_array_pop() {
        assert_eq!(
            interpret(
                "
                let a = [1, 2, 3]
                let b = a.pop()
                b
        "
            )
            .unwrap(),
            Value::Int(3),
        )
    }
}
