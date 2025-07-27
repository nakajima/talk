use crate::{
    SymbolTable,
    interpret::{
        io::InterpreterIO,
        memory::{Memory, Pointer},
        value::Value,
    },
    lowering::{
        instr::{Callee, Instr},
        ir_error::IRError,
        ir_module::IRModule,
        ir_printer::{self},
        ir_type::IRType,
        ir_value::IRValue,
        lowerer::{BasicBlock, BasicBlockID, RefKind, RegisterList},
        register::Register,
    },
};

use std::collections::HashMap;

#[derive(Debug)]
pub enum InterpreterError {
    NoMainFunc,
    CalleeNotFound(String),
    PredecessorNotFound,
    TypeError(String, String),
    UnreachableReached,
    IRError(IRError),
    Unknown(String),
    InvalidProgram,
}

#[derive(Debug)]
struct StackFrame {
    pred: Option<BasicBlockID>,
    function: usize,
    block_idx: usize,
    pc: usize,
    sp: usize,
}

impl StackFrame {
    pub fn _dump(&self) -> String {
        "".into()
    }
}

pub struct IRInterpreter<'a, IO: InterpreterIO> {
    pub(super) program: IRModule,
    pub(super) memory: Memory,
    pub symbols: &'a SymbolTable,
    io: &'a IO,
    function_map: HashMap<String, usize>,
    call_stack: Vec<StackFrame>,
}

#[allow(clippy::unwrap_used)]
#[allow(clippy::expect_used)]
impl<'a, IO: InterpreterIO> IRInterpreter<'a, IO> {
    pub fn new(program: IRModule, io: &'a IO, symbols: &'a SymbolTable) -> Self {
        let memory = Memory::new(&program.constants);
        let function_map = program
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.name.clone(), i))
            .collect();
        Self {
            program,
            call_stack: vec![],
            memory,
            io,
            symbols,
            function_map,
        }
    }

    pub fn run(mut self) -> Result<Value, InterpreterError> {
        tracing::info!("Monomorphizing module");

        #[allow(clippy::print_with_newline)]
        if std::env::var("IR").is_ok() {
            print!("{}\n", crate::lowering::ir_printer::print(&self.program));
        }

        let Some(&main_idx) = self.function_map.get("@main") else {
            return Err(InterpreterError::NoMainFunc);
        };
        let main = &self.program.functions[main_idx];
        let ret_ty = main
            .blocks
            .iter()
            .rev()
            .find_map(|b| {
                b.instructions.iter().rev().find_map(|i| match i {
                    Instr::Ret(ty, _) => Some(ty.clone()),
                    _ => None,
                })
            })
            .unwrap_or(IRType::Void);
        let result = self.execute_function(main_idx, vec![])?;

        // If the program's entry point returns a struct but the interpreter
        // represented it as a pointer, load the value from memory using the
        // function's return type.
        if let Value::Pointer(ptr) = &result
            && ret_ty != IRType::POINTER
        {
            return self.memory.load(ptr, &ret_ty);
        }

        Ok(result)
    }

    pub fn step(&mut self) -> Result<Option<Value>, InterpreterError> {
        let instr = {
            let frame = &mut self.call_stack.last().expect("Stack underflow");
            let func = &self.program.functions[frame.function];
            let block = &func.blocks[frame.block_idx];
            block.instructions[frame.pc].clone()
        };

        match self.execute_instr(instr) {
            Ok(retval) => {
                if let Some(retval) = retval {
                    return Ok(Some(retval));
                }
            }
            Err(err) => {
                tracing::error!("{err:?}");
                self.dump();
                return Err(err);
            }
        }

        Ok(None)
    }

    fn execute_function(
        &mut self,
        function_idx: usize,
        args: Vec<Value>,
    ) -> Result<Value, InterpreterError> {
        let _function = &self.program.functions[function_idx];
        let sp = self
            .call_stack
            .last()
            .map(|frame| frame.sp + self.program.functions[frame.function].size as usize)
            .unwrap_or(self.memory.next_stack_addr);

        self.call_stack.push(StackFrame {
            pred: None,
            block_idx: 0,
            pc: 0,
            sp,
            function: function_idx,
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
        tracing::trace!("PC: {:?}", self.call_stack.last().unwrap().pc);
        let frame = self.call_stack.last().unwrap();
        let func = &self.program.functions[frame.function];
        tracing::info!(
            "\n{}:{}\n{:?}\n{}\n",
            func.name,
            func.debug_info
                .get(&BasicBlockID(frame.block_idx as u32))
                .map(|i| i.get(&frame.pc))
                .map(|expr_id| format!("{expr_id:?}"))
                .unwrap_or("-".into()),
            instr,
            ir_printer::format_instruction(&instr),
        );

        for (i, value) in self
            .memory
            .range(frame.sp, func.size as usize)
            .iter()
            .enumerate()
        {
            if let Some(value) = value {
                tracing::trace!("\t%{i} = {:?}", value)
            } else {
                tracing::trace!("\t%{i} = EMPTY")
            }
        }

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
            Instr::LoadLocal(_, _, _) => (),
            Instr::Phi(dest, _, predecessors) => {
                let frame = self.call_stack.last_mut().expect("stack underflow");

                for (reg, pred) in &predecessors.0 {
                    if frame.pred == Some(*pred) {
                        tracing::trace!("Phi check {:?}: {:?} ({:?})", reg, pred, frame.pred);
                        self.set_register_value(&dest, self.register_value(reg));
                        self.call_stack.last_mut().unwrap().pc += 1;
                        return Ok(None);
                    }
                }

                tracing::error!("Phi failed from {:?}: {:?}", predecessors, frame.pred);

                return Err(InterpreterError::PredecessorNotFound);
            }
            Instr::Ref(dest, _, RefKind::Func(name)) => {
                let idx = self
                    .program
                    .functions
                    .iter()
                    .position(|f| f.name == name)
                    .unwrap_or_else(|| {
                        tracing::error!(
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
                let callee_idx = match callee {
                    Callee::Register(reg) => {
                        let callee_value = self.register_value(&reg);
                        match callee_value {
                            Value::Func(id) => id,
                            _ => {
                                return Err(InterpreterError::Unknown(format!(
                                    "Interpreter error: Expected a function in the callee register, but got {callee_value:?}."
                                )));
                            }
                        }
                    }
                    Callee::Name(name) => *self
                        .function_map
                        .get(&name)
                        .ok_or(InterpreterError::CalleeNotFound(name))?,
                };

                let arg_values = self.register_values(&args);
                let result = self.execute_function(callee_idx, arg_values)?;
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
            Instr::TagVariant(dest, ty, tag, values) => {
                let IRType::Enum(symbol_id, _) = ty else {
                    unreachable!()
                };
                self.set_register_value(
                    &dest,
                    Value::Enum {
                        symbol_id,
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
                let Value::Int(count) = count.map(|c| self.value(&c)).unwrap_or(Value::Int(1))
                else {
                    return Err(InterpreterError::Unknown("invalid alloc count".into()));
                };
                let ptr = self.memory.heap_alloc(&ty, count as usize);
                self.set_register_value(&dest, Value::Pointer(ptr));
            }
            Instr::Store { val, location, ty } => match self.register_value(&location) {
                Value::Pointer(ptr) => self.memory.store(ptr, self.value(&val), &ty),
                _ => {
                    return Err(InterpreterError::Unknown(format!(
                        "no pointer in {location}: {:?}",
                        self.register_value(&location)
                    )));
                }
            },
            Instr::Load { dest, addr, ty } => match self.register_value(&addr) {
                Value::Pointer(ptr) => {
                    let val = self.memory.load(&ptr, &ty)?;
                    self.set_register_value(&dest, val.clone());
                }
                _ => {
                    return Err(InterpreterError::Unknown(format!(
                        "unable to load {:?}",
                        self.register_value(&addr)
                    )));
                }
            },
            Instr::Const { dest, val, ty } => {
                let Value::Int(int) = self.value(&val) else {
                    return Err(InterpreterError::Unknown(format!(
                        "no const found for {:?}",
                        self.value(&val)
                    )));
                };

                let const_ptr = Pointer::new(int as usize, ty);
                self.set_register_value(&dest, Value::Pointer(const_ptr));
            }
            Instr::GetElementPointer {
                dest, base, index, ..
            } => {
                let index = match index {
                    IRValue::ImmediateInt(int) => int,
                    IRValue::Register(reg) => {
                        let val = self.register_value(&reg);
                        match val {
                            Value::Int(int) => int,
                            _ => {
                                return Err(InterpreterError::TypeError(
                                    val.to_string(self),
                                    "??".to_string(),
                                ));
                            }
                        }
                    }
                };

                let Value::Pointer(base) = self.register_value(&base) else {
                    return Err(InterpreterError::Unknown(format!(
                        "did not get base pointer for GEP: {:?}",
                        self.register_value(&base)
                    )));
                };

                let pointer = base + index as usize;
                self.set_register_value(&dest, Value::Pointer(pointer));
            }
            Instr::MakeStruct { dest, values, ty } => {
                let IRType::Struct(sym, _, _) = ty else {
                    return Err(InterpreterError::Unknown("Didn't get struct".into()));
                };
                let structure = Value::Struct(sym, self.register_values(&values));
                self.set_register_value(&dest, structure);
            }
            #[allow(clippy::print_with_newline)]
            Instr::Print { ty, val } => {
                let val = self.value(&val);

                let val = if let Value::Pointer(ptr) = val {
                    self.memory.load(&ptr, &ty)?
                } else {
                    val
                };

                self.io
                    .write_all(format!("{}\n", val.to_string(self)).as_bytes());
            }
            Instr::GetValueOf { .. } => (),
        }

        self.call_stack.last_mut().unwrap().pc += 1;

        Ok(None)
    }

    fn value(&self, value: &IRValue) -> Value {
        match value {
            IRValue::ImmediateInt(int) => Value::Int(*int),
            IRValue::Register(reg) => self.register_value(reg),
        }
    }

    fn current_basic_block(&self) -> &BasicBlock {
        let frame = self.call_stack.last().unwrap();
        &self.program.functions[frame.function].blocks[frame.block_idx]
    }

    fn set_register_value(&mut self, register: &Register, value: Value) {
        tracing::trace!("set {register:?} to {value:?}");
        let frame = self.call_stack.last_mut().expect("Stack underflow");
        let stack = self.memory.range_mut(
            frame.sp,
            self.program.functions[frame.function].size as usize,
        );
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
        let stack = self.memory.range(
            frame.sp,
            self.program.functions[frame.function].size as usize,
        );
        stack[register.0 as usize]
            .clone()
            .expect("null pointer lol")
    }

    fn dump(&self) {
        for frame in self.call_stack.iter().rev() {
            let func = &self.program.functions[frame.function];
            let stack = self.memory.range(frame.sp, func.size as usize);
            print!(
                "{}:\n{}\n",
                func.name,
                stack
                    .iter()
                    .enumerate()
                    .map(|(id, v)| {
                        format!(
                            "\t{} = {}",
                            frame.sp + id,
                            match v {
                                Some(v) => format!("{:?}", v.to_string(self)),
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
        SymbolID,
        compiling::driver::Driver,
        interpret::{
            interpreter::{IRInterpreter, InterpreterError},
            io::test_io::TestIO,
            value::Value,
        },
        transforms::monomorphizer::Monomorphizer,
    };

    fn interpret(code: &'static str) -> Result<Value, InterpreterError> {
        let mut io = TestIO::new();
        interpret_io(code, &mut io)
    }

    fn interpret_io(code: &'static str, io: &mut TestIO) -> Result<Value, InterpreterError> {
        let mut driver = Driver::with_str(code);
        let unit = driver.lower().into_iter().next().unwrap();

        let diagnostics = driver.refresh_diagnostics_for(&PathBuf::from("-")).unwrap();

        if !diagnostics.is_empty() {
            return Err(InterpreterError::InvalidProgram);
        }

        let module = unit.module();
        let mono = Monomorphizer::new(&unit.env).run(module);

        IRInterpreter::new(mono, io, &driver.symbol_table).run()
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
        assert_eq!(Value::Float(3.0), interpret("1.0 + 2.0").unwrap());
        assert!(interpret("true + false").is_err());
    }

    #[test]
    fn interprets_sub() {
        assert_eq!(Value::Int(-1), interpret("1 - 2").unwrap());
        assert_eq!(Value::Float(-1.0), interpret("1.0 - 2.0").unwrap());
        assert!(interpret("true - false").is_err());
    }

    #[test]
    fn interprets_mul() {
        assert_eq!(Value::Int(6), interpret("2 * 3").unwrap());
        assert_eq!(Value::Float(6.0), interpret("2.0 * 3.0").unwrap());
        assert!(interpret("true * false").is_err());
    }

    #[test]
    fn interprets_div() {
        assert_eq!(Value::Int(3), interpret("6 / 2").unwrap());
        assert_eq!(Value::Float(3.0), interpret("6.0 / 2.0").unwrap());
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
    fn interprets_fib() {
        let res = interpret(
            "
        func fib(n) {
          if n <= 1 {
            n
          } else {
            fib(n - 2) + fib(n - 1)
          }
        }

        let i = 0
        let n = 0

        loop i < 10 {
          n = fib(i)
          i = i + 1
        }

        n
        ",
        )
        .unwrap();

        assert_eq!(res, Value::Int(34))
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
                (b, a.count)
        "
            )
            .unwrap(),
            Value::Struct(SymbolID::TUPLE, vec![Value::Int(3), Value::Int(2)]),
        )
    }

    #[test]
    fn interprets_struct_init() {
        assert_eq!(
            interpret(
                "
            struct Person {
                let age: Int

                init(age: Int) {
                    self.age = age
                }
            }

            Person(age: 123).age
        "
            )
            .unwrap(),
            Value::Int(123),
        )
    }

    #[test]
    fn interprets_protocol_method_call() {
        assert_eq!(
            interpret(
                "
            protocol Aged {
                func getAge() -> Int
            }

            struct Person: Aged {
                func getAge() {
                    123
                }
            }

            func get<T: Aged>(t: T) {
                t.getAge()
            }

            get(Person())"
            )
            .unwrap(),
            Value::Int(123)
        );
    }

    #[test]
    fn interprets_string() {
        let Value::Struct(sym, fields) = interpret("\"hello world\"").unwrap() else {
            panic!("did not get struct");
        };
        assert_eq!(sym, SymbolID::STRING);
        assert_eq!(fields[0], Value::Int(11));
        assert_eq!(fields[1], Value::Int(11));
    }

    #[test]
    fn interprets_ir_instr() {
        assert_eq!(
            interpret(
                "
                let x = 2
                let y = 3
                __ir_instr(\"$? = add int %0, %1;\")
            "
            )
            .unwrap(),
            Value::Int(5)
        )
    }

    #[test]
    fn interprets_string_append() {
        let Value::Struct(sym, fields) = interpret(
            r#"
            let a = ""
            a.append("hello ")
            a.append("world")
            a
        "#,
        )
        .unwrap() else {
            panic!("did not get struct");
        };
        assert_eq!(sym, SymbolID::STRING);
        assert_eq!(fields[0], Value::Int(11));
        assert_eq!(fields[1], Value::Int(11));
    }

    #[test]
    fn interprets_io() {
        let mut io = TestIO::new();
        interpret_io("print(123)", &mut io).unwrap();
        assert_eq!("123\n".as_bytes(), io.stdout())
    }

    #[test]
    fn interprets_string_special_case() {
        let mut io = TestIO::new();
        interpret_io(
            r#"
            print("hello world")
            "#,
            &mut io,
        )
        .unwrap();
        assert_eq!("hello world\n", str::from_utf8(&io.stdout()).unwrap())
    }

    #[test]
    fn interprets_print_struct() {
        let mut io = TestIO::new();
        interpret_io(
            r#"
            struct Person {
                let name: String
                let age: Int
            }

            let person = Person(name: "Pat", age: 123)
            print(person)
            "#,
            &mut io,
        )
        .unwrap();
        assert_eq!(
            "Person(name: \"Pat\", age: 123)\n",
            str::from_utf8(&io.stdout()).unwrap()
        )
    }

    #[test]
    fn interprets_more_fib() {
        interpret(
            "
        func fib(n) {
            if n <= 1 { return n }

            return fib(n - 2) + fib(n - 1)
        }

        let i = 0

        // Calculate some numbers
        loop i < 15 {
            print(fib(i))
            i = i + 1
        }
        ",
        )
        .unwrap();
    }
}
