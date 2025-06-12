use std::collections::HashMap;

use crate::{
    interpreter::{
        heap::{Heap, Pointer},
        value::Value,
    },
    lowering::{
        instr::Instr,
        ir_module::IRModule,
        lowerer::{BasicBlock, BasicBlockID, IRError, IRFunction, RefKind, Register, RegisterList},
    },
};

#[derive(Debug)]
pub enum InterpreterError {
    NoMainFunc,
    CalleeNotFound,
    PredecessorNotFound,
    TypeError(Value, Value),
    UnreachableReached,
    IRError(IRError),
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
    program: IRModule,
    stack: Vec<StackFrame>,
    heap: Heap,
}

impl IRInterpreter {
    pub fn new(program: IRModule) -> Self {
        Self {
            program,
            stack: vec![],
            heap: Heap::new(),
        }
    }

    pub fn run(&mut self) -> Result<Value, InterpreterError> {
        let main = self
            .program
            .functions
            .iter()
            .position(|f| f.name == "@main");
        if let Some(main) = main {
            self.execute_function(self.load_function(&Pointer(main)).unwrap(), vec![])
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
        log::trace!("PC: {:?}", self.stack.last().unwrap().pc);
        log::trace!("Reg: {:?}", self.stack.last().unwrap().registers);
        log::trace!("{instr:?}");

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

                for (reg, pred) in &predecessors.0 {
                    if frame.pred == Some(*pred) {
                        log::trace!("Phi check {:?}: {:?} ({:?})", reg, pred, frame.pred);
                        self.set_register_value(&dest, self.register_value(reg));
                        self.stack.last_mut().unwrap().pc += 1;
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
                    .unwrap();
                self.set_register_value(&dest, Value::Func(Pointer(idx)));
            }
            Instr::Call {
                dest_reg,
                callee,
                args,
                ..
            } => {
                // 1. The `callee` register holds a `Value::Func` variant containing the mangled name
                //    of the function to be called. We first get this value.
                let callee_value = self.register_value(&callee.try_register().unwrap());
                let callee_id = match callee_value {
                    Value::Func(id) => id,
                    _ => panic!(
                        "Interpreter error: Expected a function in the callee register, but got {callee_value:?}."
                    ),
                };

                // 2. We use the function name to look up the corresponding `IRFunction`
                //    definition from the program's module.
                let Some(function_to_call) = self.load_function(&callee_id) else {
                    return Err(InterpreterError::CalleeNotFound);
                };

                // 3. The `args` list contains the registers for the arguments. The first argument
                //    is always the environment pointer for the closure, followed by the
                //    user-specified arguments. We resolve these registers to their current values.
                let arg_values = self.register_values(&args);

                // 4. We call `execute_function`, which handles pushing a new stack frame,
                //    running the function's code, and returning the result. This is a synchronous
                //    operation within the interpreter.
                let result = self.execute_function(function_to_call, arg_values)?;

                // 5. Once the function returns, `execute_function` pops the callee's stack frame.
                //    We are now back in the caller's frame. We take the return value and
                //    store it in the destination register specified by the `Call` instruction.
                self.set_register_value(&dest_reg, result);
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
            Instr::Ret(_ret, reg) => {
                if let Some(reg) = reg {
                    let retval = self.register_value(&reg);
                    self.stack.pop();
                    return Ok(Some(retval));
                } else {
                    self.stack.pop();
                    return Ok(Some(Value::Void));
                }
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
                        values: values.0.iter().map(|r| self.register_value(r)).collect(),
                    },
                );
            }
            Instr::GetEnumTag(dest, enum_reg) => {
                let Value::Enum { tag, .. } = self.register_value(&enum_reg) else {
                    panic!("did not find enum in register #{enum_reg:?}");
                };

                self.set_register_value(&dest, Value::Int(tag as i64));
            }
            Instr::GetEnumValue(dest, _, enum_reg, _tag, value) => {
                // Tag would be useful if we needed to know about memory layout but since we're
                // just using objects who cares
                let Value::Enum { values, .. } = self.register_value(&enum_reg) else {
                    panic!("did not find enum in register #{enum_reg:?}");
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
            Instr::Alloc { dest, count, ty } => {
                let ptr = self.heap.alloc(ty.mem_size() * count);
                self.set_register_value(&dest, Value::Pointer(ptr));
            }
            Instr::Store { val, location, ty } => {
                let Value::Pointer(ptr) = self.register_value(&location) else {
                    panic!("no pointer at location: {location}")
                };

                self.heap.store(&ptr, &self.register_value(&val), &ty)
            }
            Instr::Load { dest, addr, ty } => {
                let Value::Pointer(ptr) = self.register_value(&addr) else {
                    panic!("no pointer at location: {addr}")
                };

                let val = self.heap.load(&ptr, &ty);
                self.set_register_value(&dest, val.clone());
            }
            Instr::GetElementPointer {
                dest,
                from,
                index,
                ty,
            } => {
                let Value::Pointer(ptr) = self.register_value(&from) else {
                    panic!(
                        "no pointer found in register: {} in {:?}",
                        from,
                        self.stack.last().unwrap().registers
                    );
                };

                let pointer = ty
                    .get_element_pointer(ptr, index)
                    .map_err(|e| InterpreterError::IRError(e))?;

                self.set_register_value(&dest, Value::Pointer(pointer));
            }
            Instr::MakeStruct { dest, values, .. } => {
                let structure = Value::Struct(self.register_values(&values));
                self.set_register_value(&dest, structure);
            }
            Instr::GetValueOf { .. } => todo!(),
        }

        self.stack.last_mut().unwrap().pc += 1;

        Ok(None)
    }

    fn current_basic_block(&self) -> &BasicBlock {
        let frame = self.stack.last().unwrap();
        &frame.function.blocks[frame.block_idx]
    }

    fn set_register_value(&mut self, register: &Register, value: Value) {
        log::trace!("set {register:?} to {value:?}");
        self.stack
            .last_mut()
            .expect("Stack underflow")
            .registers
            .insert(*register, value);
    }

    fn register_values(&self, registers: &RegisterList) -> Vec<Value> {
        registers
            .0
            .iter()
            .map(|r| self.register_value(r).clone())
            .collect()
    }

    fn register_value(&self, register: &Register) -> Value {
        self.stack
            .last()
            .expect("Stack underflow")
            .registers
            .get(register)
            .unwrap_or_else(|| {
                panic!(
                    "No value found for register: {:?}, {:?}",
                    register,
                    self.stack.last().unwrap().registers
                )
            })
            .clone()
    }

    fn load_function(&self, idx: &Pointer) -> Option<IRFunction> {
        self.program.functions.get(idx.0).cloned()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        SymbolTable, check,
        interpreter::{
            interpreter::{IRInterpreter, InterpreterError},
            value::Value,
        },
        lowering::{ir_module::IRModule, lowerer::Lowerer},
    };

    fn interpret(code: &'static str) -> Result<Value, InterpreterError> {
        let typed = check(code).unwrap();
        let mut symbol_table = SymbolTable::default();
        let lowerer = Lowerer::new(typed, &mut symbol_table);
        let mut module = IRModule::new();
        lowerer.lower(&mut module).unwrap();

        // println!("{}", crate::lowering::ir_printer::print(&module));

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
}
