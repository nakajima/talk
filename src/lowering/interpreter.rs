use std::collections::HashMap;

use crate::lowering::{
    instr::Instr,
    ir_module::IRModule,
    lowerer::{BasicBlock, BasicBlockID, IRFunction, IRType, RefKind, Register, RegisterList},
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
    program: IRModule,
    stack: Vec<StackFrame>,
    heap: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pointer(usize, Option<usize>);

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Enum { tag: u16, values: Vec<Value> },
    Void,
    Struct(Vec<Value>),
    Pointer(Pointer),
    Func(String),
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

    fn gt(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a > b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    fn gte(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a >= b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    fn lt(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a < b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }

    fn lte(&self, other: &Value) -> Result<Value, InterpreterError> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
            (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a <= b)),
            _ => Err(InterpreterError::TypeError(self.clone(), other.clone())),
        }
    }
}

impl IRInterpreter {
    pub fn new(program: IRModule) -> Self {
        Self {
            program,
            stack: vec![],
            heap: vec![],
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
                self.set_register_value(&dest, Value::Func(name));
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
                let callee_name = match callee_value {
                    Value::Func(name) => name,
                    _ => panic!(
                        "Interpreter error: Expected a function in the callee register, but got {callee_value:?}."
                    ),
                };

                // 2. We use the function name to look up the corresponding `IRFunction`
                //    definition from the program's module.
                let Some(function_to_call) = self.load_function(&callee_name) else {
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
            Instr::Alloc { dest, ty } => {
                let ptr = self.alloc(ty);
                self.set_register_value(&dest, Value::Pointer(ptr));
            }
            Instr::Store { val, location, .. } => {
                let Value::Pointer(ptr) = self.register_value(&location) else {
                    panic!("no pointer at location: {location}")
                };

                self.store(&ptr, self.register_value(&val))
            }
            Instr::Load { dest, addr, .. } => {
                let Value::Pointer(ptr) = self.register_value(&addr) else {
                    panic!("no pointer at location: {addr}")
                };

                let val = self.load(ptr);
                self.set_register_value(&dest, val.clone());
            }
            Instr::GetElementPointer {
                dest, from, index, ..
            } => {
                let Value::Pointer(ptr) = self.register_value(&from) else {
                    panic!(
                        "no pointer found in register: {} in {:?}",
                        from,
                        self.stack.last().unwrap().registers
                    );
                };

                self.set_register_value(&dest, Value::Pointer(Pointer(ptr.0, Some(index))));
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

    fn alloc(&mut self, ty: IRType) -> Pointer {
        let i = self.heap.len();
        let initial_value = match ty {
            IRType::Struct(vals) => Value::Struct(vals.iter().map(|_| Value::Void).collect()),
            _ => Value::Void,
        };
        self.heap.push(initial_value);
        Pointer(i, None)
    }

    fn load(&self, pointer: Pointer) -> &Value {
        if let Some(offset) = pointer.1 {
            let Value::Struct(vals) = &self.heap[pointer.0] else {
                panic!("invalid index for pointer: {pointer:?}");
            };

            &vals[offset]
        } else {
            &self.heap[pointer.0]
        }
    }

    fn store(&mut self, pointer: &Pointer, val: Value) {
        if let Some(offset) = pointer.1 {
            let Value::Struct(vals) = &mut self.heap[pointer.0] else {
                panic!(
                    "invalid index for pointer: {:?}\nheap: {:?}",
                    pointer, self.heap
                );
            };

            vals[offset] = val
        } else {
            self.heap[pointer.0] = val
        }
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
        SymbolTable, check,
        lowering::{
            interpreter::{IRInterpreter, InterpreterError, Value},
            ir_module::IRModule,
            lowerer::Lowerer,
        },
    };

    fn interpret(code: &'static str) -> Result<Value, InterpreterError> {
        let typed = check(code).unwrap();
        let mut symbol_table = SymbolTable::default();
        let lowerer = Lowerer::new(typed, &mut symbol_table);
        let mut module = IRModule::new();
        lowerer.lower(&mut module).unwrap();

        // println!("{}", print(&module));

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
