use std::fmt::Display;

use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
    ir::{
        basic_block::{BasicBlock, BasicBlockId, Phi},
        function::Function,
        instruction::{CmpOperator, Instruction},
        ir_ty::IrTy,
        program::Program,
        register::Register,
        terminator::Terminator,
        value::{Addr, Reference, Value},
    },
    label::Label,
    name_resolution::symbol::{Symbol, set_symbol_names},
};

// #[derive(Debug, Clone, PartialEq)]
// pub enum Value {
//     Int(i64),
//     Float(f64),
//     Bool(bool),
//     Record(Option<Symbol>, Vec<Value>),
//     Func(Symbol),
//     Void,
//     Ref(Reference),
//     RawPtr(usize),
//     Buffer(Vec<u8>),
//     Uninit,
// }

#[allow(clippy::panic)]
#[allow(clippy::should_implement_trait)]
impl Value {
    pub fn add(self, other: Value) -> Value {
        match (&self, &other) {
            (Self::Int(lhs), Self::Int(rhs)) => Self::Int(lhs + rhs),
            (Self::Float(lhs), Self::Float(rhs)) => Self::Float(lhs + rhs),
            // Pointer arithmetic: RawPtr + Int -> RawPtr
            (Self::RawPtr(ptr), Self::Int(offset)) => Self::RawPtr(Addr(ptr.0 + *offset as usize)),
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
pub struct Memory {
    pub mem: Vec<u8>,
}

pub struct Interpreter {
    program: Program,
    symbol_names: Option<FxHashMap<Symbol, String>>,
    frames: Vec<Frame>,
    current_func: Option<Function<IrTy>>,
    main_result: Option<Value>,
    memory: Memory,
    heap_start: usize,
}

#[allow(clippy::unwrap_used)]
#[allow(clippy::expect_used)]
#[allow(clippy::panic)]
impl Interpreter {
    pub fn new(program: Program, symbol_names: Option<FxHashMap<Symbol, String>>) -> Self {
        let heap_start = program.static_memory.data.len();

        Self {
            program,
            frames: Default::default(),
            current_func: None,
            main_result: None,
            memory: Default::default(),
            heap_start,
            symbol_names,
        }
    }

    pub fn run(mut self) -> Value {
        if std::env::var("SHOW_IR").is_ok() {
            let _guard = self
                .symbol_names
                .as_ref()
                .map(|names| set_symbol_names(names.clone()));
            println!("{}", self.program);
        }

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
                let _guard = self
                    .symbol_names
                    .as_ref()
                    .map(|names| set_symbol_names(names.clone()));

                panic!(
                    "did not find function: {} {:?}",
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

        tracing::trace!("{}", self.display_ir(&next_instruction));

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
                let mut arg_vals: Vec<Value> =
                    args.items.iter().map(|v| self.val(v.clone())).collect();

                let func = match self.val(callee) {
                    Value::Closure { func, env } => {
                        // Evaluate env values and prepend as a record
                        let env_vals: Vec<Value> =
                            env.items.iter().map(|v| self.val(v.clone())).collect();
                        arg_vals.insert(0, Value::Record(None, env_vals));
                        func
                    }
                    other => self.func(other),
                };

                self.call(func, arg_vals, dest);
            }
            IR::Instr(Instruction::Nominal {
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
                let Value::Record(sym, fields) = self.read_register(&record) else {
                    panic!(
                        "did not get record from {record:?}: {:?}",
                        self.read_register(&record)
                    );
                };

                let idx = match field {
                    Label::Positional(idx) => idx,
                    Label::Named(name) => {
                        panic!("named field access not supported for {sym:?}.{name}");
                    }
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
                    super::value::Value::Func(name) => Reference::Func(name),
                    super::value::Value::Reg(reg) => Reference::Register {
                        frame: self.frames.len(),
                        register: reg.into(),
                    },
                    Value::Closure { func, .. } => Reference::Func(func),
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
            IR::Instr(Instruction::_Print { val }) => {
                let val = self.val(val.clone());
                println!("{}", self.display(val));
            }
            IR::Instr(Instruction::Alloc { dest, ty, count }) => {
                let count = match self.val(count) {
                    Value::Int(n) => n as usize,
                    v => panic!("alloc count must be int, got {v:?}"),
                };

                // Address in unified space = heap_start + current heap size
                let addr = self.heap_start + self.memory.mem.len();

                // Extend heap with zeroed bytes
                self.memory
                    .mem
                    .resize(self.memory.mem.len() + ty.bytes_len() + count, 0);

                self.write_register(&dest, Value::RawPtr(Addr(addr)));
            }
            IR::Instr(Instruction::Copy {
                ty: _,
                from,
                to,
                length,
            }) => {
                let from_addr = match self.val(from) {
                    Value::RawPtr(a) => a,
                    Value::Int(a) => Addr(a as usize),
                    v => panic!("copy from must be RawPtr or Int, got {v:?}"),
                };
                let to_addr = match self.val(to) {
                    Value::RawPtr(a) => a,
                    Value::Int(a) => Addr(a as usize),
                    v => panic!("copy to must be RawPtr or Int, got {v:?}"),
                };
                let len = match self.val(length) {
                    Value::Int(n) => n as usize,
                    v => panic!("copy length must be Int, got {v:?}"),
                };

                for i in 0..len {
                    // Read byte from source
                    let byte = if from_addr.0 < self.heap_start {
                        // Source is in static memory
                        self.program.static_memory.data[from_addr.0 + i]
                    } else {
                        // Source is in heap
                        self.memory.mem[from_addr.0 - self.heap_start + i]
                    };

                    // Write byte to destination (must be heap, since static is read-only)
                    let heap_idx = to_addr.0 - self.heap_start + i;
                    self.memory.mem[heap_idx] = byte;
                }
            }
            IR::Instr(Instruction::Load { dest, ty, addr }) => {
                let addr_val = self.val(addr);
                let Value::RawPtr(ptr) = addr_val else {
                    panic!("Load expects RawPtr, got {addr_val:?}");
                };

                let size = ty.bytes_len();
                let bytes = if ptr.0 < self.heap_start {
                    // Static memory
                    &self.program.static_memory.data[ptr.0..ptr.0 + size]
                } else {
                    // Heap memory
                    let heap_idx = ptr.0 - self.heap_start;
                    &self.memory.mem[heap_idx..heap_idx + size]
                };

                let value = match ty {
                    IrTy::Int => Value::Int(i64::from_le_bytes(bytes.try_into().unwrap())),
                    IrTy::Float => Value::Float(f64::from_le_bytes(bytes.try_into().unwrap())),
                    IrTy::Bool => Value::Bool(bytes[0] != 0),
                    IrTy::RawPtr => {
                        Value::RawPtr(Addr(usize::from_le_bytes(bytes.try_into().unwrap())))
                    }
                    _ => panic!("Load not implemented for {ty:?}"),
                };
                self.write_register(&dest, value);
            }

            IR::Instr(Instruction::Store { value, addr, .. }) => {
                let val = self.val(value);
                let addr_val = self.val(addr);
                let Value::RawPtr(ptr) = addr_val else {
                    panic!("Store expects RawPtr, got {addr_val:?}");
                };

                let bytes = val.as_bytes();
                let heap_idx = ptr.0 - self.heap_start;

                for (i, byte) in bytes.iter().enumerate() {
                    self.memory.mem[heap_idx + i] = *byte;
                }
            }

            IR::Instr(Instruction::Move { from, to, .. }) => {
                // Move is like Store but maybe with different semantics?
                // If it's the same as Store:
                let val = self.val(from);
                let addr_val = self.val(to);
                let Value::RawPtr(ptr) = addr_val else {
                    panic!("Move expects RawPtr destination, got {addr_val:?}");
                };

                let bytes = val.as_bytes();
                let heap_idx = ptr.0 - self.heap_start;

                for (i, byte) in bytes.iter().enumerate() {
                    self.memory.mem[heap_idx + i] = *byte;
                }
            }
            IR::Instr(Instruction::Free { .. }) => unimplemented!(),
        }
    }

    fn display_ir(&self, ir: &IR) -> String {
        if let Some(names) = &self.symbol_names {
            let _guard = set_symbol_names(names.clone());
            format!("{ir}")
        } else {
            format!("{ir}")
        }
    }

    fn display(&mut self, val: Value) -> String {
        match val {
            Value::Int(val) => format!("{val}"),
            Value::Reg(reg) => format!("%{reg}"),
            Value::Capture { .. } => format!("{val}"),
            Value::Poison => "<POISON>".to_string(),
            Value::Float(val) => format!("{val}"),
            Value::Bool(val) => format!("{val}"),
            Value::Record(sym, values) => {
                if sym == Some(Symbol::String) {
                    let Value::RawPtr(addr) = &values[0] else {
                        unreachable!()
                    };

                    let Value::Int(len) = &values[1] else {
                        unreachable!()
                    };
                    let len = *len as usize;

                    let bytes: Vec<u8> = if addr.0 < self.heap_start {
                        // String is in static memory
                        self.program.static_memory.data[addr.0..addr.0 + len].to_vec()
                    } else {
                        // String is in heap memory
                        let heap_idx = addr.0 - self.heap_start;
                        self.memory.mem[heap_idx..heap_idx + len].to_vec()
                    };

                    let s = str::from_utf8(&bytes).unwrap();
                    return s.to_string();
                }

                let values = values.into_iter().map(|v| self.display(v)).collect_vec();
                let name = if let Some(sym) = sym {
                    self.sym_to_str(&sym)
                } else {
                    "".to_string()
                };

                format!("{name:?}({values:?})")
            }
            Value::Func(symbol) => format!("func {}()", self.sym_to_str(&symbol)),
            Value::Closure { func, env } => format!("func {}[{env}]()", self.sym_to_str(&func)),
            Value::Void => "void".into(),
            Value::RawPtr(val) => format!("rawptr({})", val.0),
            Value::Ref(reference) => match reference {
                Reference::Func(sym) => format!("func {}()", self.sym_to_str(&sym)),
                _ => format!("{reference:?}"),
            },
            Value::Uninit => "UNINIT".into(),
            Value::Buffer(bytes) => format!("buf({bytes:?})"),
        }
    }

    fn sym_to_str(&self, sym: &Symbol) -> String {
        if let Some(symbol_names) = &self.symbol_names {
            symbol_names
                .get(sym)
                .expect("did not get symbol name")
                .clone()
        } else {
            format!("{sym:?}")
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

    fn func(&self, val: Value) -> Symbol {
        match val {
            Value::Reg(reg) => match self.read_register(&Register(reg)) {
                Value::Func(symbol) => symbol,
                Value::Closure { func, .. } => func,
                _ => panic!(
                    "didn't get func symbol from {val:?}: {:?}",
                    self.read_register(&Register(reg))
                ),
            },
            Value::Func(name) => name,
            _ => panic!("cannot get func from {val:?}"),
        }
    }

    fn val(&mut self, val: Value) -> Value {
        match val {
            super::value::Value::Reg(reg) => self.read_register(&Register(reg)),
            super::value::Value::Closure { func, env } => {
                // Resolve env values now, while we're in the right frame
                let resolved_env: Vec<Value> =
                    env.items.iter().map(|v| self.val(v.clone())).collect();
                Value::Closure {
                    func,
                    env: resolved_env.into(),
                }
            }
            super::value::Value::Poison => panic!("unreachable reached"),
            _ => val,
        }
    }
}

#[cfg(test)]
pub mod tests {
    use crate::ir::{lowerer_tests::tests::lower_module, value::Addr};

    use super::*;

    pub fn interpret(input: &str) -> Value {
        let module = lower_module(input);
        let interpreter = Interpreter::new(module.program, Some(module.symbol_names));
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

    #[test]
    fn interprets_string_plus() {
        assert_eq!(
            interpret("let a = \"hello \" + \"world\"; a"),
            Value::Record(
                Some(Symbol::String),
                vec![Value::RawPtr(Addr(11)), Value::Int(11), Value::Int(11)]
            )
        );
    }

    #[test]
    fn interprets_closure() {
        assert_eq!(
            interpret(
                "
            let a = 123
            func b() { a }
            b()
            "
            ),
            Value::Int(123)
        );
    }

    #[test]
    fn interprets_nested_closure() {
        assert_eq!(
            interpret(
                "
            let a = 123
            func b() {
                func c() {
                    a
                }
                c
            }
            b()()
            "
            ),
            Value::Int(123)
        );
    }
}
