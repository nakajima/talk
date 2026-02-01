use std::fmt::Display;

use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::span::EnteredSpan;

use crate::{
    ir::{
        basic_block::{BasicBlock, BasicBlockId, Phi},
        function::Function,
        instruction::{CmpOperator, Instruction, InstructionMeta},
        ir_ty::IrTy,
        list::List,
        program::Program,
        register::Register,
        terminator::Terminator,
        value::{Addr, RecordId, Reference, Value},
    },
    label::Label,
    name_resolution::symbol::{Symbol, set_symbol_names},
};

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
    func: Symbol,
    dest: Register,
    ret: Option<Symbol>,
    registers: Vec<Value>,
    pc: usize,
    current_block: usize,
    prev_block: Option<usize>,
    self_dest: Option<Register>,
    _span: EnteredSpan,
}

impl Frame {
    pub fn new(
        span: EnteredSpan,
        func: Symbol,
        dest: Register,
        ret: Option<Symbol>,
        self_dest: Option<Register>,
    ) -> Self {
        Self {
            func,
            _span: span,
            ret,
            dest,
            registers: Default::default(),
            pc: 0,
            current_block: 0,
            prev_block: None,
            self_dest,
        }
    }
}

impl Clone for Frame {
    fn clone(&self) -> Self {
        let span = tracing::trace_span!("call", func = format!("{:?}", self.func)).entered();
        Self {
            func: self.func,
            dest: self.dest,
            ret: self.ret,
            registers: self.registers.clone(),
            pc: self.pc,
            current_block: self.current_block,
            prev_block: self.prev_block,
            self_dest: self.self_dest,
            _span: span,
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

pub struct Interpreter<IO: super::io::IO> {
    program: Program,
    symbol_names: Option<FxHashMap<Symbol, String>>,
    pub frames: Vec<Frame>,
    current_func: Option<Function<IrTy>>,
    pub main_result: Option<Value>,
    memory: Memory,
    heap_start: usize,
    pub io: IO,
}

#[allow(clippy::unwrap_used)]
#[allow(clippy::expect_used)]
#[allow(clippy::panic)]
impl<IO: super::io::IO> Interpreter<IO> {
    pub fn new(program: Program, symbol_names: Option<FxHashMap<Symbol, String>>, io: IO) -> Self {
        let heap_start = program.static_memory.data.len();

        Self {
            program,
            frames: Default::default(),
            current_func: None,
            main_result: None,
            memory: Default::default(),
            heap_start,
            symbol_names,
            io,
        }
    }

    pub fn run(&mut self) -> Value {
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

        self.call(entrypoint.name, vec![], Register::MAIN, None);

        while !self.frames.is_empty() {
            self.next();
        }

        self.main_result.clone().unwrap_or(Value::Void)
    }

    pub fn call(
        &mut self,
        function: Symbol,
        args: Vec<Value>,
        dest: Register,
        self_dest: Option<Register>,
    ) {
        let caller_name = self.current_func.as_ref().map(|f| f.name);
        if let Some(callee_func) = self.current_func.take() {
            self.program.functions.insert(callee_func.name, callee_func);
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
                    "did not find function: {:?} {:?}",
                    function,
                    self.program
                        .functions
                        .iter()
                        .map(|f| &f.1.name)
                        .collect_vec()
                )
            });

        if func.blocks.is_empty() {
            return;
        }

        let _guard = self
            .symbol_names
            .as_ref()
            .map(|names| set_symbol_names(names.clone()));
        let span = tracing::trace_span!("call", func = format!("{function}")).entered();
        let mut frame = Frame::new(span, function, dest, caller_name, self_dest);
        frame.registers.resize(func.register_count, Value::Uninit);
        for (param, arg) in func.params.items.iter().zip(args.into_iter()) {
            match param {
                Value::Reg(reg) => {
                    frame.registers[*reg as usize] = arg;
                }
                other => panic!("unsupported param binding {other:?}"),
            }
        }
        self.frames.push(frame);
        self.current_func = Some(func);

        tracing::trace!("{:?}", self.frames.last().unwrap());
    }

    /// Call an effectful function compiled as a state machine.
    /// This drives the poll loop until the function completes.
    ///
    /// The poll function has signature:
    ///   (state: Int, state_data: Record, resumed: T) -> (Int, Record, Poll<R>)
    ///
    /// Where Poll is either:
    ///   - Ready(result)
    ///   - Pending(effect, args)
    #[allow(dead_code)]
    pub fn call_effectful(
        &mut self,
        poll_func: Symbol,
        _initial_args: Vec<Value>,
        effect_handler: impl Fn(&mut Self, Symbol, Vec<Value>) -> Value,
    ) -> Value {
        let mut state = 0i64;
        let mut state_data = Value::Record(RecordId::Anon, vec![]);
        let mut resumed = Value::Void;

        loop {
            // Build the poll function arguments: (state, state_data, resumed)
            let poll_args = vec![Value::Int(state), state_data.clone(), resumed];

            // Call the poll function
            let dest_reg = self.current_func.as_ref().map_or(Register(0), |_| {
                let reg = Register(self.frames.last().map_or(0, |f| f.registers.len() as u32));
                reg
            });
            self.call(poll_func, poll_args, dest_reg, None);

            // Run until the call returns
            while !self.frames.is_empty() {
                self.next();
            }

            // The result is a tuple: (next_state, state_data, poll_result)
            let result = self.main_result.take().unwrap_or(Value::Void);

            let Value::Record(_, fields) = result else {
                // Not a valid state machine result, return as-is
                return result;
            };

            if fields.len() < 3 {
                // Not a valid state machine result
                return Value::Record(RecordId::Anon, fields);
            }

            // Extract components
            let new_state = match &fields[0] {
                Value::Int(s) => *s,
                _ => return Value::Record(RecordId::Anon, fields),
            };

            state_data = fields[1].clone();
            let poll_result = fields[2].clone();

            // Check if we have Ready or Pending
            // For now, we use a simple convention:
            // - If poll_result is a Record with tag 0, it's Pending(effect, args)
            // - If poll_result is a Record with tag 1, it's Ready(value)
            // - Otherwise, it's the final result (simplified)

            match &poll_result {
                Value::Record(_, inner_fields) if !inner_fields.is_empty() => {
                    match &inner_fields[0] {
                        Value::Int(0) => {
                            // Pending - extract effect and args, call handler
                            let effect_sym = if inner_fields.len() > 1 {
                                match &inner_fields[1] {
                                    Value::Func(s) => *s,
                                    _ => Symbol::Main, // Placeholder
                                }
                            } else {
                                Symbol::Main
                            };

                            let effect_args = if inner_fields.len() > 2 {
                                match &inner_fields[2] {
                                    Value::Record(_, args) => args.clone(),
                                    v => vec![v.clone()],
                                }
                            } else {
                                vec![]
                            };

                            // Call the effect handler to get the resumed value
                            resumed = effect_handler(self, effect_sym, effect_args);
                            state = new_state;
                        }
                        Value::Int(1) => {
                            // Ready - return the value
                            return if inner_fields.len() > 1 {
                                inner_fields[1].clone()
                            } else {
                                Value::Void
                            };
                        }
                        _ => {
                            // Unknown poll result format, assume it's the final value
                            return poll_result;
                        }
                    }
                }
                _ => {
                    // Not a Poll enum, assume it's the final result
                    return poll_result;
                }
            }
        }
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
                // Get mutated self from self_out register (if this is a method)
                let self_val = self
                    .current_func
                    .as_ref()
                    .and_then(|f| f.self_out)
                    .map(|reg| self.frames.last().unwrap().registers[reg.0 as usize].clone());
                let frame = self.frames.pop().unwrap();

                self.write_register(&frame.dest, val);

                // Write back mutated self to caller's register
                if let Some(self_dest) = frame.self_dest {
                    if let Some(sv) = self_val {
                        self.write_register(&self_dest, sv);
                    }
                }

                let Some(func) = self.current_func.take() else {
                    unreachable!("but where did the frame come from");
                };

                self.program.functions.insert(func.name, func);

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
                } else if cond_val == Value::Bool(false) {
                    alt
                } else {
                    panic!("Branch condition not a bool: {cond_val:?}");
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
                dest,
                callee,
                args,
                self_dest,
                ..
            }) => {
                let mut arg_vals: Vec<Value> =
                    args.items.iter().map(|v| self.val(v.clone())).collect();

                let val = self.val(callee);
                let (func, env) = self.func(val);
                if !env.items.is_empty() {
                    let env_vals: Vec<Value> =
                        env.items.iter().map(|v| self.val(v.clone())).collect();
                    arg_vals.insert(0, Value::Record(RecordId::Anon, env_vals));
                }

                self.call(func, arg_vals, dest, self_dest);
            }
            IR::Instr(Instruction::Nominal {
                dest,
                record,
                sym,
                meta,
                ..
            }) => {
                let record_id = if let Some(InstructionMeta::RecordId(id)) = meta
                    .items
                    .iter()
                    .find(|meta| matches!(meta, InstructionMeta::RecordId(..)))
                {
                    *id
                } else {
                    RecordId::Nominal(sym)
                };

                let fields = record.items.iter().map(|v| self.val(v.clone())).collect();
                self.write_register(&dest, Value::Record(record_id, fields));
            }
            IR::Instr(Instruction::Record {
                dest, record, meta, ..
            }) => {
                let record_id = if let Some(InstructionMeta::RecordId(id)) = meta
                    .items
                    .iter()
                    .find(|meta| matches!(meta, InstructionMeta::RecordId(..)))
                {
                    *id
                } else {
                    RecordId::Anon
                };

                let fields = record.items.iter().map(|v| self.val(v.clone())).collect();
                self.write_register(&dest, Value::Record(record_id, fields));
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
                    Label::_Symbol(..) => {
                        panic!("symbol field access not supported for {sym:?}");
                    }
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
                    Value::Closure { func, env } => Reference::Closure(
                        func,
                        env.items
                            .into_iter()
                            .map(|f| self.val(f))
                            .collect_vec()
                            .into(),
                    ),
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
                let val = self.display(val, false);
                let val = format!("{val}\n");
                let bytes = val.as_bytes();
                self.io
                    .write_stdout(bytes)
                    .expect("unable to write to stdout");
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
                    .resize(self.memory.mem.len() + ty.bytes_len() * count, 0);

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

                let value = self.bytes_to_value(&ty, bytes);
                self.write_register(&dest, value);
            }

            IR::Instr(Instruction::Store {
                value, addr, ty, ..
            }) => {
                let val = self.val(value);
                let addr_val = self.val(addr);
                let Value::RawPtr(ptr) = addr_val else {
                    panic!("Store expects RawPtr, got {addr_val:?}");
                };

                let bytes = self.value_to_bytes(&ty, val);
                if bytes.len() != ty.bytes_len() {
                    panic!(
                        "Store size mismatch: expected {} bytes, got {}",
                        ty.bytes_len(),
                        bytes.len()
                    );
                }
                let heap_idx = ptr.0 - self.heap_start;

                for (i, byte) in bytes.iter().enumerate() {
                    self.memory.mem[heap_idx + i] = *byte;
                }
            }

            IR::Instr(Instruction::Move { from, to, ty, .. }) => {
                // Move is like Store but maybe with different semantics?
                // If it's the same as Store:
                let val = self.val(from);
                let addr_val = self.val(to);
                let Value::RawPtr(ptr) = addr_val else {
                    panic!("Move expects RawPtr destination, got {addr_val:?}");
                };

                let bytes = self.value_to_bytes(&ty, val);
                if bytes.len() != ty.bytes_len() {
                    panic!(
                        "Move size mismatch: expected {} bytes, got {}",
                        ty.bytes_len(),
                        bytes.len()
                    );
                }
                let heap_idx = ptr.0 - self.heap_start;

                for (i, byte) in bytes.iter().enumerate() {
                    self.memory.mem[heap_idx + i] = *byte;
                }
            }
            IR::Instr(Instruction::Gep {
                dest,
                ty,
                addr,
                offset_index,
            }) => {
                let Value::RawPtr(ptr) = self.val(addr) else {
                    panic!("Addr must be pointer")
                };

                let Value::Int(offset) = self.val(offset_index) else {
                    panic!("offset_index must be int")
                };

                let offset = ty.bytes_len() * offset as usize;
                let new_ptr = Value::RawPtr(Addr(ptr.0 + offset));
                self.write_register(&dest, new_ptr);
            }
            IR::Instr(Instruction::Free { .. }) => unimplemented!(),
            // I/O Instructions
            IR::Instr(Instruction::IoOpen {
                dest,
                path,
                flags,
                mode,
            }) => {
                let path_val = self.val(path);
                let flags_val = self.val(flags);
                let mode_val = self.val(mode);

                let path_bytes = self.get_bytes_from_value(path_val);
                let Value::Int(flags_int) = flags_val else {
                    panic!("IoOpen flags must be Int, got {flags_val:?}");
                };
                let Value::Int(mode_int) = mode_val else {
                    panic!("IoOpen mode must be Int, got {mode_val:?}");
                };

                let result = self.io.io_open(&path_bytes, flags_int, mode_int);
                self.write_register(&dest, Value::Int(result));
            }
            IR::Instr(Instruction::IoRead {
                dest,
                fd,
                buf,
                count,
            }) => {
                let fd_val = self.val(fd);
                let buf_val = self.val(buf);
                let count_val = self.val(count);

                let Value::Int(fd_int) = fd_val else {
                    panic!("IoRead fd must be Int, got {fd_val:?}");
                };
                let Value::RawPtr(buf_ptr) = buf_val else {
                    panic!("IoRead buf must be RawPtr, got {buf_val:?}");
                };
                let Value::Int(count_int) = count_val else {
                    panic!("IoRead count must be Int, got {count_val:?}");
                };

                // Read into a temporary buffer first
                let mut temp_buf = vec![0u8; count_int as usize];
                let result = self.io.io_read(fd_int, &mut temp_buf);

                // If read was successful, copy to memory
                if result > 0 {
                    let heap_idx = buf_ptr.0 - self.heap_start;
                    for (i, byte) in temp_buf.iter().take(result as usize).enumerate() {
                        self.memory.mem[heap_idx + i] = *byte;
                    }
                }

                self.write_register(&dest, Value::Int(result));
            }
            IR::Instr(Instruction::IoWrite {
                dest,
                fd,
                buf,
                count,
            }) => {
                let fd_val = self.val(fd);
                let buf_val = self.val(buf);
                let count_val = self.val(count);

                let Value::Int(fd_int) = fd_val else {
                    panic!("IoWrite fd must be Int, got {fd_val:?}");
                };
                let Value::RawPtr(buf_ptr) = buf_val else {
                    panic!("IoWrite buf must be RawPtr, got {buf_val:?}");
                };
                let Value::Int(count_int) = count_val else {
                    panic!("IoWrite count must be Int, got {count_val:?}");
                };

                // Get bytes from memory
                let bytes = if buf_ptr.0 < self.heap_start {
                    // Static memory
                    self.program.static_memory.data[buf_ptr.0..buf_ptr.0 + count_int as usize]
                        .to_vec()
                } else {
                    // Heap memory
                    let heap_idx = buf_ptr.0 - self.heap_start;
                    self.memory.mem[heap_idx..heap_idx + count_int as usize].to_vec()
                };

                let result = self.io.io_write(fd_int, &bytes);
                self.write_register(&dest, Value::Int(result));
            }
            IR::Instr(Instruction::IoClose { dest, fd }) => {
                let fd_val = self.val(fd);

                let Value::Int(fd_int) = fd_val else {
                    panic!("IoClose fd must be Int, got {fd_val:?}");
                };

                let result = self.io.io_close(fd_int);
                self.write_register(&dest, Value::Int(result));
            }
            IR::Instr(Instruction::IoCtl { dest, fd, op, arg }) => {
                let fd_val = self.val(fd);
                let op_val = self.val(op);
                let arg_val = self.val(arg);

                let Value::Int(fd_int) = fd_val else {
                    panic!("IoCtl fd must be Int, got {fd_val:?}");
                };
                let Value::Int(op_int) = op_val else {
                    panic!("IoCtl op must be Int, got {op_val:?}");
                };
                let Value::Int(arg_int) = arg_val else {
                    panic!("IoCtl arg must be Int, got {arg_val:?}");
                };

                let result = self.io.io_ctl(fd_int, op_int, arg_int);
                self.write_register(&dest, Value::Int(result));
            }
            IR::Instr(Instruction::IoPoll {
                dest,
                fds,
                count,
                timeout,
            }) => {
                let fds_val = self.val(fds);
                let count_val = self.val(count);
                let timeout_val = self.val(timeout);

                let Value::RawPtr(fds_ptr) = fds_val else {
                    panic!("IoPoll fds must be RawPtr, got {fds_val:?}");
                };
                let Value::Int(count_int) = count_val else {
                    panic!("IoPoll count must be Int, got {count_val:?}");
                };
                let Value::Int(timeout_int) = timeout_val else {
                    panic!("IoPoll timeout must be Int, got {timeout_val:?}");
                };

                // Read pollfd structs from memory (each is 8 bytes: i32 fd, i16 events, i16 revents)
                let heap_idx = fds_ptr.0 - self.heap_start;
                let mut poll_fds: Vec<(i32, i16, i16)> = Vec::with_capacity(count_int as usize);

                for i in 0..count_int as usize {
                    let offset = heap_idx + i * 8;
                    let fd =
                        i32::from_le_bytes(self.memory.mem[offset..offset + 4].try_into().unwrap());
                    let events = i16::from_le_bytes(
                        self.memory.mem[offset + 4..offset + 6].try_into().unwrap(),
                    );
                    let revents = i16::from_le_bytes(
                        self.memory.mem[offset + 6..offset + 8].try_into().unwrap(),
                    );
                    poll_fds.push((fd, events, revents));
                }

                let result = self.io.io_poll(&mut poll_fds, timeout_int);

                // Write back revents
                for (i, (_, _, revents)) in poll_fds.iter().enumerate() {
                    let offset = heap_idx + i * 8 + 6;
                    let bytes = revents.to_le_bytes();
                    self.memory.mem[offset] = bytes[0];
                    self.memory.mem[offset + 1] = bytes[1];
                }

                self.write_register(&dest, Value::Int(result));
            }
            IR::Instr(Instruction::IoSleep { dest, ms }) => {
                let ms_val = self.val(ms);
                let Value::Int(ms_int) = ms_val else {
                    panic!("IoSleep ms must be Int, got {ms_val:?}");
                };
                let result = self.io.io_sleep(ms_int);
                self.write_register(&dest, Value::Int(result));
            }
        }
    }

    /// Helper to extract bytes from a value (for paths, etc.)
    fn get_bytes_from_value(&self, val: Value) -> Vec<u8> {
        match val {
            Value::RawPtr(ptr) => {
                // Read null-terminated string from memory
                let mut bytes = Vec::new();
                let mut addr = ptr.0;
                loop {
                    let byte = if addr < self.heap_start {
                        self.program.static_memory.data[addr]
                    } else {
                        self.memory.mem[addr - self.heap_start]
                    };
                    if byte == 0 {
                        break;
                    }
                    bytes.push(byte);
                    addr += 1;
                }
                bytes
            }
            Value::RawBuffer(bytes) => bytes,
            Value::Record(RecordId::Nominal(sym), fields) if sym == Symbol::String => {
                // String struct: (ptr, len)
                let Value::RawPtr(ptr) = &fields[0] else {
                    panic!("String.ptr must be RawPtr");
                };
                let Value::Int(len) = &fields[1] else {
                    panic!("String.len must be Int");
                };
                let len = *len as usize;
                if ptr.0 < self.heap_start {
                    self.program.static_memory.data[ptr.0..ptr.0 + len].to_vec()
                } else {
                    let heap_idx = ptr.0 - self.heap_start;
                    self.memory.mem[heap_idx..heap_idx + len].to_vec()
                }
            }
            other => panic!("Cannot get bytes from {other:?}"),
        }
    }

    fn value_to_bytes(&mut self, ty: &IrTy, value: Value) -> Vec<u8> {
        if matches!(value, Value::Uninit) {
            return vec![0; ty.bytes_len()];
        }

        match ty {
            IrTy::Int => match value {
                Value::Int(v) => v.to_le_bytes().to_vec(),
                other => panic!("expected int for {ty:?}, got {other:?}"),
            },
            IrTy::Float => match value {
                Value::Float(v) => v.to_le_bytes().to_vec(),
                other => panic!("expected float for {ty:?}, got {other:?}"),
            },
            IrTy::Bool => match value {
                Value::Bool(v) => vec![if v { 1 } else { 0 }],
                Value::Int(v) => vec![if v != 0 { 1 } else { 0 }],
                other => panic!("expected bool for {ty:?}, got {other:?}"),
            },
            IrTy::Func(..) => match value {
                Value::Func(sym) => sym.as_bytes().to_vec(),
                Value::Ref(Reference::Func(sym)) => sym.as_bytes().to_vec(),
                other => panic!("expected func for {ty:?}, got {other:?}"),
            },
            IrTy::Record(_sym, field_tys) => match value {
                Value::Record(_record_id, fields) => {
                    if fields.len() != field_tys.len() {
                        panic!(
                            "record field count mismatch: expected {}, got {}",
                            field_tys.len(),
                            fields.len()
                        );
                    }

                    let mut bytes = Vec::with_capacity(ty.bytes_len());
                    for (field_val, field_ty) in fields.into_iter().zip(field_tys.iter()) {
                        bytes.extend(self.value_to_bytes(field_ty, field_val));
                    }
                    bytes
                }
                other => panic!("expected record for {ty:?}, got {other:?}"),
            },
            IrTy::RawPtr => match value {
                Value::RawPtr(addr) => (addr.0 as u64).to_le_bytes().to_vec(),
                Value::Int(v) => (v as u64).to_le_bytes().to_vec(),
                other => panic!("expected rawptr for {ty:?}, got {other:?}"),
            },
            IrTy::Byte => match value {
                Value::RawBuffer(bytes) => {
                    if bytes.len() != 1 {
                        panic!("expected 1 byte, got {}", bytes.len());
                    }
                    bytes
                }
                Value::Int(v) => vec![v as u8],
                other => panic!("expected byte for {ty:?}, got {other:?}"),
            },
            IrTy::Buffer(len) => match value {
                Value::RawBuffer(bytes) => {
                    if bytes.len() != *len as usize {
                        panic!("expected buffer of length {}, got {}", len, bytes.len());
                    }
                    bytes
                }
                other => panic!("expected buffer for {ty:?}, got {other:?}"),
            },
            IrTy::Void => Vec::new(),
        }
    }

    fn bytes_to_value(&self, ty: &IrTy, bytes: &[u8]) -> Value {
        match ty {
            IrTy::Int => Value::Int(i64::from_le_bytes(bytes.try_into().unwrap())),
            IrTy::Float => Value::Float(f64::from_le_bytes(bytes.try_into().unwrap())),
            IrTy::Bool => Value::Bool(bytes[0] != 0),
            IrTy::RawPtr => {
                Value::RawPtr(Addr(u64::from_le_bytes(bytes.try_into().unwrap()) as usize))
            }
            IrTy::Func(..) => Value::Func(Symbol::from_bytes(bytes.try_into().unwrap())),
            IrTy::Byte | IrTy::Buffer(..) => Value::RawBuffer(bytes.to_vec()),
            IrTy::Record(sym, field_tys) => {
                let mut offset = 0;
                let mut fields = Vec::with_capacity(field_tys.len());
                for field_ty in field_tys {
                    let field_len = field_ty.bytes_len();
                    let field_bytes = &bytes[offset..offset + field_len];
                    fields.push(self.bytes_to_value(field_ty, field_bytes));
                    offset += field_len;
                }

                let record_id = match sym {
                    Some(sym) => RecordId::Nominal(*sym),
                    None => RecordId::Anon,
                };
                Value::Record(record_id, fields)
            }
            IrTy::Void => panic!("Load not implemented for {ty:?}"),
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

    pub fn display(&self, val: Value, quoted: bool) -> String {
        match val {
            Value::Int(val) => format!("{val}"),
            Value::Reg(reg) => format!("%{reg}"),
            Value::Capture { .. } => format!("{val}"),
            Value::Poison => "<POISON>".to_string(),
            Value::Float(val) => format!("{val}"),
            Value::Bool(val) => format!("{val}"),
            Value::Record(record_id, values) => {
                if record_id == RecordId::Nominal(Symbol::String) {
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

                    return if quoted {
                        format!("\"{s}\"")
                    } else {
                        s.to_string()
                    };
                }

                if record_id == RecordId::Nominal(Symbol::Array) {
                    return "Array(..) // formatting arrays is tricky for now. Need to add proper Show protocol.".to_string();
                }

                if let RecordId::Nominal(sym) = record_id {
                    if matches!(sym, Symbol::Enum(..))
                        && let Some(labels) = self.program.record_labels.get(&record_id)
                        && let Some(formatted) = self.format_enum_variant(sym, labels, &values)
                    {
                        return formatted;
                    }

                    if let Some(labels) = self.program.record_labels.get(&record_id)
                        && let Some(fields) = self.format_labeled_fields(labels, &values)
                    {
                        let name = self.sym_to_str(&sym);
                        return self.wrap_record(Some(&name), &fields);
                    }
                } else if let Some(labels) = self.program.record_labels.get(&record_id)
                    && let Some(fields) = self.format_labeled_fields(labels, &values)
                {
                    return self.wrap_record(None, &fields);
                }

                let values = values
                    .into_iter()
                    .map(|v| self.display(v, quoted))
                    .collect_vec();
                let name = if let RecordId::Nominal(sym) = record_id {
                    self.sym_to_str(&sym)
                } else {
                    "".to_string()
                };

                format!("{name:?}({values:?})")
            }
            Value::Func(symbol) => format!("func {}()", self.sym_to_str(&symbol)),
            Value::Closure { func, env } => format!("func {}[{env}]()", self.sym_to_str(&func)),
            Value::Void => "()".into(),
            Value::RawPtr(val) => format!("rawptr({})", val.0),
            Value::Ref(reference) => match reference {
                Reference::Func(sym) => format!("func {}()", self.sym_to_str(&sym)),
                _ => format!("{reference:?}"),
            },
            Value::Uninit => "UNINIT".into(),
            Value::RawBuffer(bytes) => format!("buf({bytes:?})"),
        }
    }

    fn format_labeled_fields(&self, labels: &[String], values: &[Value]) -> Option<String> {
        if labels.len() != values.len() {
            return None;
        }

        let fields = labels
            .iter()
            .zip(values.iter())
            .map(|(label, value)| format!("{label}: {}", self.display(value.clone(), true)))
            .collect_vec();
        Some(fields.join(", "))
    }

    fn wrap_record(&self, name: Option<&str>, fields: &str) -> String {
        if fields.is_empty() {
            return match name {
                Some(name) => format!("{name} {{}}"),
                None => "{}".to_string(),
            };
        }

        match name {
            Some(name) => format!("{name} {{ {fields} }}"),
            None => format!("{{ {fields} }}"),
        }
    }

    fn format_enum_variant(
        &self,
        sym: Symbol,
        labels: &[String],
        values: &[Value],
    ) -> Option<String> {
        let tag = match values.first()? {
            Value::Int(tag) => *tag,
            _ => return None,
        };
        let idx = usize::try_from(tag).ok()?;
        let variant = labels.get(idx)?;
        let args = values
            .iter()
            .skip(1)
            .map(|value| self.display(value.clone(), true))
            .collect_vec();
        let name = self.sym_to_str(&sym);

        if args.is_empty() {
            Some(format!("{name}.{variant}"))
        } else {
            Some(format!("{name}.{variant}({})", args.join(", ")))
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

        if register == &Register::DROP {
            // Discard the value
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

    fn func(&self, val: Value) -> (Symbol, List<Value>) {
        match val {
            Value::Reg(reg) => match self.read_register(&Register(reg)) {
                Value::Func(symbol) => (symbol, Default::default()),
                Value::Closure { func, env } => (func, env),
                Value::Ref(Reference::Func(sym)) => (sym, Default::default()),
                Value::Ref(Reference::Closure(sym, env)) => (sym, env),
                _ => panic!(
                    "didn't get func symbol from {val:?}: {:?}",
                    self.read_register(&Register(reg))
                ),
            },
            Value::Func(name) => (name, Default::default()),
            Value::Ref(Reference::Func(sym)) => (sym, Default::default()),
            Value::Ref(Reference::Closure(sym, env)) => (sym, env),
            Value::Closure { func, env } => (func, env),
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
    use crate::ir::{io::CaptureIO, lowerer_tests::tests::lower_module};

    use super::*;

    pub fn interpret_with(input: &str) -> (Value, Interpreter<CaptureIO>) {
        let (module, display_names) = lower_module(input);
        let mut interpreter =
            Interpreter::new(module.program, Some(display_names), CaptureIO::default());

        (interpreter.run(), interpreter)
    }

    pub fn interpret(input: &str) -> Value {
        let (module, display_names) = lower_module(input);
        let mut interpreter =
            Interpreter::new(module.program, Some(display_names), CaptureIO::default());

        interpreter.run()
    }

    #[test]
    pub fn empty_is_void() {
        assert_eq!(interpret(""), Value::Void);
    }

    #[test]
    pub fn prints() {
        let (_, interpreter) = interpret_with(
            "
        print(\"sup\")
        ",
        );
        assert_eq!("sup\n".as_bytes(), interpreter.io.stdout);
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
    pub fn add_int() {
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
        let (value, interpreter) = interpret_with("let a = \"hello \" + \"world\"; a");
        let val = interpreter.display(value, false);
        assert_eq!(val, format!("hello world"));
    }

    #[test]
    fn interprets_greet_regression() {
        let (value, interpreter) = interpret_with(
            "
            struct Person {
                let name: String

                func greet(name) {
                    \"hey, i'm \" + self.name
                }
            }

            Person(name: \"pat\").greet()
            ",
        );

        assert_eq!(interpreter.display(value, false), "hey, i'm pat");
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
    fn interprets_mut_closure() {
        assert_eq!(
            interpret(
                "
            let a = 123
            func b() { a = a + 1; a }
            b()
            a
            "
            ),
            Value::Int(124)
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

    #[test]
    fn interprets_counter() {
        assert_eq!(
            interpret(
                "
            func makeCounter() {
                let a = 0
                return func() {
                    a = a + 1
                    a
                }
            }

            let a = makeCounter()
            let b = makeCounter()
            a() ; a()
            (a(), b())
            "
            ),
            Value::Record(RecordId::Anon, vec![Value::Int(3), Value::Int(1)])
        )
    }

    #[test]
    fn interprets_array_literal_properties() {
        assert_eq!(
            interpret(
                "
            [10,20,30].count
            "
            ),
            Value::Int(3)
        )
    }

    #[test]
    fn interprets_array_get() {
        assert_eq!(
            interpret(
                "
            [10,20,30,40].get(1)
            "
            ),
            Value::Int(20)
        )
    }

    #[test]
    fn interprets_simple_match() {
        let (val, interpreter) = interpret_with(
            "
        enum Response {
                case ok(String), redirect(String), other(Int)
            }

            match Response.ok(\"It's cool\") {
                .ok(data) -> data,
                .redirect(location) -> \"redirect \" + location,
                .other(_) -> \"other\"
            }
        ",
        );

        assert_eq!("It's cool", interpreter.display(val, false));
    }

    #[test]
    fn interprets_unqualified_variant_arg() {
        let val = interpret(
            "
            enum AB {
                case a(Int), b(Int)
            }

            func callMe(param: AB) {
                match param {
                    .a(x) -> x,
                    .b(x) -> x,
                }
            }

            callMe(.a(123))
        ",
        );

        assert_eq!(val, Value::Int(123));
    }

    #[test]
    fn interprets_or_pattern_in_let() {
        let result = interpret(
            "
          enum Wrapper {
              case box(Int)
              case bag(Int)
          }

          let .box(x) | .bag(x) = Wrapper.bag(123)
          x
          ",
        );

        assert_eq!(result, Value::Int(123));
    }

    #[test]
    fn interprets_or_pattern_falls_through_to_next_arm() {
        let result = interpret(
            "
          enum ABC {
              case a
              case b
              case c
          }

          func toInt(x: ABC) -> Int {
              match x {
                  .a | .b -> 1,
                  .c -> 2
              }
          }

          toInt(.c)
          ",
        );

        assert_eq!(result, Value::Int(2));
    }

    #[test]
    fn formats_record() {
        let (value, interpreter) = interpret_with(
            "
            { fizz: 123, buzz: true }
            ",
        );

        assert_eq!(
            "{ fizz: 123, buzz: true }",
            &interpreter.display(value, false)
        )
    }

    #[test]
    fn formats_struct_instance() {
        let (value, interpreter) = interpret_with(
            "
            struct Person {
                let fizz: Int
                let buzz: Bool
            }

            Person(fizz: 123, buzz: true)
            ",
        );

        assert_eq!(
            "Person { fizz: 123, buzz: true }",
            &interpreter.display(value, false)
        )
    }

    #[test]
    fn formats_enum_variant() {
        let (value, interpreter) = interpret_with(
            "
            enum Foo {
                case fizz(Int), buzz(Bool)
            }

            Foo.fizz(123)
            ",
        );

        assert_eq!("Foo.fizz(123)", &interpreter.display(value, false))
    }

    #[test]
    #[ignore = "formatting arrays is tricky, need to introduce a proper Show protocol"]
    fn formats_array() {
        let (value, interpreter) = interpret_with(
            "
            [1,2,3]
            ",
        );

        assert_eq!("[1, 2, 3]", &interpreter.display(value, false))
    }

    #[test]
    fn interprets_protocol_example() {
        let (_, interpreter) = interpret_with(
            "
// Ok so we've got some different pet foods here
struct CatFood {}
struct DogFood {}

// And we've got a protocol `Named` that just knows how
// to get names of things.
protocol Named {
    func name() -> String
}

// Let's make the pet foods conform to Named
extend CatFood: Named {
    func name() { \"tasty cat food\" }
}

extend DogFood: Named {
    func name() { \"tasty dog food\" }
}

// So far so good, right? Ok now let's add a Pet protocol.

protocol Pet {
    // Pets eat different foods, who knew??
    associated Food: Named

    func favoriteFood() -> Food

    // See what the pet does when daylight saves time changes
    func handleDSTChange() {
        print(\"what the heck where is my \" + self.favoriteFood().name())
    }
 }

struct Cat {}
extend Cat: Pet {
    func favoriteFood() {
        CatFood()
    }
}

struct Dog {}
extend Dog: Pet {
    func favoriteFood() {
        DogFood()
    }
}

Cat().handleDSTChange()
Dog().handleDSTChange()
        ",
        );

        assert_eq!(
            "what the heck where is my tasty cat food\nwhat the heck where is my tasty dog food\n",
            String::from_utf8(interpreter.io.stdout).unwrap()
        );
    }

    #[test]
    fn interprets_effect_call() {
        let (_val, interpreter) = interpret_with(
            "
            effect 'fizz(x: Int) -> Int

            @handle 'fizz { x in
                continue x
            }

            func fizzes(x) '[fizz] {
                'fizz(x)
            }

            print(fizzes(123))",
        );

        assert_eq!(interpreter.io.stdout, "123\n".as_bytes());
    }

    #[test]
    fn interprets_throw_with_effect_handler() {
        let (val, interpreter) = interpret_with(
            "
          effect 'throw(msg: String) -> Never

          @handle 'throw { msg in
              print(\"caught: \" + msg)
              99
          }

          func boom(x) '[throw] {
              if x == 0 {
                  'throw(\"boom\")
              }
              print(\"after\") // should not run
              x + 1
          }

          boom(0)
          ",
        );

        assert_eq!(val, Value::Int(99));
        assert_eq!(
            String::from_utf8(interpreter.io.stdout).unwrap(),
            "caught: boom\n"
        );
    }

    #[test]
    fn interprets_nested_extend_method() {
        // Minimal test for nested extend methods
        let (_val, interpreter) = interpret_with(
            "
            protocol Greeter {
                func greet() -> Int
            }

            struct MyStruct {
                let value: Int

                extend Self: Greeter {
                    func greet() -> Int {
                        self.value + 100
                    }
                }
            }

            let s = MyStruct(value: 42)
            print(s.greet())
            ",
        );

        assert_eq!(interpreter.io.stdout, "142\n".as_bytes());
    }

    #[test]
    fn interprets_nested_extend_method_with_generic() {
        // Test nested extend with generics (similar to Iterator pattern)
        let (_val, interpreter) = interpret_with(
            "
            protocol Getter<T> {
                func get() -> T
            }

            struct Container<Element> {
                let item: Element

                extend Self: Getter<Element> {
                    func get() -> Element {
                        self.item
                    }
                }
            }

            let c = Container<Int>(item: 42)
            print(c.get())
            ",
        );

        assert_eq!(interpreter.io.stdout, "42\n".as_bytes());
    }

    #[test]
    fn interprets_nested_extend_method_with_array() {
        // Test nested extend that uses arrays (like ArrayIterator)
        let (_val, interpreter) = interpret_with(
            "
            protocol Accessor<T> {
                func first() -> T
            }

            struct ArrayWrapper<Element> {
                let arr: Array<Element>

                extend Self: Accessor<Element> {
                    func first() -> Element {
                        self.arr.get(0)
                    }
                }
            }

            let w = ArrayWrapper<Int>(arr: [1, 2, 3])
            print(w.first())
            ",
        );

        assert_eq!(interpreter.io.stdout, "1\n".as_bytes());
    }

    #[test]
    fn interprets_array_iter_method() {
        // Test just calling iter() to create an iterator
        let (_val, interpreter) = interpret_with(
            "
            let a = [1,2,3]
            let i = a.iter()
            print(\"created iterator\")
            ",
        );

        assert_eq!(interpreter.io.stdout, "created iterator\n".as_bytes());
    }

    #[test]
    fn interprets_nested_extend_method_with_self_access() {
        // Test nested extend method that accesses self fields
        let (_val, interpreter) = interpret_with(
            "
            protocol Doubler {
                func doubled() -> Int
            }

            struct Wrapper {
                let value: Int

                extend Self: Doubler {
                    func doubled() -> Int {
                        self.value + self.value
                    }
                }
            }

            let w = Wrapper(value: 21)
            print(w.doubled())
            ",
        );

        assert_eq!(interpreter.io.stdout, "42\n".as_bytes());
    }

    #[test]
    fn interprets_iterator_simple() {
        // First test: just call next() once
        // next() returns Optional<Element>, so the output includes the enum wrapper
        let (_val, interpreter) = interpret_with(
            "
            let a = [1,2,3]
            let i = a.iter()
            let result = i.next()
            print(result)
            ",
        );

        assert_eq!(interpreter.io.stdout, "Optional.some(1)\n".as_bytes());
    }

    #[test]
    fn interprets_iterator() {
        // next() returns Optional<Element>, so the output includes the enum wrapper
        let (_val, interpreter) = interpret_with(
            "
            let a = [1,2,3]
            let i = a.iter()
            print(i.next())
            print(i.next())
            print(i.next())
            ",
        );

        assert_eq!(
            interpreter.io.stdout,
            "Optional.some(1)\nOptional.some(2)\nOptional.some(3)\n".as_bytes()
        );
    }

    #[test]
    fn interprets_io_open_and_close() {
        // Test io_open and io_close via inline IR
        let (val, _interpreter) = interpret_with(
            "
            func test_io_open(path: RawPtr, flags: Int, mode: Int) -> Int {
                @_ir(path, flags, mode) { %? = io_open $0 $1 $2 }
            }

            func test_io_close(fd: Int) -> Int {
                @_ir(fd) { %? = io_close $0 }
            }

            // Open returns a simulated fd >= 3
            let fd = test_io_open(\"test.txt\".base, 0, 0)
            // Close should succeed (return 0)
            let result = test_io_close(fd)
            result
            ",
        );

        // CaptureIO.io_close returns 0 on success
        assert_eq!(val, Value::Int(0));
    }

    #[test]
    fn interprets_io_close_invalid_fd() {
        let (val, _interpreter) = interpret_with(
            "
            func test_io_close(fd: Int) -> Int {
                @_ir(fd) { %? = io_close $0 }
            }

            // Closing an invalid fd should return EBADF (-9)
            test_io_close(999)
            ",
        );

        // Should return -9 (EBADF) for invalid fd
        assert_eq!(val, Value::Int(-9));
    }

    #[test]
    fn interprets_io_sleep() {
        let (val, _interpreter) = interpret_with(
            "
            func test_io_sleep(ms: Int) -> Int {
                @_ir(ms) { %? = io_sleep $0 }
            }

            test_io_sleep(0)
            ",
        );

        // CaptureIO.io_sleep returns 0 (no-op for testing)
        assert_eq!(val, Value::Int(0));
    }

    #[test]
    fn interprets_optional_match() {
        // Test that match on custom Optional-like enum works
        let (_val, interpreter) = interpret_with(
            "
            enum MyOptional<T> { case some(T), none }

            let opt = MyOptional.some(42)
            match opt {
                .some(x) -> print(x),
                .none -> print(0)
            }
            ",
        );
        assert_eq!(interpreter.io.stdout, "42\n".as_bytes());
    }

    #[test]
    fn interprets_simple_loop_break() {
        // Test basic loop with break
        let (_val, interpreter) = interpret_with(
            "
            let i = 0
            loop {
                if i >= 3 {
                    break
                }
                print(i)
                i = i + 1
            }
            ",
        );
        assert_eq!(interpreter.io.stdout, "0\n1\n2\n".as_bytes());
    }

    #[test]
    fn interprets_match_with_conditional_and_break() {
        // Test match on conditionally created enum with break in arm
        let (_val, interpreter) = interpret_with(
            "
            enum Opt { case yes(Int), no }
            let i = 0
            loop {
                let opt = if i < 3 { Opt.yes(i) } else { Opt.no }
                match opt {
                    .yes(x) -> {
                        print(x)
                        i = i + 1
                        ()
                    },
                    .no -> break
                }
            }
            ",
        );
        assert_eq!(interpreter.io.stdout, "0\n1\n2\n".as_bytes());
    }

    #[test]
    fn interprets_core_optional_match() {
        // Test that matching on Optional from Core (imported enum) gets correct variant tags.
        // The bug was that when enum variants from imported modules are cached in order of
        // use rather than declaration order, the tag indices become wrong.
        // We use the iterator pattern which returns Optional<Element>.
        let (_val, interpreter) = interpret_with(
            "
            let a = [42]
            let i = a.iter()
            let opt = i.next()
            match opt {
                .some(x) -> print(x),
                .none -> print(0)
            }
            ",
        );
        assert_eq!(interpreter.io.stdout, "42\n".as_bytes());
    }
}
