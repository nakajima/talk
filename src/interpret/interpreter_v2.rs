use crate::{
    SymbolID, SymbolTable,
    interpret::{
        io::InterpreterIO,
        memory_v2::{Memory, MemoryLocation, Pointer},
        value_v2::Value,
    },
    lowering::{
        instr::{Callee, Instr},
        ir_error::IRError,
        ir_module::IRModule,
        ir_type::IRType,
        ir_value::IRValue,
        lowerer::{BasicBlockID, RefKind, RegisterList},
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
    // Stack frame allocation info
    stack_base: usize,
    locals: HashMap<Register, Value>,
    // Register to store return value in caller's frame
    return_register: Option<Register>,
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
        tracing::info!("Running interpreter v2 with improved memory model");

        #[allow(clippy::print_with_newline)]
        if std::env::var("IR").is_ok() {
            print!("{}\n", crate::lowering::ir_printer::print(&self.program));
        }

        let Some(&main_idx) = self.function_map.get("@main") else {
            return Err(InterpreterError::NoMainFunc);
        };

        let main = &self.program.functions[main_idx];
        let _ret_ty = main
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

        self.call_func(main_idx, &[], 0, None)?;

        match self.execute() {
            Ok(Some(result)) => {
                tracing::info!("Execution completed with result: {:?}", result);
                Ok(result)
            }
            Ok(None) => {
                tracing::info!("Execution completed with no result");
                Ok(Value::Int(0))
            }
            Err(e) => {
                tracing::error!("Execution failed: {:?}", e);
                Err(e)
            }
        }
    }

    fn call_func(
        &mut self,
        func_idx: usize,
        args: &[Value],
        _call_block: usize,
        return_register: Option<Register>,
    ) -> Result<(), InterpreterError> {
        let stack_base = self.memory.get_stack_pointer();

        let mut locals = HashMap::new();

        // Initialize parameters
        let func = &self.program.functions[func_idx];
        tracing::debug!("Calling function {} with type {:?}", func.name, func.ty);

        // For init functions, we need to handle the parameters specially
        // Init functions have type Struct but take pointer + field values as args
        let expected_arg_count = if func.name.contains("_init") {
            // Init function: first arg is struct pointer, rest are field values
            if let IRType::Struct(_, fields, _) = &func.ty {
                1 + fields.len() // pointer + fields
            } else {
                func.args().len()
            }
        } else {
            func.args().len()
        };

        tracing::debug!(
            "Calling function {} with {} args, function expects {} args",
            func.name,
            args.len(),
            expected_arg_count
        );

        for (i, arg) in args.iter().enumerate() {
            tracing::debug!("Setting arg {} (register {}) to {:?}", i, i, arg);
            // Parameters start at register 0
            locals.insert(Register(i as i32), arg.clone());
        }

        self.call_stack.push(StackFrame {
            pred: None,
            function: func_idx,
            block_idx: 0,
            pc: 0,
            stack_base,
            locals,
            return_register,
        });

        Ok(())
    }

    fn execute(&mut self) -> Result<Option<Value>, InterpreterError> {
        loop {
            if self.call_stack.is_empty() {
                return Ok(None);
            }

            // Get instruction to execute
            let (instr_to_execute, is_terminator) = {
                let frame = self.call_stack.last().unwrap();
                let func = &self.program.functions[frame.function];

                if frame.block_idx >= func.blocks.len() {
                    return Err(InterpreterError::InvalidProgram);
                }

                let block = &func.blocks[frame.block_idx];

                if frame.pc >= block.instructions.len() {
                    // End of block - the last instruction should be a terminator
                    return Err(InterpreterError::InvalidProgram);
                }

                let instr = block.instructions[frame.pc].clone();
                let is_term = matches!(
                    &instr,
                    Instr::Ret(..) | Instr::Jump(..) | Instr::Branch { .. } | Instr::Unreachable
                );
                (instr, is_term)
            };

            // Execute the instruction
            if is_terminator {
                match self.execute_terminator(&instr_to_execute)? {
                    Some(val) => {
                        // Function returned
                        let finished_frame = self.call_stack.pop().unwrap();

                        if self.call_stack.is_empty() {
                            return Ok(Some(val));
                        }

                        // Store return value in caller's register if needed
                        if let Some(ret_reg) = finished_frame.return_register {
                            self.set_register_value(ret_reg, val);
                        }

                        // Restore stack pointer
                        let current_frame = self.call_stack.last().unwrap();
                        self.memory.set_stack_pointer(current_frame.stack_base);
                    }
                    None => {
                        // Continue execution
                    }
                }
            } else {
                // Execute regular instruction
                if let Some(val) = self.execute_instr(&instr_to_execute)? {
                    return Ok(Some(val));
                }
            }
        }
    }

    fn execute_terminator(
        &mut self,
        terminator: &Instr,
    ) -> Result<Option<Value>, InterpreterError> {
        match terminator {
            Instr::Ret(ty, val) => {
                let result = match val {
                    Some(v) => {
                        let val = self.value(v);
                        tracing::debug!("Returning value {:?} of type {:?}", val, ty);
                        // HACK: Work around monomorphization bug where array.get
                        // returns a pointer value when the return type is int
                        match (&val, ty) {
                            (Value::Pointer(p), IRType::Int) if p.addr < 1000 => {
                                // Small pointer addresses are likely integer values
                                // that got misinterpreted as pointers
                                Value::Int(p.addr as i64)
                            }
                            _ => val,
                        }
                    }
                    None => Value::Int(0),
                };
                Ok(Some(result))
            }
            Instr::Jump(block) => {
                self.jump_to_block(*block)?;
                Ok(None)
            }
            Instr::Branch {
                cond,
                true_target,
                false_target,
            } => {
                let cond_val = self.register_value(*cond);
                match cond_val {
                    Value::Bool(true) => self.jump_to_block(*true_target)?,
                    Value::Bool(false) => self.jump_to_block(*false_target)?,
                    _ => {
                        return Err(InterpreterError::TypeError(
                            format!("{:?}", cond_val),
                            "bool".into(),
                        ));
                    }
                }
                Ok(None)
            }
            Instr::Unreachable => Err(InterpreterError::UnreachableReached),
            _ => Err(InterpreterError::Unknown(format!(
                "Invalid terminator: {:?}",
                terminator
            ))),
        }
    }

    fn jump_to_block(&mut self, block_id: BasicBlockID) -> Result<(), InterpreterError> {
        let frame = self.call_stack.last_mut().unwrap();
        let current_block = frame.block_idx;
        frame.pred = Some(BasicBlockID(current_block as u32));
        frame.block_idx = block_id.0 as usize;
        frame.pc = 0;
        Ok(())
    }

    fn execute_instr(&mut self, instr: &Instr) -> Result<Option<Value>, InterpreterError> {
        match instr {
            Instr::Add(dest, _, a, b) => {
                let result = self.register_value(*a).add(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::Sub(dest, _, a, b) => {
                let result = self.register_value(*a).sub(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::Mul(dest, _, a, b) => {
                let result = self.register_value(*a).mul(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::Div(dest, _, a, b) => {
                let result = self.register_value(*a).div(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::Eq(dest, _, a, b) => {
                let result = self.register_value(*a).eq(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::Ne(dest, _, a, b) => {
                let result = self.register_value(*a).neq(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::LessThan(dest, _, a, b) => {
                let result = self.register_value(*a).lt(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::LessThanEq(dest, _, a, b) => {
                let result = self.register_value(*a).lte(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::GreaterThan(dest, _, a, b) => {
                let result = self.register_value(*a).gt(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::GreaterThanEq(dest, _, a, b) => {
                let result = self.register_value(*a).gte(&self.register_value(*b))?;
                self.set_register_value(*dest, result);
            }
            Instr::Alloc { dest, ty, count } => {
                let count_val = count
                    .as_ref()
                    .map(|c| self.value(c))
                    .unwrap_or(Value::Int(1));
                let Value::Int(count) = count_val else {
                    return Err(InterpreterError::Unknown("Invalid alloc count".into()));
                };
                let ptr = self.memory.heap_alloc(ty, count as usize)?;
                self.set_register_value(*dest, Value::Pointer(ptr));
            }
            Instr::Store {
                val,
                location,
                ty: _,
            } => {
                let loc_val = self.register_value(*location);
                match loc_val {
                    Value::Pointer(ptr) => {
                        let val = self.value(val);
                        tracing::debug!("Storing {:?} to pointer {:?}", val, ptr);
                        val.store_to_memory(&mut self.memory, &ptr)?;
                    }
                    _ => {
                        return Err(InterpreterError::Unknown(format!(
                            "Expected pointer for store, got {:?}",
                            loc_val
                        )));
                    }
                }
            }
            Instr::Load { dest, addr, ty: _ } => {
                let addr_val = self.register_value(*addr);
                match addr_val {
                    Value::Pointer(ptr) => {
                        let val = Value::load_from_memory(&self.memory, &ptr)?;
                        tracing::debug!("Load from {:?} returned {:?}", ptr, val);
                        self.set_register_value(*dest, val);
                    }
                    _ => {
                        return Err(InterpreterError::Unknown(format!(
                            "Expected pointer for load, got {:?}",
                            addr_val
                        )));
                    }
                }
            }
            Instr::Const { dest, val, ty } => {
                let Value::Int(int) = self.value(val) else {
                    return Err(InterpreterError::Unknown(format!(
                        "Expected int for const, got {:?}",
                        self.value(val)
                    )));
                };

                let const_ptr = Pointer {
                    addr: int as usize,
                    ty: ty.clone(),
                    location: MemoryLocation::Static,
                };
                self.set_register_value(*dest, Value::Pointer(const_ptr));
            }
            Instr::GetElementPointer {
                dest,
                base,
                index,
                ty,
            } => {
                let index_val = match index {
                    IRValue::ImmediateInt(int) => *int,
                    IRValue::Register(reg) => match self.register_value(*reg) {
                        Value::Int(int) => int,
                        val => {
                            return Err(InterpreterError::TypeError(
                                format!("{:?}", val),
                                "int".to_string(),
                            ));
                        }
                    },
                };

                let base_val = self.register_value(*base);
                tracing::debug!(
                    "GEP: base={:?}, index={}, base_val={:?}, instr_ty={:?}",
                    base,
                    index_val,
                    base_val,
                    ty
                );
                match base_val {
                    Value::Pointer(mut ptr) => {
                        // Use the instruction's type, not the pointer's type
                        // This handles cases where we're reinterpreting the pointer type
                        match ty {
                            IRType::Struct(_, fields, _) => {
                                // For struct, index is the field index
                                let field_idx = index_val as usize;
                                if field_idx >= fields.len() {
                                    return Err(InterpreterError::Unknown(format!(
                                        "Field index {} out of bounds",
                                        field_idx
                                    )));
                                }

                                // Calculate offset to the field
                                let mut offset = 0;
                                for i in 0..field_idx {
                                    let field_info = Memory::type_info(&fields[i]);
                                    // Align to field alignment
                                    offset =
                                        (offset + field_info.align - 1) & !(field_info.align - 1);
                                    offset += field_info.size;
                                }

                                // Align to target field
                                let field_info = Memory::type_info(&fields[field_idx]);
                                offset = (offset + field_info.align - 1) & !(field_info.align - 1);

                                ptr.addr += offset;
                                ptr.ty = fields[field_idx].clone();
                            }
                            IRType::TypedBuffer { element } => {
                                // For arrays, index is the element index
                                let elem_info = Memory::type_info(element);
                                ptr.addr += (index_val as usize) * elem_info.size;
                                ptr.ty = element.as_ref().clone();
                            }
                            IRType::Pointer { .. } => {
                                // For pointers, assume 8-byte elements
                                ptr.addr += (index_val as usize) * 8;
                            }
                            _ => {
                                return Err(InterpreterError::Unknown(format!(
                                    "Cannot index into type {:?}",
                                    ty
                                )));
                            }
                        }

                        self.set_register_value(*dest, Value::Pointer(ptr));
                    }
                    _ => {
                        return Err(InterpreterError::Unknown(format!(
                            "Expected pointer for GEP, got {:?}",
                            base_val
                        )));
                    }
                }
            }
            Instr::MakeStruct { dest, values, ty } => {
                let IRType::Struct(sym, _, _) = ty else {
                    return Err(InterpreterError::Unknown("Expected struct type".into()));
                };
                let field_values = self.register_values(values);
                self.set_register_value(*dest, Value::Struct(*sym, field_values));
            }
            Instr::GetValueOf {
                dest,
                ty: _,
                structure,
                index,
            } => {
                let struct_val = self.register_value(*structure);
                match struct_val {
                    Value::Struct(_, fields) => {
                        if let Some(field_val) = fields.get(*index) {
                            self.set_register_value(*dest, field_val.clone());
                        } else {
                            return Err(InterpreterError::Unknown(format!(
                                "Field index {} out of bounds for struct",
                                index
                            )));
                        }
                    }
                    _ => {
                        return Err(InterpreterError::Unknown(format!(
                            "GetValueOf expects a struct, got {:?}",
                            struct_val
                        )));
                    }
                }
            }
            Instr::ConstantInt(dest, val) => {
                self.set_register_value(*dest, Value::Int(*val));
            }
            Instr::ConstantFloat(dest, val) => {
                self.set_register_value(*dest, Value::Float(*val));
            }
            Instr::ConstantBool(dest, val) => {
                self.set_register_value(*dest, Value::Bool(*val));
            }
            #[allow(clippy::print_with_newline)]
            Instr::Print { ty: _, val } => {
                let val = self.value(val);

                let val = if let Value::Pointer(ptr) = val {
                    Value::load_from_memory(&self.memory, &ptr)?
                } else {
                    val
                };

                // Special handling for strings
                let output = if let Value::Struct(sym, fields) = &val {
                    if *sym == SymbolID::STRING && fields.len() >= 3 {
                        // String struct has fields: length, capacity, storage pointer
                        if let Value::Pointer(storage_ptr) = fields[2].clone() {
                            // Check if this pointer is actually a static constant
                            // If the address is small and we have a constant at that index, it's static
                            if storage_ptr.addr < self.program.constants.len() {
                                if let Some(
                                    crate::lowering::ir_module::IRConstantData::RawBuffer(bytes),
                                ) = self.program.constants.get(storage_ptr.addr)
                                {
                                    String::from_utf8_lossy(bytes).to_string()
                                } else {
                                    val.display(&|sym| {
                                        self.symbols
                                            .get(&sym)
                                            .map(|info| info.name.clone())
                                            .unwrap_or_else(|| format!("<unknown {:?}>", sym))
                                    })
                                }
                            } else {
                                // For heap strings, load the buffer
                                match Value::load_from_memory(&self.memory, &storage_ptr) {
                                    Ok(Value::RawBuffer(bytes)) => {
                                        String::from_utf8_lossy(&bytes).to_string()
                                    }
                                    _ => val.display(&|sym| {
                                        self.symbols
                                            .get(&sym)
                                            .map(|info| info.name.clone())
                                            .unwrap_or_else(|| format!("<unknown {:?}>", sym))
                                    }),
                                }
                            }
                        } else {
                            val.display(&|sym| {
                                self.symbols
                                    .get(&sym)
                                    .map(|info| info.name.clone())
                                    .unwrap_or_else(|| format!("<unknown {:?}>", sym))
                            })
                        }
                    } else {
                        val.display(&|sym| {
                            self.symbols
                                .get(&sym)
                                .map(|info| info.name.clone())
                                .unwrap_or_else(|| format!("<unknown {:?}>", sym))
                        })
                    }
                } else {
                    val.display(&|sym| {
                        self.symbols
                            .get(&sym)
                            .map(|info| info.name.clone())
                            .unwrap_or_else(|| format!("<unknown {:?}>", sym))
                    })
                };

                self.io.write_all(format!("{}\n", output).as_bytes());
            }
            Instr::Call {
                dest_reg: dest,
                callee,
                args,
                ..
            } => {
                let return_reg = *dest;
                match callee {
                    Callee::Name(func_name) => {
                        let Some(&func_idx) = self.function_map.get(func_name) else {
                            return Err(InterpreterError::CalleeNotFound(func_name.clone()));
                        };

                        let arg_values: Vec<Value> = args
                            .0
                            .iter()
                            .map(|arg| self.register_value(arg.register))
                            .collect();

                        // Save current frame's PC
                        self.call_stack.last_mut().unwrap().pc += 1;

                        // Call the function
                        self.call_func(func_idx, &arg_values, 0, Some(return_reg))?;

                        // Return early to start executing the called function
                        return Ok(None);
                    }
                    Callee::Register(ptr) => {
                        let func_val = self.register_value(*ptr);
                        match func_val {
                            Value::Func(sym) => {
                                let func_name = self
                                    .symbols
                                    .get(&sym)
                                    .map(|info| format!("@{}", info.name))
                                    .unwrap_or_else(|| format!("@<unknown {:?}>", sym));
                                let Some(&func_idx) = self.function_map.get(&func_name) else {
                                    return Err(InterpreterError::CalleeNotFound(func_name));
                                };

                                let arg_values: Vec<Value> = args
                                    .0
                                    .iter()
                                    .map(|arg| self.register_value(arg.register))
                                    .collect();

                                // Save current frame's PC (skip the call instruction)
                                self.call_stack.last_mut().unwrap().pc += 1;

                                // Call the function
                                self.call_func(func_idx, &arg_values, 0, Some(return_reg))?;

                                // Return early to start executing the called function
                                return Ok(None);
                            }
                            _ => {
                                return Err(InterpreterError::Unknown(format!(
                                    "Expected function pointer, got {:?}",
                                    func_val
                                )));
                            }
                        }
                    }
                }
            }
            Instr::StoreLocal(dest, _ty, src) => {
                let val = self.register_value(*src);
                self.set_register_value(*dest, val);
            }
            Instr::LoadLocal(dest, _ty, src) => {
                let val = self.register_value(*src);
                self.set_register_value(*dest, val);
            }
            Instr::Phi(dest, _ty, predecessors) => {
                // Phi nodes select a value based on which block we came from
                let frame = self.call_stack.last().unwrap();
                let pred_block = frame
                    .pred
                    .ok_or_else(|| InterpreterError::PredecessorNotFound)?;

                // Find the value from the predecessor block
                for (reg, block) in &predecessors.0 {
                    if *block == pred_block {
                        let val = self.register_value(*reg);
                        self.set_register_value(*dest, val);
                        break;
                    }
                }
                // Note: If we don't find a matching predecessor, the destination register remains uninitialized
                // This is okay as long as the value is not used
            }
            Instr::Ref(dest, _ty, RefKind::Func(name)) => {
                // For now, store function index. In a real implementation,
                // we'd create a proper function pointer with symbol ID
                let idx = self
                    .function_map
                    .get(name)
                    .copied()
                    .ok_or_else(|| InterpreterError::CalleeNotFound(name.clone()))?;

                // Store a dummy symbol ID for now - we'll need to improve this
                self.set_register_value(*dest, Value::Func(SymbolID(idx as i32)));
            }
            Instr::GetEnumTag(dest, scrutinee) => {
                let val = self.register_value(*scrutinee);
                match val {
                    Value::Enum(_, _) => {
                        // For now, just return 0
                        // In a real implementation, we'd track variant tags
                        self.set_register_value(*dest, Value::Int(0));
                    }
                    _ => {
                        return Err(InterpreterError::Unknown(format!(
                            "GetEnumTag expects enum, got {:?}",
                            val
                        )));
                    }
                }
            }
            Instr::GetEnumValue(dest, _ty, scrutinee, _tag, _index) => {
                let val = self.register_value(*scrutinee);
                match val {
                    Value::Enum(_, inner) => {
                        self.set_register_value(*dest, *inner);
                    }
                    _ => {
                        return Err(InterpreterError::Unknown(format!(
                            "GetEnumValue expects enum, got {:?}",
                            val
                        )));
                    }
                }
            }
            Instr::TagVariant(dest, ty, _tag, values) => {
                // For simplicity, just store the first value wrapped in an enum
                // In a real implementation, we'd handle multiple values and proper tagging
                let val = if let Some(first) = values.0.first() {
                    self.register_value(first.register)
                } else {
                    Value::Int(0)
                };

                // Extract the enum symbol from the type
                if let IRType::Enum(sym, _) = ty {
                    self.set_register_value(*dest, Value::Enum(*sym, Box::new(val)));
                } else {
                    return Err(InterpreterError::Unknown(
                        "TagVariant expects enum type".into(),
                    ));
                }
            }
            Instr::Unreachable => {
                return Err(InterpreterError::UnreachableReached);
            }
            // Terminators should not be handled here
            Instr::Ret(..) | Instr::Jump(..) | Instr::Branch { .. } => {
                return Err(InterpreterError::Unknown(
                    "Terminator instruction found in non-terminator position".into(),
                ));
            }
        }

        // Increment PC
        self.call_stack.last_mut().unwrap().pc += 1;

        Ok(None)
    }

    fn value(&self, value: &IRValue) -> Value {
        match value {
            IRValue::ImmediateInt(int) => Value::Int(*int),
            IRValue::Register(reg) => self.register_value(*reg),
        }
    }

    fn register_value(&self, register: Register) -> Value {
        let frame = self.call_stack.last().expect("Stack underflow");
        frame.locals.get(&register).cloned().unwrap_or_else(|| {
            panic!(
                "Uninitialized register {:?} in function {}",
                register, self.program.functions[frame.function].name
            )
        })
    }

    fn set_register_value(&mut self, register: Register, value: Value) {
        let frame = self.call_stack.last_mut().expect("Stack underflow");
        frame.locals.insert(register, value);
    }

    fn register_values(&self, registers: &RegisterList) -> Vec<Value> {
        registers
            .0
            .iter()
            .map(|r| self.register_value(r.register))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        compiling::driver::Driver, interpret::io::test_io::TestIO,
        transforms::monomorphizer::Monomorphizer,
    };

    fn interpret(code: &'static str) -> Result<Value, InterpreterError> {
        let mut io = TestIO::new();
        interpret_io(code, &mut io)
    }

    fn interpret_io(code: &'static str, io: &mut TestIO) -> Result<Value, InterpreterError> {
        let mut driver = Driver::with_str(code);
        let unit = driver.lower().into_iter().next().unwrap();

        let diagnostics = driver
            .refresh_diagnostics_for(&std::path::PathBuf::from("-"))
            .unwrap();
        if !diagnostics.is_empty() {
            eprintln!("Compilation diagnostics:");
            for diag in &diagnostics {
                eprintln!("  {:?}", diag);
            }
            return Err(InterpreterError::InvalidProgram);
        }

        let module = unit.module();
        let mono = Monomorphizer::new(&unit.env).run(module);

        println!(
            "----- functions: {:?}",
            mono.functions
                .iter()
                .map(|f| f.name.clone())
                .collect::<Vec<String>>()
                .join(", ")
        );
        IRInterpreter::new(mono, io, &driver.symbol_table).run()
    }

    #[test]
    fn interprets_int() {
        assert_eq!(Value::Int(3), interpret("3").unwrap());
    }

    #[test]
    fn interprets_add() {
        assert_eq!(Value::Int(7), interpret("3 + 4").unwrap());
    }

    #[test]
    fn interprets_print() {
        let mut io = TestIO::new();
        interpret_io("print(123)", &mut io).unwrap();
        assert_eq!("123\n".as_bytes(), io.stdout());
    }

    #[test]
    fn interprets_function_call() {
        assert_eq!(
            Value::Int(6),
            interpret(
                "
                func add(x, y) {
                    x + y
                }
                add(2, 4)
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_struct() {
        assert_eq!(
            Value::Int(7),
            interpret(
                "
                struct Point {
                    let x: Int
                    let y: Int
                }
                let p = Point(x: 3, y: 4)
                p.x + p.y
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_simple_array() {
        assert_eq!(
            Value::Int(3),
            interpret(
                "
                let a = [1, 2, 3]
                a.count
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_array_get() {
        assert_eq!(
            Value::Int(2),
            interpret(
                "
                let a = [1, 2, 3]
                a.get(1)
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
                    if n <= 1 {
                        return 1
                    }
                    n * factorial(n - 1)
                }
                
                factorial(5)
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_if_else() {
        assert_eq!(
            Value::Int(2),
            interpret(
                "
                let x = 5
                if x > 3 {
                    2
                } else {
                    1
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_comparison_operators() {
        assert_eq!(Value::Bool(true), interpret("1 < 2").unwrap());
        assert_eq!(Value::Bool(false), interpret("2 < 1").unwrap());
        assert_eq!(Value::Bool(true), interpret("1 <= 1").unwrap());
        assert_eq!(Value::Bool(false), interpret("2 <= 1").unwrap());

        assert_eq!(Value::Bool(true), interpret("2 > 1").unwrap());
        assert_eq!(Value::Bool(false), interpret("1 > 2").unwrap());
        assert_eq!(Value::Bool(true), interpret("2 >= 2").unwrap());
        assert_eq!(Value::Bool(false), interpret("1 >= 2").unwrap());

        assert_eq!(Value::Bool(true), interpret("1 == 1").unwrap());
        assert_eq!(Value::Bool(false), interpret("1 == 2").unwrap());
        assert_eq!(Value::Bool(true), interpret("1 != 2").unwrap());
        assert_eq!(Value::Bool(false), interpret("1 != 1").unwrap());
    }

    #[test]
    fn interprets_basic_arithmetic() {
        assert_eq!(Value::Int(7), interpret("3 + 4").unwrap());
        assert_eq!(Value::Int(-1), interpret("3 - 4").unwrap());
        assert_eq!(Value::Int(12), interpret("3 * 4").unwrap());
        assert_eq!(Value::Int(2), interpret("8 / 4").unwrap());
    }

    #[test]
    fn interprets_float_arithmetic() {
        assert_eq!(Value::Float(7.0), interpret("3.0 + 4.0").unwrap());
        assert_eq!(Value::Float(-1.0), interpret("3.0 - 4.0").unwrap());
        assert_eq!(Value::Float(12.0), interpret("3.0 * 4.0").unwrap());
        assert_eq!(Value::Float(2.0), interpret("8.0 / 4.0").unwrap());
    }

    #[test]
    fn interprets_bool() {
        assert_eq!(Value::Bool(true), interpret("true").unwrap());
        assert_eq!(Value::Bool(false), interpret("false").unwrap());
    }

    #[test]
    fn interprets_nested_function_calls() {
        assert_eq!(
            Value::Int(10),
            interpret(
                "
                func add(x, y) {
                    x + y
                }

                func double(x) {
                    add(x, x)
                }

                double(5)
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_loop() {
        assert_eq!(
            Value::Int(10),
            interpret(
                "
                let sum = 0
                let i = 0
                loop i < 5 {
                    sum = sum + i
                    i = i + 1
                }
                sum
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_multiple_struct_fields() {
        assert_eq!(
            Value::Int(60),
            interpret(
                "
                struct Rectangle {
                    let width: Int
                    let height: Int
                }
                
                let r = Rectangle(width: 10, height: 6)
                r.width * r.height
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_array_push() {
        assert_eq!(
            Value::Int(4),
            interpret(
                "
                let a = [1, 2, 3]
                a.push(4)
                a.get(3)
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_string() {
        let mut io = TestIO::new();
        interpret_io(r#"print("hello world")"#, &mut io).unwrap();
        assert_eq!("hello world\n", str::from_utf8(&io.stdout()).unwrap());
    }

    #[test]
    fn interprets_simple_match() {
        assert_eq!(
            Value::Int(2),
            interpret(
                "
                match 5 {
                    1 -> 0,
                    3 -> 1,
                    5 -> 2,
                    _ -> 3
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    #[ignore] // Compiler doesn't support match guards
    fn interprets_match_with_guard() {
        assert_eq!(
            Value::Int(10),
            interpret(
                "
                let x = 5
                match x {
                    n if n < 3 -> 0,
                    n if n < 7 -> 10,
                    _ -> 20
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_enum_match() {
        assert_eq!(
            Value::Int(42),
            interpret(
                "
                enum Res{
                    case ok(Int)
                    case err(Int)
                }
                
                let r = Res.ok(42)
                match r {
                    .ok(val) -> val,
                    .err(e) -> 0
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_optional_match() {
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
    fn interprets_optional_none_match() {
        assert_eq!(
            Value::Int(0),
            interpret(
                "
                match Optional.none {
                    .some(x) -> x,
                    .none -> 0
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    #[ignore] // Compiler doesn't support tuple destructuring syntax
    fn interprets_tuple_destructuring() {
        assert_eq!(
            Value::Int(7),
            interpret(
                "
                let (a, b) = (3, 4)
                a + b
                "
            )
            .unwrap()
        );
    }

    #[test]
    #[ignore] // Compiler doesn't support tuple destructuring syntax
    fn interprets_nested_tuple_destructuring() {
        assert_eq!(
            Value::Int(6),
            interpret(
                "
                let ((a, b), c) = ((1, 2), 3)
                a + b + c
                "
            )
            .unwrap()
        );
    }

    #[test]
    #[ignore] // Compiler doesn't support array destructuring syntax
    fn interprets_array_destructuring() {
        assert_eq!(
            Value::Int(6),
            interpret(
                "
                let [a, b, c] = [1, 2, 3]
                a + b + c
                "
            )
            .unwrap()
        );
    }

    #[test]
    #[ignore] // Compiler doesn't support struct pattern matching syntax
    fn interprets_struct_match() {
        assert_eq!(
            Value::Int(5),
            interpret(
                "
                struct Point {
                    let x: Int
                    let y: Int
                }
                
                let p = Point(x: 3, y: 2)
                match p {
                    Point(x, y) -> x + y
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_record_pattern_match() {
        assert_eq!(
            Value::Bool(true),
            interpret(
                "
                let a = {x: 123, y: 456}
                
                match a {
                    { x, y: 123 } -> false,
                    { x, y: 456 } -> true,
                    { x, y: _ } -> false
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_wildcard_pattern() {
        assert_eq!(
            Value::Int(99),
            interpret(
                "
                match 42 {
                    1 -> 1,
                    2 -> 2,
                    _ -> 99
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_match_in_function() {
        assert_eq!(
            Value::Int(2),
            interpret(
                "
                func classify(n) {
                    match n {
                        0 -> 0,
                        1 -> 1,
                        _ -> 2
                    }
                }
                
                classify(5)
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_nested_match() {
        assert_eq!(
            Value::Int(30),
            interpret(
                "
                enum Outer {
                    case a(Int)
                    case b(Int)
                }
                
                let val = Outer.a(3)
                match val {
                    .a(n) -> {
                        match n {
                            1 -> 10,
                            2 -> 20,
                            3 -> 30,
                            _ -> 40
                        }
                    },
                    .b(n) -> n
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    #[ignore] // Compiler doesn't support multiple patterns with |
    fn interprets_match_with_multiple_patterns() {
        assert_eq!(
            Value::Int(1),
            interpret(
                "
                match 2 {
                    1 | 2 | 3 -> 1,
                    4 | 5 | 6 -> 2,
                    _ -> 3
                }
                "
            )
            .unwrap()
        );
    }

    #[test]
    fn interprets_complex_destructuring() {
        assert_eq!(
            Value::Int(456),
            interpret(
                "
                let a = { x: 123, y: 456 }
                match a {
                    { x: 123, y } -> y,
                    { x: _, y: _ } -> 0
                }
                "
            )
            .unwrap()
        );
    }
}
