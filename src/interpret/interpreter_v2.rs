use crate::{
    SymbolTable,
    interpret::{
        io::InterpreterIO,
        memory_v2::{Memory, Pointer, MemoryLocation},
        value_v2::Value,
    },
    lowering::{
        instr::{Callee, Instr},
        ir_error::IRError,
        ir_module::IRModule,
        ir_type::IRType,
        ir_value::IRValue,
        lowerer::{BasicBlockID, RegisterList},
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

        self.call_func(main_idx, &[], 0, None)?;
        
        match self.execute() {
            Ok(Some(result)) => Ok(result),
            Ok(None) => Ok(Value::Int(0)),
            Err(e) => Err(e),
        }
    }

    fn call_func(
        &mut self,
        func_idx: usize,
        args: &[Value],
        call_block: usize,
        return_register: Option<Register>,
    ) -> Result<(), InterpreterError> {
        let stack_base = self.memory.get_stack_pointer();
        
        let mut locals = HashMap::new();
        
        // Initialize parameters
        let func = &self.program.functions[func_idx];
        let func_args = func.args();
        for (i, arg_ty) in func_args.iter().enumerate() {
            if let Some(arg) = args.get(i) {
                // Parameters start at register 0
                locals.insert(Register(i as i32), arg.clone());
            }
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
                let is_term = matches!(&instr, Instr::Ret(..) | Instr::Jump(..) | Instr::Branch { .. } | Instr::Unreachable);
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
                    Some(v) => self.value(v),
                    None => Value::Int(0),
                };
                Ok(Some(result))
            }
            Instr::Jump(block) => {
                self.jump_to_block(*block)?;
                Ok(None)
            }
            Instr::Branch { cond, true_target, false_target } => {
                let cond_val = self.register_value(*cond);
                match cond_val {
                    Value::Bool(true) => self.jump_to_block(*true_target)?,
                    Value::Bool(false) => self.jump_to_block(*false_target)?,
                    _ => return Err(InterpreterError::TypeError(
                        format!("{:?}", cond_val),
                        "bool".into(),
                    )),
                }
                Ok(None)
            }
            Instr::Unreachable => Err(InterpreterError::UnreachableReached),
            _ => Err(InterpreterError::Unknown(
                format!("Invalid terminator: {:?}", terminator)
            )),
        }
    }

    fn jump_to_block(&mut self, block_id: BasicBlockID) -> Result<(), InterpreterError> {
        let frame = self.call_stack.last_mut().unwrap();
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
                let count_val = count.as_ref().map(|c| self.value(c)).unwrap_or(Value::Int(1));
                let Value::Int(count) = count_val else {
                    return Err(InterpreterError::Unknown("Invalid alloc count".into()));
                };
                let ptr = self.memory.heap_alloc(ty, count as usize)?;
                self.set_register_value(*dest, Value::Pointer(ptr));
            }
            Instr::Store { val, location, ty } => {
                let loc_val = self.register_value(*location);
                match loc_val {
                    Value::Pointer(ptr) => {
                        let val = self.value(val);
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
            Instr::Load { dest, addr, ty } => {
                let addr_val = self.register_value(*addr);
                match addr_val {
                    Value::Pointer(ptr) => {
                        let val = Value::load_from_memory(&self.memory, &ptr)?;
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
                dest, base, index, ..
            } => {
                let index_val = match index {
                    IRValue::ImmediateInt(int) => *int,
                    IRValue::Register(reg) => {
                        match self.register_value(*reg) {
                            Value::Int(int) => int,
                            val => {
                                return Err(InterpreterError::TypeError(
                                    format!("{:?}", val),
                                    "int".to_string(),
                                ));
                            }
                        }
                    }
                };
                
                let base_val = self.register_value(*base);
                match base_val {
                    Value::Pointer(mut ptr) => {
                        // Calculate element size based on pointer type
                        let elem_size = match &ptr.ty {
                            IRType::Pointer { .. } => 8,
                            IRType::TypedBuffer { element } => Memory::type_info(element).size,
                            _ => Memory::type_info(&ptr.ty).size,
                        };
                        
                        ptr.addr += (index_val as usize) * elem_size;
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
            Instr::Print { ty, val } => {
                let val = self.value(val);
                
                let val = if let Value::Pointer(ptr) = val {
                    Value::load_from_memory(&self.memory, &ptr)?
                } else {
                    val
                };
                
                let output = val.display(|sym| {
                    self.symbols.get(&sym)
                        .map(|info| info.name.clone())
                        .unwrap_or_else(|| format!("<unknown {:?}>", sym))
                });
                self.io.write_all(format!("{}\n", output).as_bytes());
            }
            Instr::Call { dest_reg: dest, callee, args, .. } => {
                let return_reg = *dest;
                match callee {
                    Callee::Name(func_name) => {
                        let Some(&func_idx) = self.function_map.get(func_name) else {
                            return Err(InterpreterError::CalleeNotFound(func_name.clone()));
                        };
                        
                        let arg_values: Vec<Value> = args.0.iter()
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
                                let func_name = self.symbols.get(&sym)
                                .map(|info| format!("@{}", info.name))
                                .unwrap_or_else(|| format!("@<unknown {:?}>", sym));
                                let Some(&func_idx) = self.function_map.get(&func_name) else {
                                    return Err(InterpreterError::CalleeNotFound(func_name));
                                };
                                
                                let arg_values: Vec<Value> = args.0.iter()
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
            _ => {
                return Err(InterpreterError::Unknown(format!(
                    "Unimplemented instruction: {:?}",
                    instr
                )));
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
        registers.0.iter()
            .map(|r| self.register_value(r.register))
            .collect()
    }
}