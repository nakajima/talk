use std::collections::HashMap;

use crate::lowering::ir::{BasicBlock, BasicBlockID, IRFunction, Instr, Register, Terminator};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(u64),
    Float(f64),
    Bool(bool),
    // Represents a memory address, typically for locals. Can be derived from an Int value.
    Address(u32),
}

#[allow(dead_code)]
impl Value {
    fn as_int(&self) -> u64 {
        match self {
            Value::Int(i) => *i,
            _ => panic!("Type error: Expected Int, found {:?}", self),
        }
    }

    fn as_float(&self) -> f64 {
        match self {
            Value::Float(f) => *f,
            _ => panic!("Type error: Expected Float, found {:?}", self),
        }
    }

    fn as_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            _ => panic!("Type error: Expected Bool, found {:?}", self),
        }
    }

    fn as_address(&self) -> u32 {
        match self {
            // An address can be directly stored or be the content of an Int register.
            Value::Address(addr) => *addr,
            Value::Int(val) => *val as u32, // Interpret Int register content as address
            _ => panic!(
                "Type error: Expected Address or Int for address, found {:?}",
                self
            ),
        }
    }
}

pub struct VM<'a> {
    function: &'a IRFunction,
    /// Quick lookup for blocks by their ID
    block_map: HashMap<BasicBlockID, &'a BasicBlock>,
    registers: HashMap<Register, Value>,
    locals: HashMap<u32, Value>, // Memory for local variables, keyed by a u32 address

    current_block_id: BasicBlockID,
    prev_block_id: Option<BasicBlockID>, // For Phi instructions
    ip: usize, // Instruction pointer within the current_block's instruction list

    halted: bool,
    return_value: Option<Value>,
}

impl<'a> VM<'a> {
    pub fn new(function: &'a IRFunction) -> Self {
        if function.blocks.is_empty() {
            panic!("Cannot execute a function with no basic blocks.");
        }

        let mut block_map = HashMap::new();
        for block in &function.blocks {
            block_map.insert(block.id, block);
        }

        // Assume the first block in the list is the entry point.
        let entry_block_id = function.blocks[0].id;

        VM {
            function,
            block_map,
            registers: HashMap::new(),
            locals: HashMap::new(),
            current_block_id: entry_block_id,
            prev_block_id: None,
            ip: 0,
            halted: false,
            return_value: None,
        }
    }

    fn get_reg_val(&self, reg: Register) -> &Value {
        self.registers
            .get(&reg)
            .unwrap_or_else(|| panic!("Fatal error: Read from uninitialized register {:?}", reg))
    }

    fn set_reg_val(&mut self, reg: Register, value: Value) {
        self.registers.insert(reg, value);
    }

    /// Runs the VM until it halts.
    pub fn run(&mut self) -> Option<Value> {
        while !self.halted {
            self.step();
        }
        self.return_value.clone()
    }

    /// Executes a single step of the VM (one instruction or a terminator).
    fn step(&mut self) {
        if self.halted {
            return;
        }

        let current_block = self
            .block_map
            .get(&self.current_block_id)
            .unwrap_or_else(|| {
                panic!(
                    "Fatal error: Current block ID {:?} not found in block map.",
                    self.current_block_id
                )
            });

        if self.ip < current_block.instructions.len() {
            // Clone instruction to avoid complex borrow scenarios if it modified VM state
            // in a way that interfered with borrowing `current_block`.
            let instr_to_execute = current_block.instructions[self.ip].clone();
            self.execute_instruction(instr_to_execute);
            self.ip += 1;
        } else {
            let terminator_to_execute = current_block.terminator.clone();
            self.execute_terminator(terminator_to_execute);
        }
    }

    fn execute_instruction(&mut self, instr: Instr) {
        // For debugging:
        println!("Regs: {:?}, Locals: {:?}", self.registers, self.locals);
        println!(
            "Executing @{:?}.{:?}: {:?}",
            self.current_block_id, self.ip, instr
        );

        match instr {
            Instr::ConstantInt(dest, val) => self.set_reg_val(dest, Value::Int(val)),
            Instr::ConstantFloat(dest, val) => self.set_reg_val(dest, Value::Float(val)),
            Instr::ConstantBool(dest, val) => self.set_reg_val(dest, Value::Bool(val)),
            Instr::Add(dest, src1, src2) => {
                let v1 = self.get_reg_val(src1);
                let v2 = self.get_reg_val(src2);
                match (v1, v2) {
                    (Value::Int(i1), Value::Int(i2)) => self.set_reg_val(dest, Value::Int(i1 + i2)),
                    (Value::Float(f1), Value::Float(f2)) => {
                        self.set_reg_val(dest, Value::Float(f1 + f2))
                    }
                    _ => panic!("Type error for Add: {:?}, {:?}", v1, v2),
                }
            }
            Instr::Sub(dest, src1, src2) => {
                let v1 = self.get_reg_val(src1);
                let v2 = self.get_reg_val(src2);
                match (v1, v2) {
                    (Value::Int(i1), Value::Int(i2)) => self.set_reg_val(dest, Value::Int(i1 - i2)),
                    (Value::Float(f1), Value::Float(f2)) => {
                        self.set_reg_val(dest, Value::Float(f1 - f2))
                    }
                    _ => panic!("Type error for Sub: {:?}, {:?}", v1, v2),
                }
            }
            Instr::Mul(dest, src1, src2) => {
                let v1 = self.get_reg_val(src1);
                let v2 = self.get_reg_val(src2);
                match (v1, v2) {
                    (Value::Int(i1), Value::Int(i2)) => self.set_reg_val(dest, Value::Int(i1 * i2)),
                    (Value::Float(f1), Value::Float(f2)) => {
                        self.set_reg_val(dest, Value::Float(f1 * f2))
                    }
                    _ => panic!("Type error for Mul: {:?}, {:?}", v1, v2),
                }
            }
            Instr::Div(dest, src1, src2) => {
                let v1 = self.get_reg_val(src1);
                let v2 = self.get_reg_val(src2);
                match (v1, v2) {
                    (Value::Int(i1), Value::Int(i2)) => {
                        if *i2 == 0 {
                            panic!("Division by zero (Int)");
                        }
                        self.set_reg_val(dest, Value::Int(i1 / i2));
                    }
                    (Value::Float(f1), Value::Float(f2)) => {
                        if *f2 == 0.0 {
                            panic!("Division by zero (Float)");
                        }
                        self.set_reg_val(dest, Value::Float(f1 / f2));
                    }
                    _ => panic!("Type error for Div: {:?}, {:?}", v1, v2),
                }
            }
            Instr::StoreLocal(addr_reg, val_reg) => {
                let address = self.get_reg_val(addr_reg).as_address();
                let value_to_store = self.get_reg_val(val_reg).clone();
                self.locals.insert(address, value_to_store);
            }
            Instr::LoadLocal(dest_reg, addr_reg) => {
                let address = self.get_reg_val(addr_reg).as_address();
                let loaded_value = self
                    .locals
                    .get(&address)
                    .unwrap_or_else(|| {
                        panic!(
                            "Fatal error: Read from uninitialized local slot at address {}",
                            address
                        )
                    })
                    .clone();
                self.set_reg_val(dest_reg, loaded_value);
            }
            Instr::Phi(dest_reg, sources) => {
                let predecessor_block_id = self.prev_block_id
                    .unwrap_or_else(|| panic!("Phi instruction in block {:?} executed without a predecessor block ID. Phi nodes should not be at the function entry block's start if no prior block could lead to it.", self.current_block_id));

                let mut value_found = false;
                for (src_register, pred_block_candidate_id) in &sources {
                    if pred_block_candidate_id == &predecessor_block_id {
                        let value = self.get_reg_val(*src_register).clone();
                        self.set_reg_val(dest_reg, value);
                        value_found = true;
                        break;
                    }
                }
                if !value_found {
                    panic!(
                        "Phi instruction in block {:?} did not find a source for predecessor block {:?}. Sources: {:?}",
                        self.current_block_id, predecessor_block_id, sources
                    );
                }
            }
            Instr::Ref(_register, _ref_kind) => {
                todo!()
            }
            Instr::Call { .. } => {
                todo!()
            }
        }
    }

    fn execute_terminator(&mut self, term: Terminator) {
        // For debugging:
        // println!("Executing @{}.T: {:?}", self.current_block_id.0, term);
        let previously_current_block_id = self.current_block_id;

        match term {
            Terminator::Ret(opt_reg) => {
                self.return_value = opt_reg.map(|reg| self.get_reg_val(reg).clone());
                self.halted = true;
            }
            Terminator::Unreachable => {
                eprintln!(
                    "VM Error: Reached Unreachable terminator in block {:?}. Halting.",
                    self.current_block_id
                );
                self.halted = true; // Or panic, depending on desired strictness
            }
            Terminator::Jump(target_block_id) => {
                self.prev_block_id = Some(previously_current_block_id);
                self.current_block_id = target_block_id;
                self.ip = 0; // Reset instruction pointer for the new block
            }
            Terminator::JumpUnless(condition_reg, target_block_id_if_false) => {
                let condition_value = self.get_reg_val(condition_reg).as_bool();
                self.prev_block_id = Some(previously_current_block_id);

                if !condition_value {
                    // If condition is false, jump to target_block_id_if_false
                    self.current_block_id = target_block_id_if_false;
                } else {
                    // If condition is true, fall through to the "next" block.
                    // This assumes blocks are laid out sequentially in the IRFunction's blocks vector
                    // and the IR generator (Lowerer) places the true-branch block immediately after
                    // the block containing the conditional jump.
                    let current_block_index = self
                        .function
                        .blocks
                        .iter()
                        .position(|b| b.id == previously_current_block_id)
                        .expect("Current block not found in function's block list");

                    if current_block_index + 1 < self.function.blocks.len() {
                        self.current_block_id = self.function.blocks[current_block_index + 1].id;
                    } else {
                        panic!(
                            "JumpUnless true branch fell off the end of the function block list from block {:?}",
                            previously_current_block_id
                        );
                    }
                }
                self.ip = 0; // Reset instruction pointer for the new block
            }
        }
    }
}
