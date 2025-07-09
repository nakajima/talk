use std::collections::HashMap;

use inkwell::{
    AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel,
    builder::Builder,
    context::Context,
    execution_engine::ExecutionEngine,
    module::{Linkage, Module},
    support::LLVMString,
    types::{AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum},
    values::{BasicValue, BasicValueEnum, IntMathValue, IntValue, PointerValue},
};

use crate::{
    SymbolID,
    lowering::{
        instr::Instr,
        ir_module::{IRConstantData, IRModule},
        ir_type::IRType,
        ir_value::IRValue,
        register::Register,
    },
};

// helper to fetch and cast in one line
macro_rules! get_int {
    ($registers:expr, $reg:expr) => {
        $registers.get($reg).expect("reg missing").into_int_value()
    };
}
macro_rules! get_float {
    ($registers:expr, $reg:expr) => {
        $registers
            .get($reg)
            .expect("reg missing")
            .into_float_value()
    };
}

#[derive(Debug)]
pub enum LLVMGenError {
    CouldNotCreateEngine,
}

#[derive(Debug)]
pub struct LLVMGenerator<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}

#[allow(clippy::unwrap_used)]
#[allow(clippy::todo)]
#[allow(clippy::panic)]
impl IRType {
    fn to_basic_type<'a>(&self, context: &'a Context) -> Option<BasicTypeEnum<'a>> {
        match self {
            IRType::Int => Some(BasicTypeEnum::IntType(context.i64_type())),
            IRType::Float => Some(BasicTypeEnum::FloatType(context.f64_type())),
            IRType::Bool => Some(BasicTypeEnum::IntType(context.bool_type())),
            IRType::Byte => Some(BasicTypeEnum::IntType(context.i8_type())),
            IRType::Enum(_, _) => todo!(),
            IRType::Struct(_, fields, _) | IRType::Tuple { elements: fields } => {
                let fields = fields
                    .iter()
                    .filter_map(|f| f.to_basic_type(context))
                    .collect::<Vec<BasicTypeEnum>>();
                Some(BasicTypeEnum::StructType(
                    context.struct_type(&fields, false),
                ))
            }
            IRType::Pointer { .. } | IRType::RawBuffer | IRType::TypedBuffer { .. } => Some(
                BasicTypeEnum::PointerType(context.ptr_type(AddressSpace::default())),
            ),
            IRType::TypeVar(_) => panic!("Should not have type variables at LLVM generation phase"),
            IRType::Func(_, _) => None,
            IRType::Void => None,
        }
    }

    fn to_metadata_type<'a>(&self, context: &'a Context) -> Option<BasicMetadataTypeEnum<'a>> {
        match self {
            IRType::Int => Some(BasicMetadataTypeEnum::IntType(context.i64_type())),
            IRType::Float => Some(BasicMetadataTypeEnum::FloatType(context.f64_type())),
            IRType::Bool => Some(BasicMetadataTypeEnum::IntType(context.bool_type())),
            IRType::Byte => Some(BasicMetadataTypeEnum::IntType(context.i8_type())),
            IRType::Enum(_, _) => todo!(),
            IRType::Struct(_, fields, _) | IRType::Tuple { elements: fields } => {
                let fields = fields
                    .iter()
                    .filter_map(|f| f.to_basic_type(context))
                    .collect::<Vec<BasicTypeEnum>>();
                Some(BasicMetadataTypeEnum::StructType(
                    context.struct_type(&fields, false),
                ))
            }
            IRType::Pointer { .. } | IRType::RawBuffer | IRType::TypedBuffer { .. } => Some(
                BasicMetadataTypeEnum::PointerType(context.ptr_type(AddressSpace::default())),
            ),

            _ => None,
        }
    }

    fn to_any_type<'a>(&self, context: &'a Context) -> Option<AnyTypeEnum<'a>> {
        match self {
            IRType::Int => Some(AnyTypeEnum::IntType(context.i64_type())),
            IRType::Float => Some(AnyTypeEnum::FloatType(context.f64_type())),
            IRType::Bool => Some(AnyTypeEnum::IntType(context.bool_type())),
            IRType::Byte => Some(AnyTypeEnum::IntType(context.i8_type())),
            IRType::Func(params, ret) => {
                let params = params
                    .iter()
                    .filter_map(|p| p.to_metadata_type(context))
                    .collect::<Vec<BasicMetadataTypeEnum>>();
                Some(AnyTypeEnum::FunctionType(
                    ret.to_basic_type(context).unwrap().fn_type(&params, false),
                ))
            }
            IRType::Enum(_, _) => todo!(),
            IRType::Struct(_, fields, _) | IRType::Tuple { elements: fields } => {
                let fields = fields
                    .iter()
                    .filter_map(|f| f.to_basic_type(context))
                    .collect::<Vec<BasicTypeEnum>>();
                Some(AnyTypeEnum::StructType(context.struct_type(&fields, false)))
            }
            IRType::Pointer { .. } | IRType::RawBuffer | IRType::TypedBuffer { .. } => Some(
                AnyTypeEnum::PointerType(context.ptr_type(AddressSpace::default())),
            ),
            IRType::TypeVar(_) => panic!("Should not have type variables at LLVM generation phase"),
            IRType::Void => None,
        }
    }
}

#[allow(clippy::unimplemented)]
#[allow(clippy::unwrap_used)]
impl<'ctx> LLVMGenerator<'ctx> {
    pub fn new(name: &str, context: &'ctx Context) -> Result<Self, LLVMString> {
        let module = context.create_module(name);
        let builder = context.create_builder();
        let execution_engine = module.create_jit_execution_engine(OptimizationLevel::None)?;

        Ok(Self {
            context,
            module,
            builder,
            execution_engine,
        })
    }

    pub fn run(self, module: IRModule) -> Result<String, LLVMGenError> {
        for (i, constant) in module.constants.iter().enumerate() {
            let val = match constant {
                IRConstantData::RawBuffer(bytes) => self.context.const_string(bytes, false),
            };

            let global =
                self.module
                    .add_global(val.get_type(), None, format!("global_{i}").as_str());
            global.set_initializer(&val);
            global.set_constant(true);
        }

        for function in module.functions.iter() {
            let mut params = function
                .args()
                .iter()
                .map(|i| i.to_metadata_type(self.context).unwrap())
                .collect::<Vec<BasicMetadataTypeEnum>>();

            if let Some(env_ty) = &function.env_ty {
                params.insert(0, env_ty.to_metadata_type(self.context).unwrap());
            }

            let llvm_func_type = if let Some(ret) = function.ret().to_basic_type(self.context) {
                ret.fn_type(&params, false)
            } else {
                self.context.void_type().fn_type(&params, false)
            };

            let func =
                self.module
                    .add_function(&function.name, llvm_func_type, Some(Linkage::External));

            let mut registers: HashMap<Register, BasicValueEnum> = Default::default();

            for (i, _) in params.iter().enumerate() {
                registers.insert(Register(i as i32), func.get_nth_param(i as u32).unwrap());
            }

            for block in function.blocks.iter() {
                let basic_block = self
                    .context
                    .append_basic_block(func, block.label().as_str());
                self.builder.position_at_end(basic_block);

                for instruction in block.instructions.iter() {
                    match instruction {
                        Instr::ConstantInt(reg, val) => {
                            let val = self.context.i64_type().const_int(*val as u64, true);
                            registers.insert(*reg, BasicValueEnum::IntValue(val));
                        }
                        Instr::ConstantFloat(reg, val) => {
                            let val = self.context.f64_type().const_float(*val);
                            registers.insert(*reg, BasicValueEnum::FloatValue(val));
                        }
                        Instr::ConstantBool(reg, val) => {
                            let val = if *val {
                                self.context.bool_type().const_all_ones()
                            } else {
                                self.context.bool_type().const_zero()
                            };

                            registers.insert(*reg, BasicValueEnum::IntValue(val));
                        }
                        Instr::Add(dest, ty, op1, op2) => {
                            let reg = match ty {
                                IRType::Int => {
                                    println!("{}", self.module.to_string());
                                    let op1 = registers.get(op1).unwrap();
                                    let op2 = registers.get(op2).unwrap();
                                    BasicValueEnum::IntValue(
                                        self.builder
                                            .build_int_add(
                                                op1.into_int_value(),
                                                op2.into_int_value(),
                                                dest.to_string().as_str(),
                                            )
                                            .unwrap(),
                                    )
                                }
                                IRType::Float => {
                                    let op1 = registers.get(op1).unwrap();
                                    let op2 = registers.get(op2).unwrap();
                                    BasicValueEnum::FloatValue(
                                        self.builder
                                            .build_float_add(
                                                op1.into_float_value(),
                                                op2.into_float_value(),
                                                dest.to_string().as_str(),
                                            )
                                            .unwrap(),
                                    )
                                }
                                _ => unimplemented!(),
                            };

                            registers.insert(*dest, reg);
                        }
                        Instr::Sub(dest, irtype, op1, op2) => {
                            let v = match irtype {
                                IRType::Int => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_int_sub(
                                            get_int!(registers, op1),
                                            get_int!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                IRType::Float => BasicValueEnum::FloatValue(
                                    self.builder
                                        .build_float_sub(
                                            get_float!(registers, op1),
                                            get_float!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                _ => unimplemented!("Sub only handles Int/Float right now"),
                            };
                            registers.insert(*dest, v);
                        }
                        Instr::Mul(dest, irtype, op1, op2) => {
                            let v = match irtype {
                                IRType::Int => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_int_mul(
                                            get_int!(registers, op1),
                                            get_int!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                IRType::Float => BasicValueEnum::FloatValue(
                                    self.builder
                                        .build_float_mul(
                                            get_float!(registers, op1),
                                            get_float!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                _ => unimplemented!("Sub only handles Int/Float right now"),
                            };
                            registers.insert(*dest, v);
                        }
                        Instr::Div(dest, irtype, op1, op2) => {
                            let v = match irtype {
                                IRType::Int => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_int_signed_div(
                                            get_int!(registers, op1),
                                            get_int!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                IRType::Float => BasicValueEnum::FloatValue(
                                    self.builder
                                        .build_float_div(
                                            get_float!(registers, op1),
                                            get_float!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                _ => unimplemented!("Sub only handles Int/Float right now"),
                            };

                            registers.insert(*dest, v);
                        }
                        Instr::LessThan(dest, irtype, op1, op2) => {
                            let v = match irtype {
                                IRType::Int => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_int_compare(
                                            IntPredicate::SLT,
                                            get_int!(registers, op1),
                                            get_int!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                IRType::Float => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_float_compare(
                                            FloatPredicate::OLT,
                                            get_float!(registers, op1),
                                            get_float!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                _ => unimplemented!("Sub only handles Int/Float right now"),
                            };

                            registers.insert(*dest, v);
                        }
                        Instr::LessThanEq(dest, irtype, op1, op2) => {
                            let v = match irtype {
                                IRType::Int => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_int_compare(
                                            IntPredicate::SLE,
                                            get_int!(registers, op1),
                                            get_int!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                IRType::Float => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_float_compare(
                                            FloatPredicate::OLE,
                                            get_float!(registers, op1),
                                            get_float!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                _ => unimplemented!("Sub only handles Int/Float right now"),
                            };

                            registers.insert(*dest, v);
                        }
                        Instr::GreaterThan(dest, irtype, op1, op2) => {
                            let v = match irtype {
                                IRType::Int => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_int_compare(
                                            IntPredicate::SGT,
                                            get_int!(registers, op1),
                                            get_int!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                IRType::Float => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_float_compare(
                                            FloatPredicate::OGT,
                                            get_float!(registers, op1),
                                            get_float!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                _ => unimplemented!("Sub only handles Int/Float right now"),
                            };

                            registers.insert(*dest, v);
                        }
                        Instr::GreaterThanEq(dest, irtype, op1, op2) => {
                            let v = match irtype {
                                IRType::Int => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_int_compare(
                                            IntPredicate::SGE,
                                            get_int!(registers, op1),
                                            get_int!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                IRType::Float => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_float_compare(
                                            FloatPredicate::OGE,
                                            get_float!(registers, op1),
                                            get_float!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                _ => unimplemented!("Sub only handles Int/Float right now"),
                            };

                            registers.insert(*dest, v);
                        }
                        Instr::Eq(dest, irtype, op1, op2) => {
                            let v = match irtype {
                                IRType::Int => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_int_compare(
                                            IntPredicate::EQ,
                                            get_int!(registers, op1),
                                            get_int!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                IRType::Float => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_float_compare(
                                            FloatPredicate::OEQ,
                                            get_float!(registers, op1),
                                            get_float!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                _ => unimplemented!("Sub only handles Int/Float right now"),
                            };

                            registers.insert(*dest, v);
                        }
                        Instr::Ne(dest, irtype, op1, op2) => {
                            let v = match irtype {
                                IRType::Int => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_int_compare(
                                            IntPredicate::NE,
                                            get_int!(registers, op1),
                                            get_int!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                IRType::Float => BasicValueEnum::IntValue(
                                    self.builder
                                        .build_float_compare(
                                            FloatPredicate::ONE,
                                            get_float!(registers, op1),
                                            get_float!(registers, op2),
                                            &dest.to_string(),
                                        )
                                        .unwrap(),
                                ),
                                _ => unimplemented!("Sub only handles Int/Float right now"),
                            };

                            registers.insert(*dest, v);
                        }
                        Instr::StoreLocal(register, irtype, register1) => todo!(),
                        Instr::LoadLocal(register, irtype, register1) => todo!(),
                        Instr::Phi(dest, irtype, phi_predecessors) => todo!(),
                        Instr::Ref(dest, irtype, ref_kind) => todo!(),

                        Instr::Alloc { dest, ty, count } => todo!(),
                        Instr::Const { dest, ty, val } => todo!(),
                        Instr::Store { ty, val, location } => todo!(),
                        Instr::Load { dest, ty, addr } => todo!(),
                        Instr::GetElementPointer {
                            dest,
                            base,
                            ty,
                            index,
                        } => {
                            //------------------------------------------------------------------
                            // 1. Grab the base pointer that we’re indexing from the register map
                            //------------------------------------------------------------------
                            let base_ptr = registers
                                .get(base)
                                .expect("base reg missing")
                                .into_pointer_value();

                            //------------------------------------------------------------------
                            // 2. Turn `index` (IRValue) into an LLVM i64 constant / value
                            //------------------------------------------------------------------
                            let i64_ty = self.context.i64_type();
                            let idx_val = match index {
                                IRValue::ImmediateInt(n) => i64_ty.const_int(*n as u64, true),
                                IRValue::Register(r) => registers.get(r).unwrap().into_int_value(),
                                _ => {
                                    unimplemented!("GEP index must be int literal or int register")
                                }
                            };

                            //------------------------------------------------------------------
                            // 3. Choose the right GEP helper based on the pointee type
                            //------------------------------------------------------------------
                            let gep_ptr = match ty {
                                // -------- struct (or your special closure struct) ------------
                                IRType::Struct(sym, _, _) if *sym != SymbolID::STRING => {
                                    // Field access in LLVM is [0, field_index]
                                    //  *first* index steps into the struct itself,
                                    //  second index picks the field.
                                    let zero = i64_ty.const_zero();
                                    unsafe {
                                        self.builder
                                            .build_in_bounds_gep(
                                                ty.to_basic_type(self.context).unwrap(),
                                                base_ptr,
                                                &[zero, idx_val],
                                                &dest.to_string(),
                                            )
                                            .unwrap()
                                    }
                                    // NOTE: if you prefer the convenience helper:
                                    //   self.builder.build_struct_gep(base_ptr, idx, name).unwrap()
                                }

                                // -------- pointer-to-array / slice ---------------------------
                                IRType::RawBuffer => unsafe {
                                    self.builder
                                        .build_in_bounds_gep(
                                            ty.to_basic_type(self.context).unwrap(),
                                            base_ptr,
                                            &[idx_val],
                                            &dest.to_string(),
                                        )
                                        .unwrap()
                                },

                                _ => unimplemented!("GEP not implemented for {:?}", ty),
                            };

                            //------------------------------------------------------------------
                            // 4. Stash resulting pointer in the register table
                            //------------------------------------------------------------------
                            registers.insert(*dest, BasicValueEnum::PointerValue(gep_ptr));
                        }
                        Instr::MakeStruct { dest, ty, values } => todo!(),
                        Instr::GetValueOf {
                            dest,
                            ty,
                            structure,
                            index,
                        } => todo!(),
                        Instr::Call {
                            dest_reg,
                            ty,
                            callee,
                            args,
                        } => todo!(),
                        Instr::GetEnumTag(register, register1) => todo!(),
                        Instr::GetEnumValue(register, irtype, register1, _, _) => todo!(),
                        Instr::TagVariant(register, irtype, _, register_list) => todo!(),
                        Instr::Ret(_, irvalue) => {
                            println!("{irvalue:?}, {registers:#?}");
                            if let Some(IRValue::Register(reg)) = irvalue {
                                self.builder
                                    .build_return(Some(registers.get(reg).unwrap()))
                                    .unwrap();
                            } else {
                                self.builder.build_return(None).unwrap();
                            }
                        }
                        Instr::Jump(basic_block_id) => todo!(),
                        Instr::Branch {
                            cond,
                            true_target,
                            false_target,
                        } => todo!(),
                        Instr::Print { val } => todo!(),
                        Instr::Unreachable => todo!(),
                    }
                }
            }
        }

        Ok(self.module.to_string())
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use inkwell::context::Context;

    use crate::{
        compiling::driver::{Driver, DriverConfig},
        lowering::{ir_error::IRError, ir_module::IRModule},
        transforms::{llvm_generator::LLVMGenerator, monomorphizer::Monomorphizer},
    };

    fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let mut driver = Driver::new(DriverConfig {
            executable: true,
            include_prelude: true,
            include_comments: false,
        });
        driver.update_file(&PathBuf::from("-"), input.into());
        let lowered = driver.lower().into_iter().next().unwrap();
        let diagnostics = driver.refresh_diagnostics_for(&PathBuf::from("-"));
        let module = lowered.module().clone();

        let mono = Monomorphizer::new(&lowered.env).run(module);

        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        Ok(mono)
    }

    #[test]
    fn lowers_basic_llvm_string() {
        let lowered = lower(
            r#"
        let a = 1
        let b = 2
         __ir_instr("$? = add int %0, %1;")

         struct Person {
            let age: Int
         }

         let person = Person(age: 123)
         person.age + 1
        "#,
        )
        .unwrap();

        let context = Context::create();
        let program = LLVMGenerator::new("Moddy", &context)
            .unwrap()
            .run(lowered)
            .unwrap();

        println!("Dope");
        println!("{}", program);
    }
}
