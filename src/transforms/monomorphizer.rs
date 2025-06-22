use std::collections::{HashMap, HashSet};

use crate::lowering::{
    instr::{Callee, Instr},
    ir_module::IRModule,
    ir_type::IRType,
    lowerer::{BasicBlock, IRFunction, RegisterList, TypedRegister},
};

/// The Monomorphizer monomorphizes. So it takes a func like this:
///
///     func identity(x) { x }
///
/// which lowers to (T1) -> T1. And then given a call like this:
///
///     identity(123)
///
/// and it'll generate a version of identity that lowers to (Int) -> Int.
/// It'll also update calls to the generic form to the specialized form.
#[derive(Default)]
pub struct Monomorphizer {
    cache: HashSet<String>,
    generic_functions: Vec<IRFunction>,
}

impl Monomorphizer {
    pub fn new() -> Self {
        Self {
            cache: Default::default(),
            generic_functions: Default::default(),
        }
    }

    pub fn run(mut self, module: IRModule) -> IRModule {
        let mut module = module;

        let (generic_templates, concrete_funcs): (Vec<_>, Vec<_>) =
            module.functions.into_iter().partition(|f| {
                log::warn!("is generic: {} {:?}", is_generic(f), f.name);
                is_generic(f)
            });

        self.generic_functions = generic_templates;

        let mut final_functions = Vec::new();

        for func in concrete_funcs {
            final_functions.push(self.detect_monomorphizations_in(func));
        }

        let instantiated_functions = self.generic_functions;

        for f in instantiated_functions.iter() {
            log::info!(
                "-> instantiated function: {:?} {:?} {:?}",
                f.name.clone(),
                f.env_ty,
                is_generic(f)
            );
        }
        final_functions.extend(
            instantiated_functions
                .into_iter()
                .filter(|f| !is_generic(f)),
        );

        module.functions = final_functions;
        module
    }

    fn detect_monomorphizations_in(&mut self, mut function: IRFunction) -> IRFunction {
        for block in function.blocks.iter_mut() {
            for instruction in block.instructions.iter_mut() {
                if let Instr::Call {
                    callee: Callee::Name(callee),
                    args,
                    ty,
                    ..
                } = instruction
                {
                    let Some(callee_function) = self
                        .generic_functions
                        .iter()
                        .find(|f| f.name == *callee)
                        .cloned()
                    else {
                        log::error!("Did not find callee function: {}", callee);
                        return function;
                    };

                    if is_generic(&callee_function) {
                        let monomorphized_name = self.monomorphize_function(
                            &callee_function,
                            args.0.iter().map(|a| a.ty.clone()).collect(),
                            &ty,
                            &mut HashMap::new(),
                        );

                        *callee = monomorphized_name;
                    }
                }
            }
        }

        function
    }

    fn monomorphize_function(
        &mut self,
        function: &IRFunction,
        args: Vec<IRType>,
        expected_ret: &IRType,
        substitutions: &mut HashMap<IRType, IRType>,
    ) -> String {
        let mangled_name = self.mangle_name(&function.name, &args);

        if self.cache.contains(&mangled_name) {
            return mangled_name;
        }

        log::info!("monomorphizing: {} -> {:?}", mangled_name, expected_ret);

        let IRType::Func(params, ret) = &function.ty else {
            unreachable!()
        };

        substitutions.insert(*ret.clone(), expected_ret.clone());

        for (param, concrete_arg) in params.iter().zip(&args) {
            if contains_type_var(param) {
                substitutions.insert(param.clone(), concrete_arg.clone());
            }
        }

        let mut monomorphized_function = IRFunction {
            debug_info: Default::default(),
            name: mangled_name.clone(),
            ty: IRType::Func(
                params
                    .iter()
                    .map(|p| Self::apply_type(p, &substitutions))
                    .collect(),
                Self::apply_type(ret, &substitutions).into(),
            ),
            blocks: function
                .blocks
                .iter()
                .map(|block| self.apply_block(block, substitutions))
                .collect(),
            env_reg: function.env_reg,
            env_ty: function
                .env_ty
                .as_ref()
                .map(|ty| Self::apply_type(ty, &substitutions)),
            size: function.size,
        };

        monomorphized_function.ty = Self::apply_type(&monomorphized_function.ty, substitutions);

        log::info!(
            "monomorphized {} ({}): {:?}, {:#?}",
            mangled_name,
            is_generic(&monomorphized_function),
            Self::apply_type(monomorphized_function.ret(), &substitutions),
            substitutions
        );

        self.cache.insert(mangled_name.clone());
        self.generic_functions.push(monomorphized_function);

        mangled_name
    }

    fn apply_block(
        &mut self,
        block: &BasicBlock,
        substitutions: &mut HashMap<IRType, IRType>,
    ) -> BasicBlock {
        BasicBlock {
            id: block.id,
            instructions: block
                .instructions
                .iter()
                .map(|i| self.apply_instruction(i, substitutions))
                .collect(),
        }
    }

    fn apply_instruction(
        &mut self,
        instr: &Instr,
        substitutions: &mut HashMap<IRType, IRType>,
    ) -> Instr {
        let mut applied_instruction = instr.clone();
        match &mut applied_instruction {
            Instr::Add(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Sub(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Mul(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Div(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::StoreLocal(_, ty, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::LoadLocal(_, ty, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Phi(_, ty, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Ref(_, ty, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Eq(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Ne(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::LessThan(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::LessThanEq(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::GreaterThan(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::GreaterThanEq(_, ty, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Alloc { ty, .. } => *ty = Self::apply_type(ty, substitutions),
            Instr::Store { ty, .. } => *ty = Self::apply_type(ty, substitutions),
            Instr::Load { ty, .. } => *ty = Self::apply_type(ty, substitutions),
            Instr::GetElementPointer { ty, .. } => *ty = Self::apply_type(ty, substitutions),
            Instr::MakeStruct { ty, values, .. } => {
                *ty = Self::apply_type(ty, substitutions);
                *values = RegisterList(
                    values
                        .0
                        .iter()
                        .map(|v| {
                            TypedRegister::new(Self::apply_type(&v.ty, substitutions), v.register)
                        })
                        .collect(),
                );
            }
            Instr::GetValueOf { ty, .. } => *ty = Self::apply_type(ty, substitutions),
            Instr::Call {
                ty, args, callee, ..
            } => {
                let applied_args: Vec<TypedRegister> = args
                    .0
                    .iter()
                    .map(|a| TypedRegister::new(Self::apply_type(&a.ty, substitutions), a.register))
                    .collect();

                *ty = Self::apply_type(ty, substitutions);
                *args = RegisterList(applied_args.clone());

                // We want to monomorphize all the way down
                if let Callee::Name(name) = callee
                    && let Some(func) = self
                        .generic_functions
                        .iter()
                        .find(|f| f.name == *name)
                        .cloned()
                {
                    let new_callee = self.monomorphize_function(
                        &func,
                        applied_args.iter().map(|a| a.ty.clone()).collect(),
                        ty,
                        substitutions,
                    );

                    *callee = Callee::Name(new_callee);
                }
            }
            Instr::GetEnumTag(_, _) => todo!(),
            Instr::GetEnumValue(_, ty, _, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::TagVariant(_, ty, _, __list) => *ty = Self::apply_type(ty, substitutions),
            Instr::Ret(ty, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Jump(_) => (),
            Instr::Branch { .. } => (),
            Instr::Unreachable => (),
            Instr::ConstantInt(_, _) => (),
            Instr::ConstantFloat(_, _) => (),
            Instr::ConstantBool(_, _) => (),
        }

        applied_instruction
    }

    fn apply_type(ty: &IRType, substitutions: &HashMap<IRType, IRType>) -> IRType {
        match ty {
            IRType::TypeVar(_) => {
                log::debug!("substitute: {:?} -> {:?}", ty, substitutions.get(ty));
                substitutions.get(ty).cloned().unwrap_or(ty.clone())
            }
            IRType::Func(params, ret) => IRType::Func(
                params
                    .iter()
                    .map(|p| Self::apply_type(p, substitutions))
                    .collect(),
                Self::apply_type(ret, substitutions).into(),
            ),

            IRType::Enum(generics) => IRType::Enum(
                generics
                    .iter()
                    .map(|g| Self::apply_type(g, substitutions))
                    .collect(),
            ),
            IRType::Struct(symbol_id, properties, generics) => IRType::Struct(
                *symbol_id,
                properties.clone(),
                generics
                    .iter()
                    .map(|g| Self::apply_type(g, substitutions))
                    .collect(),
            ),
            IRType::Array { element } => IRType::Array {
                element: Self::apply_type(element, substitutions).clone().into(),
            },
            _ => ty.clone(),
        }
    }

    fn mangle_name(&self, callee_name: &str, args: &[IRType]) -> String {
        let mut mangled = String::new();
        mangled.push_str(callee_name);
        mangled.push('<');
        mangled.push_str(
            &args
                .iter()
                .map(|t| format!("{t}"))
                .collect::<Vec<String>>()
                .join(" "),
        );
        mangled.push('>');
        mangled
    }
}

fn is_generic(func: &IRFunction) -> bool {
    if let Some(env_ty) = &func.env_ty {
        contains_type_var(env_ty) || contains_type_var(&func.ty)
    } else {
        contains_type_var(&func.ty)
    }
}

fn contains_type_var(ty: &IRType) -> bool {
    match ty {
        IRType::TypeVar(_) => true,
        IRType::Func(params, ret) => params.iter().any(contains_type_var) || contains_type_var(ret),
        IRType::Struct(_, params, generics) => {
            params.iter().any(contains_type_var) || generics.iter().any(contains_type_var)
        }
        IRType::Enum(params) => params.iter().any(contains_type_var),
        IRType::Array { element } => contains_type_var(element),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        SymbolID, assert_lowered_function,
        compiling::driver::Driver,
        lowering::{
            instr::{Callee, Instr},
            ir_module::IRModule,
            ir_type::IRType,
            ir_value::IRValue,
            lowerer::{BasicBlock, BasicBlockID, IRFunction, RegisterList, TypedRegister},
            register::Register,
        },
        transforms::monomorphizer::Monomorphizer,
    };

    #[test]
    fn monomorphizes_generic_func() {
        let module = IRModule {
            functions: vec![
                IRFunction {
                    debug_info: Default::default(),
                    name: "@_3_identity".into(),
                    ty: IRType::Func(
                        vec![IRType::TypeVar("T1".into())],
                        IRType::TypeVar("T1".into()).into(),
                    ),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID::ENTRY,
                        instructions: vec![Instr::Ret(
                            IRType::TypeVar("T1".into()),
                            Some(IRValue::Register(Register(0))),
                        )],
                    }],
                    env_ty: None,
                    env_reg: None,
                    size: 0,
                },
                IRFunction {
                    debug_info: Default::default(),
                    name: "@main".into(),
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID::ENTRY,
                        instructions: vec![
                            Instr::ConstantInt(Register(1), 123),
                            Instr::Call {
                                dest_reg: Register(2),
                                ty: IRType::Int,
                                callee: Callee::Name("@_3_identity".into()),
                                args: RegisterList(vec![TypedRegister::new(
                                    IRType::Int,
                                    Register(1),
                                )]),
                            },
                        ],
                    }],
                    env_ty: None,
                    env_reg: None,
                    size: 0,
                },
            ],
        };

        let monomorphized = Monomorphizer::new().run(module);

        assert_lowered_function!(
            monomorphized,
            "@_3_identity<int>",
            IRFunction {
                debug_info: Default::default(),
                name: "@_3_identity<int>".into(),
                ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![Instr::Ret(
                        IRType::Int,
                        Some(IRValue::Register(Register(0))),
                    )],
                }],
                env_ty: None,
                env_reg: None,
                size: 0,
            }
        );

        assert_lowered_function!(
            monomorphized,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                name: "@main".into(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::Call {
                            dest_reg: Register(2),
                            ty: IRType::Int,
                            callee: Callee::Name("@_3_identity<int>".into()),
                            args: RegisterList(vec![TypedRegister::new(IRType::Int, Register(1),)]),
                        },
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 0,
            }
        )
    }

    #[test]
    fn monomorphs_array_get() {
        let mut driver = Driver::with_str(
            "
      let a = [1,2,3]
      a.get(0)
      ",
        );

        let module = driver.lower().into_iter().next().unwrap().module();
        let monomorphed = Monomorphizer::new().run(module);

        assert_lowered_function!(
            monomorphed,
            "@_Array_3_get<int>",
            IRFunction {
                debug_info: Default::default(),
                name: "@_Array_get<int>".into(),
                ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        // First alloc (so we can get a pointer)
                        Instr::ConstantInt(Register(1), 2),
                        Instr::Alloc {
                            dest: Register(0),
                            ty: IRType::Int,
                            count: Some(Register(1)),
                        },
                        Instr::ConstantInt(Register(3), 1),
                        Instr::GetElementPointer {
                            dest: Register(4),
                            base: Register(0),
                            ty: IRType::Array {
                                element: IRType::Int.into()
                            },
                            index: Register(3).into()
                        },
                        Instr::Load {
                            dest: Register(2),
                            ty: IRType::Int.into(),
                            addr: Register(4)
                        },
                        Instr::Ret(IRType::Int, Some(Register(2).into()))
                    ]
                }],
                env_ty: Some(IRType::Struct(
                    SymbolID::ARRAY,
                    vec![IRType::Int, IRType::Int, IRType::Pointer],
                    vec![IRType::Int]
                )),
                env_reg: Some(Register(0)),
                size: 0,
            }
        );
    }
}
