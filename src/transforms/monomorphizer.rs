use std::collections::{HashMap, HashSet};

use async_lsp::lsp_types::request::Formatting;

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
            module.functions.into_iter().partition(is_generic);

        self.generic_functions = generic_templates;

        let mut final_functions = Vec::new();

        for func in concrete_funcs {
            final_functions.push(self.detect_monomorphizations_in(func));
        }

        let instantiated_functions = self.generic_functions;
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
                    ..
                } = instruction
                {
                    let Some(callee_function) = self
                        .generic_functions
                        .iter()
                        .find(|f| f.name == *callee)
                        .cloned()
                    else {
                        log::error!("Did not find callee function");
                        return function;
                    };

                    if contains_type_var(&callee_function.ty) {
                        let monomorphized_name = self.monomorphize_function(
                            &callee_function,
                            args.0.iter().map(|a| a.ty.clone()).collect(),
                        );

                        *callee = monomorphized_name;
                    }
                }
            }
        }

        function
    }

    fn monomorphize_function(&mut self, function: &IRFunction, args: Vec<IRType>) -> String {
        let mangled_name = self.mangle_name(&function.name, &args);

        if self.cache.contains(&mangled_name) {
            return mangled_name;
        }

        log::info!("monomorphizing {mangled_name}");

        let IRType::Func(params, ret) = &function.ty else {
            unreachable!()
        };

        let mut substitutions = HashMap::new();
        for (param, concrete_arg) in params.into_iter().zip(&args) {
            if contains_type_var(param) {
                substitutions.insert(param.clone(), concrete_arg.clone());
            }
        }

        let monomorphized_function = IRFunction {
            name: mangled_name.clone(),
            ty: IRType::Func(
                params
                    .iter()
                    .map(|p| self.apply_type(p, &substitutions))
                    .collect(),
                self.apply_type(ret, &substitutions).into(),
            ),
            blocks: function
                .blocks
                .iter()
                .map(|block| self.apply_block(block, &substitutions))
                .collect(),
            env_reg: function.env_reg,
            env_ty: function
                .env_ty
                .as_ref()
                .map(|ty| self.apply_type(ty, &substitutions)),
        };

        self.cache.insert(mangled_name.clone());
        self.generic_functions.push(monomorphized_function);

        return mangled_name;
    }

    fn apply_block(
        &mut self,
        block: &BasicBlock,
        substitutions: &HashMap<IRType, IRType>,
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

    fn apply_instruction(&mut self, instr: &Instr, substitutions: &HashMap<IRType, IRType>) -> Instr {
        let mut applied_instruction = instr.clone();
        match &mut applied_instruction {
            Instr::Add(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::Sub(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::Mul(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::Div(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::StoreLocal(_, ty, _1) => *ty = self.apply_type(ty, substitutions),
            Instr::LoadLocal(_, ty, _1) => *ty = self.apply_type(ty, substitutions),
            Instr::Phi(_, ty, _) => *ty = self.apply_type(ty, substitutions),
            Instr::Ref(_, ty, _) => *ty = self.apply_type(ty, substitutions),
            Instr::Eq(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::Ne(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::LessThan(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::LessThanEq(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::GreaterThan(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::GreaterThanEq(_, ty, _1, _2) => *ty = self.apply_type(ty, substitutions),
            Instr::Alloc { ty, .. } => *ty = self.apply_type(ty, substitutions),
            Instr::Store { ty, .. } => *ty = self.apply_type(ty, substitutions),
            Instr::Load { ty, .. } => *ty = self.apply_type(ty, substitutions),
            Instr::GetElementPointer { ty, .. } => *ty = self.apply_type(ty, substitutions),
            Instr::MakeStruct { ty, values, .. } => {
                *ty = self.apply_type(ty, substitutions);
                *values = RegisterList(
                    values
                        .0
                        .iter()
                        .map(|v| {
                            TypedRegister::new(self.apply_type(&v.ty, substitutions), v.register)
                        })
                        .collect(),
                );
            }
            Instr::GetValueOf { ty, .. } => *ty = self.apply_type(ty, substitutions),
            Instr::Call {
                ty, args, callee, ..
            } => {
                let applied_args: Vec<TypedRegister> = args
                    .0
                    .iter()
                    .map(|a| TypedRegister::new(self.apply_type(&a.ty, substitutions), a.register))
                    .collect();

                *ty = self.apply_type(ty, substitutions);
                *args = RegisterList(applied_args.clone());

                // We want to monomorphize all the way down
                if let Callee::Name(name) = callee
                    && let Some(func) = self.generic_functions.iter().find(|f| f.name == *name).cloned()
                {
                    self.detect_monomorphizations_in(
                        func,
                    );
                }
            }
            Instr::GetEnumTag(_, _1) => todo!(),
            Instr::GetEnumValue(_, ty, _1, _, _) => *ty = self.apply_type(ty, substitutions),
            Instr::TagVariant(_, ty, _, __list) => *ty = self.apply_type(ty, substitutions),
            Instr::Ret(ty, _) => *ty = self.apply_type(ty, substitutions),
            Instr::Jump(_) => (),
            Instr::Branch { .. } => (),
            Instr::Unreachable => (),
            Instr::ConstantInt(_, _) => (),
            Instr::ConstantFloat(_, _) => (),
            Instr::ConstantBool(_, _) => (),
        }

        applied_instruction
    }

    fn apply_type(&self, ty: &IRType, substitutions: &HashMap<IRType, IRType>) -> IRType {
        match ty {
            IRType::TypeVar(_) => substitutions.get(ty).cloned().unwrap_or(ty.clone()),
            IRType::Func(params, ret) => IRType::Func(
                params
                    .into_iter()
                    .map(|p| self.apply_type(p, substitutions))
                    .collect(),
                self.apply_type(ret, substitutions).into(),
            ),

            IRType::Enum(generics) => IRType::Enum(
                generics
                    .into_iter()
                    .map(|g| self.apply_type(g, substitutions))
                    .collect(),
            ),
            IRType::Struct(symbol_id, generics) => IRType::Struct(
                *symbol_id,
                generics
                    .into_iter()
                    .map(|g| self.apply_type(g, substitutions))
                    .collect(),
            ),
            IRType::Array { element } => IRType::Array {
                element: self.apply_type(element, substitutions).clone().into(),
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
                .into_iter()
                .map(|t| format!("{t}"))
                .collect::<Vec<String>>()
                .join(" "),
        );
        mangled.push('>');
        mangled
    }
}

fn is_generic(func: &IRFunction) -> bool {
    contains_type_var(&func.ty)
}

fn contains_type_var(ty: &IRType) -> bool {
    match ty {
        IRType::TypeVar(_) => true,
        IRType::Func(params, ret) => params.iter().any(contains_type_var) || contains_type_var(ret),
        IRType::Struct(_, params) | IRType::Enum(params) => params.iter().any(contains_type_var),
        IRType::Array { element } => contains_type_var(element),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        assert_lowered_function,
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
                    name: "@_123_identity".into(),
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
                },
                IRFunction {
                    name: "@main".into(),
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID::ENTRY,
                        instructions: vec![
                            Instr::ConstantInt(Register(1), 123),
                            Instr::Call {
                                dest_reg: Register(2),
                                ty: IRType::Int,
                                callee: Callee::Name("@_123_identity".into()),
                                args: RegisterList(vec![TypedRegister::new(
                                    IRType::Int,
                                    Register(1),
                                )]),
                            },
                        ],
                    }],
                    env_ty: None,
                    env_reg: None,
                },
            ],
        };

        let monomorphized = Monomorphizer::new().run(module);

        assert_lowered_function!(
            monomorphized,
            "@_123_identity<int>",
            IRFunction {
                name: "@_123_identity<int>".into(),
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
            }
        );

        assert_lowered_function!(
            monomorphized,
            "@main",
            IRFunction {
                name: "@main".into(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::Call {
                            dest_reg: Register(2),
                            ty: IRType::Int,
                            callee: Callee::Name("@_123_identity<int>".into()),
                            args: RegisterList(vec![TypedRegister::new(IRType::Int, Register(1),)]),
                        },
                    ],
                }],
                env_ty: None,
                env_reg: None,
            }
        )
    }
}
