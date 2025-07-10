use std::collections::{HashMap, HashSet};

use crate::{
    environment::Environment,
    lowering::{
        instr::{Callee, Instr},
        ir_function::IRFunction,
        ir_module::IRModule,
        ir_type::IRType,
        lowerer::{BasicBlock, RefKind, RegisterList, TypedRegister},
    },
    type_defs::TypeDef,
};

// The Monomorphizer monomorphizes. So it takes a func like this:
//
//     func identity(x) { x }
//
// which lowers to (T1) -> T1. And then given a call like this:
//
//     identity(123)
//
// and it'll generate a version of identity that lowers to (Int) -> Int.
// It'll also update calls to the generic form to the specialized form.
pub struct Monomorphizer<'a> {
    env: &'a Environment,
    cache: HashSet<String>,
    generic_functions: Vec<IRFunction>,
    currently_monomorphizing_stack: Vec<String>,
}

impl<'a> Monomorphizer<'a> {
    pub fn new(env: &'a Environment) -> Self {
        Self {
            env,
            cache: Default::default(),
            generic_functions: Default::default(),
            currently_monomorphizing_stack: Default::default(),
        }
    }

    pub fn run(mut self, mut module: IRModule) -> IRModule {
        let mut concrete_funcs = vec![];
        // self.module.functions.iter().partition(|f|Self::is_generic(f));
        for func in module.functions.iter().cloned() {
            if Self::is_generic(&func) || func.blocks.is_empty() {
                self.generic_functions.push(func)
            } else {
                concrete_funcs.push(func)
            }
        }

        let mut final_functions = Vec::new();

        for func in concrete_funcs {
            let func = self.detect_monomorphizations_in(func, &module, &mut HashMap::default());
            final_functions.push(func);
        }
        // Keep any specialized functions even if they still contain type
        // variables. Recursively monomorphized functions may reference their own
        // return type before constraints fully resolve, so filtering them out
        // would drop required definitions.
        // TODO: ideally we wouldn't need this.
        final_functions.extend(self.generic_functions.into_iter());

        module.functions = final_functions;
        module
    }

    fn detect_monomorphizations_in(
        &mut self,
        mut function: IRFunction,
        module: &IRModule,
        substitutions: &mut HashMap<IRType, IRType>,
    ) -> IRFunction {
        tracing::trace!(
            "Detecting monomorphization opportunities in {:?}",
            function.name
        );
        let mut renames = HashMap::new();

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
                        continue;
                    };

                    if Some(&*callee) == self.currently_monomorphizing_stack.last() {
                        continue;
                    }

                    if callee_function.blocks.is_empty()
                        && let Some(first_arg) = &args.0.first()
                    {
                        // it's a protocol method, we need to specialize it
                        tracing::info!("Detected protocol method, specializing: {args:?}");
                        let Some(concrete) =
                            Self::find_concrete_type(first_arg, substitutions, self.env)
                        else {
                            continue;
                        };

                        let name_parts = callee.clone();
                        let Some(member_name) = name_parts.split("_").nth(3) else {
                            continue;
                        };

                        let monomorphized_name = format!(
                            "@_{}_{}_{}",
                            concrete.symbol_id().0,
                            concrete.name(),
                            member_name
                        );

                        renames.insert(callee.clone(), monomorphized_name.clone());

                        let Some(callee_function) =
                            module.functions.iter().find(|f| &f.name == callee).cloned()
                        else {
                            continue;
                        };

                        self.detect_monomorphizations_in(callee_function, module, substitutions);
                    } else if Self::is_generic(&callee_function) {
                        let monomorphized_name = self.monomorphize_function(
                            &callee_function,
                            args.0.iter().map(|a| a.ty.clone()).collect(),
                            ty,
                            substitutions,
                            module,
                        );

                        *callee = monomorphized_name.clone();
                        renames.insert(callee.clone(), monomorphized_name.clone());
                    }
                }
            }
        }

        // Replace polymorphic func names with new monomorphized ones
        for block in function.blocks.iter_mut() {
            for instruction in block.instructions.iter_mut() {
                match instruction {
                    Instr::Call {
                        callee: Callee::Name(name),
                        ..
                    } => {
                        if let Some(new_name) = renames.get(name) {
                            *name = new_name.clone()
                        }
                    }
                    Instr::Ref(_, _, RefKind::Func(name)) => {
                        if let Some(new_name) = renames.get(name) {
                            *name = new_name.clone()
                        }
                    }
                    _ => (),
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
        module: &IRModule,
    ) -> String {
        let mangled_name = self.mangle_name(&function.name, &args);

        if self.cache.contains(&mangled_name) {
            return mangled_name;
        }

        self.currently_monomorphizing_stack
            .push(function.name.clone());

        tracing::info!("monomorphizing: {mangled_name} -> {expected_ret:?} {substitutions:?}");

        let IRType::Func(params, ret) = &function.ty else {
            unreachable!()
        };

        if !contains_type_var(expected_ret) {
            substitutions.insert(*ret.clone(), expected_ret.clone());
        }

        for (param, concrete_arg) in params.iter().zip(&args) {
            if contains_type_var(param) && !contains_type_var(concrete_arg) {
                substitutions.insert(param.clone(), concrete_arg.clone());
            }
        }

        let mut monomorphized_function =
            self.apply_function(&mangled_name, params, ret, function, substitutions, module);

        monomorphized_function.ty = Self::apply_type(&monomorphized_function.ty, substitutions);

        tracing::info!(
            "monomorphized {} ({}): {:?}, {:#?}",
            mangled_name,
            Self::is_generic(&monomorphized_function),
            Self::apply_type(monomorphized_function.ret(), substitutions),
            substitutions
        );

        let is_generic = Self::is_generic(&monomorphized_function);
        if !is_generic {
            self.cache.insert(mangled_name.clone());
        }

        monomorphized_function =
            self.detect_monomorphizations_in(monomorphized_function.clone(), module, substitutions);
        self.generic_functions.push(monomorphized_function);

        self.currently_monomorphizing_stack.pop();

        mangled_name
    }

    fn apply_function(
        &mut self,
        mangled_name: &str,
        params: &[IRType],
        ret: &IRType,
        function: &IRFunction,
        substitutions: &mut HashMap<IRType, IRType>,
        module: &IRModule,
    ) -> IRFunction {
        IRFunction {
            debug_info: Default::default(),
            name: mangled_name.to_string(),
            ty: IRType::Func(
                params
                    .iter()
                    .map(|p| Self::apply_type(p, substitutions))
                    .collect(),
                Self::apply_type(ret, substitutions).into(),
            ),
            blocks: function
                .blocks
                .iter()
                .map(|block| self.apply_block(block, substitutions, module))
                .collect(),
            env_reg: function.env_reg,
            env_ty: function
                .env_ty
                .as_ref()
                .map(|ty| Self::apply_type(ty, substitutions)),
            size: function.size,
        }
    }

    fn apply_block(
        &mut self,
        block: &BasicBlock,
        substitutions: &mut HashMap<IRType, IRType>,
        module: &IRModule,
    ) -> BasicBlock {
        BasicBlock {
            id: block.id,
            instructions: block
                .instructions
                .iter()
                .map(|i| self.apply_instruction(i, substitutions, module))
                .collect(),
        }
    }

    fn apply_instruction(
        &mut self,
        instr: &Instr,
        substitutions: &mut HashMap<IRType, IRType>,
        module: &IRModule,
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
            Instr::Const { ty, .. } => *ty = Self::apply_type(ty, substitutions),
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
            Instr::Call { callee, .. } => {
                // We want to monomorphize all the way down
                if let Callee::Name(name) = callee
                    && let Some(func) = self
                        .generic_functions
                        .iter()
                        .find(|f| f.name == *name)
                        .cloned()
                    && Some(name) != self.currently_monomorphizing_stack.last_mut()
                {
                    let name = self
                        .detect_monomorphizations_in(func, module, substitutions)
                        .name
                        .clone();
                    *callee = Callee::Name(name);
                }
            }
            Instr::GetEnumTag(_, _) => (),
            Instr::GetEnumValue(_, ty, _, _, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::TagVariant(_, ty, _, __list) => *ty = Self::apply_type(ty, substitutions),
            Instr::Ret(ty, _) => *ty = Self::apply_type(ty, substitutions),
            Instr::Print { .. } => (),
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
            IRType::TypeVar(_) => substitutions.get(ty).cloned().unwrap_or(ty.clone()),
            IRType::Func(params, ret) => IRType::Func(
                params
                    .iter()
                    .map(|p| Self::apply_type(p, substitutions))
                    .collect(),
                Self::apply_type(ret, substitutions).into(),
            ),

            IRType::Enum(enum_id, generics) => IRType::Enum(
                *enum_id,
                generics
                    .iter()
                    .map(|g| Self::apply_type(g, substitutions))
                    .collect(),
            ),
            IRType::Struct(symbol_id, properties, generics) => IRType::Struct(
                *symbol_id,
                properties
                    .iter()
                    .map(|g| Self::apply_type(g, substitutions))
                    .collect(),
                generics
                    .iter()
                    .map(|g| Self::apply_type(g, substitutions))
                    .collect(),
            ),
            IRType::TypedBuffer { element } => IRType::TypedBuffer {
                element: Self::apply_type(element, substitutions).clone().into(),
            },
            _ => ty.clone(),
        }
    }

    fn find_concrete_type(
        name: &TypedRegister,
        substitutions: &HashMap<IRType, IRType>,
        env: &'a Environment,
    ) -> Option<&'a TypeDef> {
        if let IRType::Struct(type_id, _, _) | IRType::Enum(type_id, _) =
            substitutions.get(&name.ty).unwrap_or(&name.ty)
        {
            return env.lookup_type(type_id);
        }

        if let IRType::Pointer { hint: Some(hint) } =
            substitutions.get(&name.ty).unwrap_or(&name.ty)
        {
            let type_var = IRType::TypeVar(hint.to_string());
            let replaced = substitutions.get(&type_var)?;

            if let IRType::Struct(type_id, _, _) | IRType::Enum(type_id, _) = replaced {
                return env.lookup_type(type_id);
            }
        }

        None
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

    fn is_generic(func: &IRFunction) -> bool {
        if let Some(env_ty) = &func.env_ty {
            contains_type_var(env_ty) || contains_type_var(&func.ty)
        } else {
            contains_type_var(&func.ty)
        }
    }
}

fn contains_type_var(ty: &IRType) -> bool {
    match ty {
        IRType::TypeVar(_) => true,
        IRType::Func(params, ret) => params.iter().any(contains_type_var) || contains_type_var(ret),
        IRType::Struct(_, params, generics) => {
            params.iter().any(contains_type_var) || generics.iter().any(contains_type_var)
        }
        IRType::Enum(_, params) => params.iter().any(contains_type_var),
        IRType::TypedBuffer { element } => contains_type_var(element),
        IRType::Pointer { hint } => hint.is_some(),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        SymbolID, assert_lowered_function,
        compiling::driver::Driver,
        environment::Environment,
        lowering::{
            instr::{Callee, Instr},
            ir_function::IRFunction,
            ir_module::IRModule,
            ir_type::IRType,
            ir_value::IRValue,
            lowerer::{BasicBlock, BasicBlockID, RefKind, RegisterList, TypedRegister},
            lowerer_tests::helpers::lower_without_prelude_with_env,
            register::Register,
        },
        transforms::monomorphizer::Monomorphizer,
    };

    #[test]
    fn monomorphizes_generic_func() {
        let module = IRModule {
            constants: vec![],
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

        let monomorphized = Monomorphizer::new(&Environment::default()).run(module);

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
        let monomorphed = Monomorphizer::new(&Environment::default()).run(module);

        assert_lowered_function!(
            monomorphed,
            format!("@_{}_Array_get<ptr int>", SymbolID::ARRAY.0),
            IRFunction {
                debug_info: Default::default(),
                name: format!("@_{}_Array_get<ptr int>", SymbolID::ARRAY.0),
                ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::GetElementPointer {
                            dest: Register(3),
                            base: Register(0),
                            ty: IRType::array(IRType::Int),
                            index: IRValue::ImmediateInt(2)
                        },
                        Instr::Load {
                            dest: Register(4),
                            ty: IRType::POINTER,
                            addr: Register(3)
                        },
                        Instr::GetElementPointer {
                            dest: Register(5),
                            base: Register(4),
                            ty: IRType::TypedBuffer {
                                element: IRType::Int.into()
                            },
                            index: IRValue::Register(Register(1))
                        },
                        Instr::Load {
                            dest: Register(2),
                            ty: IRType::Int,
                            addr: Register(5)
                        },
                        Instr::Ret(IRType::Int, Some(Register(2).into()))
                    ]
                }],
                env_ty: Some(IRType::array(IRType::Int)),
                env_reg: Some(Register(0)),
                size: 6,
            }
        );
    }

    #[test]
    fn monomorphs_protocol_functions() {
        let (lowered, env) = lower_without_prelude_with_env(
            "
            protocol Aged {
                func getAge() -> Int
            }

            struct Person: Aged {
                func getAge() {
                    123
                }
            }

            struct Cat: Aged {
                func getAge() {
                    123
                }
            }

            func get<T: Aged>(t: T) {
                t.getAge()
            }

            get(Person())
            get(Cat())
        ",
        )
        .unwrap();

        let mono = Monomorphizer::new(&env).run(lowered);

        let person_struct = IRType::Struct(SymbolID(4), vec![], vec![]);
        let cat_struct = IRType::Struct(SymbolID(6), vec![], vec![]);

        assert_lowered_function!(
            mono,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![
                        Instr::Ref(
                            Register(0),
                            IRType::Func(vec![IRType::TypeVar("T12".into())], IRType::Int.into()),
                            RefKind::Func("@_3_get".into())
                        ),
                        Instr::Alloc {
                            dest: Register(1),
                            ty: person_struct.clone(),
                            count: None
                        },
                        Instr::Call {
                            dest_reg: Register(2),
                            ty: person_struct.clone(),
                            callee: Callee::Name("@_4_Person_init".into()),
                            args: RegisterList(vec![TypedRegister::new(
                                IRType::POINTER,
                                Register(1)
                            )])
                        },
                        Instr::Call {
                            dest_reg: Register(3),
                            ty: IRType::Int,
                            callee: Callee::Name("@_3_get<@4{}>".into()),
                            args: RegisterList(vec![TypedRegister::new(
                                person_struct.clone(),
                                Register(1)
                            )])
                        },
                        Instr::Alloc {
                            dest: Register(4),
                            ty: cat_struct.clone(),
                            count: None
                        },
                        Instr::Call {
                            dest_reg: Register(5),
                            ty: cat_struct.clone(),
                            callee: Callee::Name("@_6_Cat_init".into()),
                            args: RegisterList(vec![TypedRegister::new(
                                IRType::POINTER,
                                Register(4)
                            )])
                        },
                        Instr::Call {
                            dest_reg: Register(6),
                            ty: IRType::Int,
                            callee: Callee::Name("@_3_get<@6{}>".into()),
                            args: RegisterList(vec![TypedRegister::new(
                                cat_struct.clone(),
                                Register(4)
                            )])
                        },
                        Instr::Ret(IRType::Int, Some(IRValue::Register(Register(6))))
                    ]
                }],
                env_ty: None,
                env_reg: None,
                size: 7,
            }
        );

        assert_lowered_function!(
            mono,
            "@_3_get<@4{}>",
            IRFunction {
                ty: IRType::Func(vec![person_struct.clone()], IRType::Int.into()),
                name: "@_3_get<@4{}>".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![
                        Instr::Call {
                            dest_reg: Register(1),
                            ty: IRType::Int,
                            callee: Callee::Name("@_4_Person_getAge".into()),
                            args: RegisterList(vec![TypedRegister::new(
                                IRType::Pointer {
                                    hint: Some("T12".into())
                                },
                                Register(0)
                            )])
                        },
                        Instr::Ret(IRType::Int, Some(IRValue::Register(Register(1))))
                    ]
                }],
                env_ty: None,
                env_reg: None,
                size: 2,
                debug_info: Default::default()
            }
        )
    }

    #[test]
    fn handles_more_recursion() {
        let mut driver = Driver::with_str(
            "
         func fib(n) {
                if n <= 1 { return n }

                return fib(n - 2) + fib(n - 1)
            }

            let i = 0

            // Calculate some numbers
            loop i < 15 {
                print(fib(i))
                i = i + 1
            }
      ",
        );

        let module = driver.lower().into_iter().next().unwrap().module();
        Monomorphizer::new(&Environment::default()).run(module);
    }

    #[test]
    fn handles_recursion() {
        let (lowered, env) = lower_without_prelude_with_env(
            "
            func rec(x, y) {
                if x == y { x } else { rec(x-y, y) }
            }

            rec(0, 2)
            rec(0.0, 2.0)
        ",
        )
        .unwrap();

        let mono = Monomorphizer::new(&env).run(lowered);
        let t3 = IRType::TypeVar("T9".to_string());

        assert_lowered_function!(
            mono,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![
                        Instr::Ref(
                            Register(0),
                            IRType::Func(vec![t3.clone(), t3.clone()], t3.clone().into()),
                            RefKind::Func("@_1_rec".into())
                        ),
                        Instr::ConstantInt(Register(1), 0),
                        Instr::ConstantInt(Register(2), 2),
                        Instr::Call {
                            dest_reg: Register(3),
                            ty: IRType::Int,
                            callee: Callee::Name("@_1_rec<int int>".into()),
                            args: RegisterList(vec![
                                TypedRegister::new(IRType::Int, Register(1)),
                                TypedRegister::new(IRType::Int, Register(2))
                            ])
                        },
                        Instr::ConstantFloat(Register(4), 0.),
                        Instr::ConstantFloat(Register(5), 2.),
                        Instr::Call {
                            dest_reg: Register(6),
                            ty: IRType::Float,
                            callee: Callee::Name("@_1_rec<float float>".into()),
                            args: RegisterList(vec![
                                TypedRegister::new(IRType::Float, Register(4)),
                                TypedRegister::new(IRType::Float, Register(5))
                            ])
                        },
                        Instr::Ret(IRType::Float, Some(IRValue::Register(Register(6))))
                    ]
                }],
                env_ty: None,
                env_reg: None,
                size: 7,
            }
        );

        // assert_lowered_function!(
        //     mono,
        //     "@_3_get<@4{}>",
        //     IRFunction {
        //         ty: IRType::Func(vec![person_struct.clone()], IRType::Int.into()),
        //         name: "@_3_get<@4{}>".into(),
        //         blocks: vec![BasicBlock {
        //             id: BasicBlockID::ENTRY,
        //             instructions: vec![
        //                 Instr::Call {
        //                     dest_reg: Register(1),
        //                     ty: IRType::Int,
        //                     callee: Callee::Name("@_4_Person_getAge".into()),
        //                     args: RegisterList(vec![TypedRegister::new(
        //                         IRType::Pointer {
        //                             hint: Some("T7".into())
        //                         },
        //                         Register(0)
        //                     )])
        //                 },
        //                 Instr::Ret(IRType::Int, Some(IRValue::Register(Register(1))))
        //             ]
        //         }],
        //         env_ty: None,
        //         env_reg: None,
        //         size: 2,
        //         debug_info: Default::default()
        //     }
        // )
    }
}
