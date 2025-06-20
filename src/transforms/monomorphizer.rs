use std::collections::HashMap;

use crate::lowering::{
    instr::{Callee, Instr},
    ir_module::IRModule,
    ir_type::IRType,
    lowerer::IRFunction,
};

type InstantiationCache<'a> = HashMap<(String, Vec<&'a IRType>), String>;

pub struct Monomorphizer<'a> {
    cache: InstantiationCache<'a>,
    instantiated_functions: Vec<IRFunction>,
}

impl Monomorphizer<'_> {
    pub fn new() -> Self {
        Self {
            cache: Default::default(),
            instantiated_functions: Default::default(),
        }
    }

    pub fn run(mut self, module: IRModule) -> IRModule {
        let mut module = module;

        let (generic_templates, concrete_funcs): (Vec<_>, Vec<_>) =
            module.functions.into_iter().partition(|f| is_generic(f));

        // The generic functions will be used as templates for instantiation.
        self.instantiated_functions = generic_templates;

        // This will hold the final list of functions for our monomorphized module.
        let mut final_functions = Vec::new();

        // Process all the initially concrete functions.
        // This may trigger the creation of new, monomorphized functions, which will be
        // added to `self.instantiated_functions`.
        for func in concrete_funcs {
            final_functions.push(self.monomorphize_function(func));
        }

        // Now, `self.instantiated_functions` contains the original generic templates
        // plus all the new concrete functions we generated during the process.
        // We'll filter out the original templates and add the new concrete functions
        // to our final list.
        let instantiated_functions = self.instantiated_functions;
        final_functions.extend(
            instantiated_functions
                .into_iter()
                .filter(|f| !is_generic(f)),
        );

        module.functions = final_functions;
        module
    }

    fn monomorphize_function(&mut self, mut function: IRFunction) -> IRFunction {
        for block in function.blocks.iter_mut() {
            for instruction in block.instructions.iter_mut() {
                if let Instr::Call {
                    ty: IRType::Func(params, ret),
                    callee: Callee::Name(callee),
                    ..
                } = instruction
                {
                    let mut type_vars: Vec<&IRType> =
                        params.iter().filter(|p| contains_type_var(&p)).collect();
                    if contains_type_var(&ret) {
                        type_vars.push(ret);
                    }

                    if type_vars.is_empty() {
                        continue;
                    }

                    let mangled_name = self.instantiate_if_needed(&callee, &type_vars);
                    *callee = mangled_name.into();
                }
            }
        }
        function
    }

    // This is the core logic: create a new monomorphized function if we haven't already.
    fn instantiate_if_needed(&mut self, callee_name: &str, type_args: &[&IRType]) -> String {
        let key = (callee_name.to_string(), type_args.to_vec());
        if let Some(mangled_name) = self.cache.get(&key) {
            return mangled_name.clone();
        }

        // Find the generic function template.
        let generic_func = self
            .instantiated_functions
            .iter()
            .find(|f| f.name == callee_name)
            .expect("Cannot find generic function to instantiate.")
            .clone();

        // Create a substitution map from generic parameters to concrete types.
        let mut substitution = HashMap::new();
        if let IRType::Func(_, _) = &generic_func.ty {
            for (param, arg) in generics.iter().zip(type_args.iter()) {
                if let IRType::TypeVar(tv) = param {
                    substitution.insert(tv.clone(), arg.clone());
                }
            }
        }

        let mangled_name = self.mangle_name(callee_name, type_args);

        let mut new_func = generic_func.clone();
        new_func.name = mangled_name.clone();
        new_func.ty = self.substitute_type(&new_func.ty, &substitution);

        for instr in new_func.instructions.iter_mut() {
            self.substitute_instr(instr, &substitution);
        }

        self.cache.insert(key, mangled_name.clone());
        self.instantiated_functions.push(new_func);

        mangled_name
    }

    fn substitute_instr(&self, instr: &mut Instr, substitution: &HashMap<String, IRType>) {
        match instr {
            Instr::Alloc { ty, .. } => *ty = self.substitute_type(ty, substitution),
            Instr::Add(.., ty, _, _)
            | Instr::Sub(.., ty, _, _)
            | Instr::Mul(.., ty, _, _)
            | Instr::Div(.., ty, _, _) => *ty = self.substitute_type(ty, substitution),
            // and so on for all instructions that have a type.
            _ => {}
        }
    }

    fn substitute_type(&self, ty: &IRType, substitution: &HashMap<String, IRType>) -> IRType {
        match ty {
            IRType::TypeVar(tv) => substitution.get(tv).cloned().unwrap_or_else(|| ty.clone()),
            IRType::Func(params, ret) => IRType::Func(
                params
                    .iter()
                    .map(|p| self.substitute_type(p, substitution))
                    .collect(),
                Box::new(self.substitute_type(ret, substitution)),
            ),
            IRType::Struct(id, params) => IRType::Struct(
                *id,
                params
                    .iter()
                    .map(|p| self.substitute_type(p, substitution))
                    .collect(),
            ),
            IRType::Enum(params) => IRType::Enum(
                params
                    .iter()
                    .map(|p| self.substitute_type(p, substitution))
                    .collect(),
            ),
            IRType::Array { element } => IRType::Array {
                element: Box::new(self.substitute_type(element, substitution)),
            },
            _ => ty.clone(),
        }
    }

    fn mangle_name(&self, callee_name: &str, type_args: &[&IRType]) -> String {
        let mut mangled = String::new();
        mangled.push_str(callee_name);
        mangled.push('<');
        mangled.push_str(
            &type_args
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
    use std::path::PathBuf;

    use crate::{
        assert_lowered_function,
        compiling::driver::{Driver, DriverConfig},
        lowering::{
            instr::{Callee, Instr},
            ir_error::IRError,
            ir_module::IRModule,
            ir_type::IRType,
            ir_value::IRValue,
            lowerer::{BasicBlock, BasicBlockID, IRFunction, RegisterList},
            register::Register,
        },
        transforms::monomorphizer::Monomorphizer,
    };

    fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let mut driver = Driver::new(DriverConfig {
            executable: true,
            include_prelude: false,
        });
        driver.update_file(&PathBuf::from("-"), input.into());
        let lowered = driver.lower().into_iter().next().unwrap();
        let diagnostics = lowered.source_file(&"-".into()).unwrap().diagnostics();
        let module = lowered.module().clone();

        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        Ok(module)
    }

    #[test]
    fn monomorphizes_generic_func() {
        let lowered = lower(
            "
        func identity(x) { x }
        identity(123)
        identity(45.6)
        ",
        )
        .unwrap();

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
                            IRType::TypeVar("1".into()),
                            Some(IRValue::Register(Register(0))),
                        )],
                    }],
                    env_ty: IRType::closure(),
                    env_reg: Register(0),
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
                                ty: IRType::Func(
                                    vec![IRType::TypeVar("T1".into())],
                                    IRType::TypeVar("T1".into()).into(),
                                ),
                                callee: Callee::Name("@_123_identity".into()),
                                args: RegisterList(vec![Register(1)]),
                            },
                        ],
                    }],
                    env_ty: IRType::closure(),
                    env_reg: Register(0),
                },
            ],
        };

        let monomorphized = Monomorphizer::new().run(module);

        assert_lowered_function!(
            monomorphized,
            "@_123_identity<Int>",
            IRFunction {
                name: "@_123_identity<Int>".into(),
                ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![Instr::Ret(
                        IRType::Int,
                        Some(IRValue::Register(Register(0))),
                    )],
                }],
                env_ty: IRType::closure(),
                env_reg: Register(0)
            }
        )
    }
}
