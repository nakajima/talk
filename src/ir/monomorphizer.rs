use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    compiling::driver::DriverConfig,
    ir::{
        basic_block::{BasicBlock, Phi},
        function::Function,
        instruction::{Instruction, InstructionMeta},
        ir_ty::IrTy,
        lowerer::PolyFunction,
        terminator::Terminator,
        value::{Reference, Value},
    },
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        conformance::ConformanceKey,
        passes::specialization_pass::SpecializedCallee,
        ty::{Specializations, Ty},
        types::Types,
    },
};

pub struct Monomorphizer<'a> {
    types: &'a Types,
    config: &'a DriverConfig,
    pub(super) functions: IndexMap<Symbol, PolyFunction>,
    specializations: &'a FxHashMap<Symbol, Vec<Symbol>>,
    specialized_callees: &'a FxHashMap<Symbol, SpecializedCallee>,
    /// Maps (specialized_caller, call_site_id) -> specialized_callee.
    /// Aligns with the paper's model: each call site is a dimension, resolution maps to the callee.
    call_resolutions: &'a FxHashMap<(Symbol, NodeID), Symbol>,
}

#[allow(clippy::expect_used)]
impl<'a> Monomorphizer<'a> {
    pub fn new(
        types: &'a Types,
        functions: IndexMap<Symbol, PolyFunction>,
        config: &'a DriverConfig,
        specializations: &'a FxHashMap<Symbol, Vec<Symbol>>,
        specialized_callees: &'a FxHashMap<Symbol, SpecializedCallee>,
        call_resolutions: &'a FxHashMap<(Symbol, NodeID), Symbol>,
    ) -> Self {
        Monomorphizer {
            types,
            functions,
            config,
            specializations,
            specialized_callees,
            call_resolutions,
        }
    }

    #[instrument(skip(self))]
    pub fn monomorphize(&mut self) -> IndexMap<Symbol, Function<IrTy>> {
        let mut result = IndexMap::<Symbol, Function<IrTy>>::default();
        let functions = self.functions.clone();
        for func in functions.into_values() {
            self.monomorphize_func(func, &mut result);
        }

        // Ensure all external callees referenced by monomorphized functions are imported.
        let mut checked = IndexSet::default();
        let syms: Vec<Symbol> = result.keys().copied().collect();
        for sym in syms {
            self.check_imports(&sym, &mut result, &mut checked);
        }

        result
    }

    fn check_imports(
        &mut self,
        sym: &Symbol,
        result: &mut IndexMap<Symbol, Function<IrTy>>,
        checked: &mut IndexSet<Symbol>,
    ) {
        if !checked.insert(*sym) {
            return; // Already checked
        }
        let mut callees: IndexSet<&Symbol> = IndexSet::default();
        let Some(func) = result.get(sym).cloned() else {
            return;
        };
        for block in func.blocks.iter() {
            for instruction in block.instructions.iter() {
                if let Instruction::Call {
                    callee:
                        Value::Func(sym)
                        | Value::Ref(Reference::Func(sym))
                        | Value::Ref(Reference::Closure(sym, ..)),
                    ..
                } = instruction
                {
                    callees.insert(sym);
                }
            }
        }

        for callee in callees {
            // Check if this is a synthesized callee pointing to an external function
            if let Some(specialized_callee) = self.specialized_callees.get(callee).cloned() {
                let original = specialized_callee.original_symbol;
                if let Some(module_id) = original.module_id()
                    && module_id != self.config.module_id
                    && let Some(program) = self.config.modules.program_for(module_id)
                    && let Some(poly_func) = program.polyfunctions.get(&original).cloned()
                {
                    self.generate_specialized_function(
                        &poly_func,
                        *callee,
                        &specialized_callee,
                        result,
                    );
                    // Also import the original monomorphized version
                    if let Some(imported) = program.functions.get(&original).cloned() {
                        result.insert(original, imported);
                    }
                }
                continue; // Skip normal import logic for synthesized symbols
            }

            // Check if this callee has specializations that need to be generated
            // This handles the case where the IR has the original symbol but we need
            // a specialized version
            if let Some(specialization_syms) = self.specializations.get(callee).cloned() {
                for specialized_sym in specialization_syms {
                    if result.contains_key(&specialized_sym) {
                        continue; // Already generated
                    }
                    let Some(specialized_callee) = self.specialized_callees.get(&specialized_sym).cloned() else {
                        continue;
                    };
                    // Get the poly function from external module if needed
                    if let Some(module_id) = callee.module_id()
                        && module_id != self.config.module_id
                        && let Some(program) = self.config.modules.program_for(module_id)
                        && let Some(poly_func) = program.polyfunctions.get(callee).cloned()
                    {
                        self.generate_specialized_function(
                            &poly_func,
                            specialized_sym,
                            &specialized_callee,
                            result,
                        );
                    }
                }
            }

            let Some(module_id) = callee.module_id() else {
                tracing::warn!("Trying to import {callee:?}, no module ID found");
                continue;
            };

            if module_id != self.config.module_id
                && let Some(program) = self.config.modules.program_for(module_id)
                && let Some(imported) = program.functions.get(callee).cloned()
            {
                result.insert(*callee, imported);
            };

            self.check_imports(callee, result, checked);
        }
    }

    #[instrument(skip(self, result))]
    fn monomorphize_func(
        &mut self,
        func: PolyFunction,
        result: &mut IndexMap<Symbol, Function<IrTy>>,
    ) {
        for specialization in self
            .specializations
            .get(&func.name)
            .cloned()
            .unwrap_or_default()
        {
            let Some(specialized_callee) = self.specialized_callees.get(&specialization).cloned()
            else {
                tracing::error!("did not find specialization for {specialization:?}");
                continue;
            };

            self.generate_specialized_function(&func, specialization, &specialized_callee, result);
        }

        // Extract receiver type from function signature for instance methods
        let receiver_ty = if let Ty::Func(box param, ..) = &func.ty {
            match param {
                Ty::Primitive(_) | Ty::Nominal { .. } => Some(param.clone()),
                _ => None,
            }
        } else {
            None
        };

        let func = Function {
            name: func.name,
            ty: self.monomorphize_ty(func.ty, &Default::default()),
            params: func.params.into(),
            blocks: func
                .blocks
                .into_iter()
                .map(|b| self.monomorphize_block(b, &Default::default(), receiver_ty.as_ref(), None))
                .collect(),
            register_count: func.register_count,
        };

        result.insert(func.name, func);
    }

    #[instrument(skip(self, block), fields(block = %block))]
    fn monomorphize_block(
        &mut self,
        block: BasicBlock<Ty>,
        substitutions: &Specializations,
        receiver_ty: Option<&Ty>,
        specialized_caller: Option<Symbol>,
    ) -> BasicBlock<IrTy> {
        BasicBlock {
            id: block.id,
            phis: block
                .phis
                .into_iter()
                .map(|phi| Phi {
                    dest: phi.dest,
                    ty: self.monomorphize_ty(phi.ty, substitutions),
                    sources: phi.sources,
                })
                .collect(),
            instructions: block
                .instructions
                .into_iter()
                .map(|i| self.monomorphize_instruction(i, substitutions, receiver_ty, specialized_caller))
                .collect(),
            terminator: self.monomorphize_terminator(block.terminator, substitutions),
        }
    }

    #[instrument(skip(self))]
    fn monomorphize_terminator(
        &mut self,
        terminator: Terminator<Ty>,
        substitutions: &Specializations,
    ) -> Terminator<IrTy> {
        match terminator {
            Terminator::Ret { val, ty } => Terminator::Ret {
                val,
                ty: self.monomorphize_ty(ty, substitutions),
            },
            Terminator::Branch { cond, conseq, alt } => Terminator::Branch { cond, conseq, alt },
            Terminator::Jump { to } => Terminator::Jump { to },
            Terminator::Unreachable => Terminator::Unreachable,
        }
    }

    #[instrument(skip(self, instruction), fields(instruction = %instruction), ret)]
    fn monomorphize_instruction(
        &mut self,
        instruction: Instruction<Ty>,
        substitutions: &Specializations,
        receiver_ty: Option<&Ty>,
        specialized_caller: Option<Symbol>,
    ) -> Instruction<IrTy> {
        // Handle Call instructions specially to substitute callees
        if let Instruction::Call {
            dest,
            ty,
            callee,
            args,
            meta,
        } = instruction
        {
            let new_callee = match &callee {
                Value::Func(sym @ Symbol::MethodRequirement(_)) => {
                    // Resolve MethodRequirement to concrete witness when monomorphizing
                    if let Some(witness) =
                        self.resolve_method_requirement(sym, substitutions, receiver_ty)
                    {
                        Value::Func(witness)
                    } else {
                        callee
                    }
                }
                Value::Func(_sym) => {
                    // Only substitute if the call's return type has type params
                    // For concrete return types (like protocol default methods returning Int),
                    // no substitution is needed
                    if !ty.contains_type_params() {
                        callee
                    } else if let Some(caller) = specialized_caller {
                        // Extract call site ID from instruction meta
                        let call_id = meta.items.iter().find_map(|m| {
                            if let InstructionMeta::Source(id) = m {
                                Some(id)
                            } else {
                                None
                            }
                        });
                        // Look up by (caller, call_site) - aligns with paper's dimension model
                        if let Some(call_id) = call_id
                            && let Some(specialized_sym) = self.call_resolutions.get(&(caller, *call_id))
                        {
                            Value::Func(*specialized_sym)
                        } else {
                            callee
                        }
                    } else {
                        callee
                    }
                }
                _ => callee,
            };

            return Instruction::Call {
                dest,
                ty: self.monomorphize_ty(ty, substitutions),
                callee: new_callee,
                args,
                meta,
            };
        }

        instruction.map_type(|ty| self.monomorphize_ty(ty, substitutions))
    }


    /// Resolve a method requirement to a concrete witness implementation
    fn resolve_method_requirement(
        &self,
        method_req: &Symbol,
        substitutions: &Specializations,
        receiver_ty: Option<&Ty>,
    ) -> Option<Symbol> {
        // Find the protocol for this method requirement
        let protocol_sym = self.types.catalog.protocol_for_method_requirement(method_req)?;
        let Symbol::Protocol(protocol_id) = protocol_sym else {
            return None;
        };

        // Find the label for this method requirement
        let method_reqs = self.types.catalog.method_requirements.get(&protocol_sym)?;
        let label = method_reqs
            .iter()
            .find_map(|(label, sym)| if sym == method_req { Some(label.clone()) } else { None })?;

        // Collect candidate types: from substitutions plus explicit receiver type
        let mut candidates: Vec<&Ty> = substitutions.ty.values().collect();
        if let Some(recv) = receiver_ty {
            candidates.push(recv);
        }

        // Look through candidates to find a conforming type
        for concrete_ty in candidates {
            let conforming_sym = match concrete_ty {
                Ty::Nominal { symbol, .. } => *symbol,
                Ty::Primitive(sym) => *sym,
                _ => continue,
            };

            let key = ConformanceKey {
                conforming_id: conforming_sym,
                protocol_id,
            };

            if let Some(conformance) = self.types.catalog.conformances.get(&key)
                && let Some(witness) = conformance.witnesses.get_witness(&label, method_req) {
                    return Some(witness);
                }
        }

        None
    }

    #[allow(clippy::only_used_in_recursion)]
    #[instrument(skip(self))]
    fn monomorphize_ty(&mut self, ty: Ty, substitutions: &Specializations) -> IrTy {
        match ty {
            Ty::Primitive(symbol) => match symbol {
                Symbol::Int => IrTy::Int,
                Symbol::Float => IrTy::Float,
                Symbol::Bool => IrTy::Bool,
                Symbol::Void => IrTy::Void,
                Symbol::Never => IrTy::Void,
                Symbol::RawPtr => IrTy::RawPtr,
                Symbol::Byte => IrTy::Byte,
                _ => unreachable!(),
            },
            Ty::Param(param, _) => {
                if let Some(replaced) = substitutions.ty.get(&param).cloned() {
                    self.monomorphize_ty(replaced, substitutions)
                } else {
                    // Type parameter wasn't substituted - this happens for top-level generic struct access
                    // where the type should have been resolved during type inference but wasn't
                    IrTy::Void
                }
            }
            Ty::Constructor {
                name: Name::Resolved(sym @ Symbol::Variant(..), ..),
                params,
                ..
            } => {
                let mut values = match &params[0] {
                    &Ty::Void => vec![],
                    Ty::Tuple(items) => items
                        .iter()
                        .map(|t| self.monomorphize_ty(t.clone(), substitutions))
                        .collect(),
                    other => vec![self.monomorphize_ty(other.clone(), substitutions)],
                };
                values.insert(0, IrTy::Int);

                IrTy::Record(Some(sym), values)
            }
            Ty::Constructor {
                name: Name::Resolved(Symbol::Struct(..), _),
                params,
                box ret,
                ..
            } => IrTy::Func(
                params
                    .into_iter()
                    .map(|p| self.monomorphize_ty(p, substitutions))
                    .collect(),
                self.monomorphize_ty(ret, substitutions).into(),
            ),
            Ty::Func(param, ret, effects) => {
                let (params, final_ret) = uncurry_function(Ty::Func(param, ret, effects));
                IrTy::Func(
                    params
                        .into_iter()
                        .map(|p| self.monomorphize_ty(p, substitutions))
                        .collect(),
                    self.monomorphize_ty(final_ret, substitutions).into(),
                )
            }
            Ty::Tuple(items) => IrTy::Record(
                None,
                items
                    .into_iter()
                    .map(|i| self.monomorphize_ty(i, substitutions))
                    .collect(),
            ),
            Ty::Record(sym, row) => {
                let closed = row.close();
                IrTy::Record(
                    sym,
                    closed
                        .values()
                        .map(|v| self.monomorphize_ty(v.clone(), substitutions))
                        .collect(),
                )
            }
            Ty::Nominal { symbol, type_args } => {
                let nominal = if let Some(module_id) = symbol.module_id()
                    && module_id != self.config.module_id
                {
                    self.config
                        .modules
                        .lookup_nominal(&symbol)
                        .cloned()
                        .expect("didn't get external nominal")
                } else {
                    self.types
                        .catalog
                        .nominals
                        .get(&symbol)
                        .cloned()
                        .unwrap_or_else(|| unreachable!("didn't get nominal: {symbol:?}"))
                };

                // First monomorphize type_args to resolve any type parameters
                let monomorphized_type_args: Vec<Ty> = type_args
                    .iter()
                    .map(|arg| substitutions.apply(arg.clone()))
                    .collect();
                let properties = nominal.substitute_properties(&monomorphized_type_args);

                if matches!(symbol, Symbol::Enum(..)) {
                    IrTy::Record(Some(symbol), vec![IrTy::Int])
                } else {
                    let values = properties
                        .values()
                        .map(|v| self.monomorphize_ty(v.clone(), substitutions))
                        .collect();
                    IrTy::Record(Some(symbol), values)
                }
            }
            other => unreachable!("{other:?}"),
        }
    }

    #[instrument(skip(self, result))]
    fn generate_specialized_function(
        &mut self,
        func: &PolyFunction,
        specialized_name: Symbol,
        specialization: &SpecializedCallee,
        result: &mut IndexMap<Symbol, Function<IrTy>>,
    ) {
        // Get receiver type from substitutions (first concrete type substitution)
        let receiver_ty = specialization
            .specializations
            .ty
            .values()
            .find(|ty| matches!(ty, Ty::Primitive(_) | Ty::Nominal { .. }))
            .cloned();

        let specialized_func = Function {
            name: specialized_name,
            ty: self.monomorphize_ty(func.ty.clone(), &specialization.specializations),
            params: func.params.clone().into(),
            register_count: func.register_count,
            blocks: func
                .blocks
                .clone()
                .into_iter()
                .map(|b| {
                    self.monomorphize_block(b, &specialization.specializations, receiver_ty.as_ref(), Some(specialized_name))
                })
                .collect(),
        };

        result.insert(specialized_name, specialized_func);

        let mut checked = IndexSet::default();
        self.check_imports(&specialized_name, result, &mut checked);
    }
}

pub fn uncurry_function(ty: Ty) -> (Vec<Ty>, Ty) {
    match ty {
        Ty::Func(box param, box ret, _effects) => {
            let (mut params, final_ret) = uncurry_function(ret);
            if param != Ty::Void {
                params.insert(0, param);
            }
            (params, final_ret)
        }
        other => (vec![], other),
    }
}
