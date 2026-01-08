use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    compiling::{driver::DriverConfig, module::ModuleId},
    ir::{
        basic_block::{BasicBlock, Phi},
        function::Function,
        instruction::{CallInstantiations, Instruction, InstructionMeta},
        ir_ty::IrTy,
        list::List,
        lowerer::{
            is_concrete_row, is_concrete_ty, substitute, substitute_row, Lowerer, PolyFunction,
            Specialization, SpecializationKey, Substitutions,
        },
        terminator::Terminator,
        value::{Reference, Value},
    },
    name::Name,
    name_resolution::{
        name_resolver::ResolvedNames,
        symbol::{Symbol, Symbols},
    },
    types::{row::Row, ty::Ty, type_session::Types, typed_ast::TypedAST},
};

#[allow(dead_code)]
pub struct Monomorphizer<'a> {
    ast: &'a mut TypedAST<Ty>,
    types: &'a mut Types,
    config: &'a DriverConfig,
    symbols: &'a mut Symbols,
    resolved_names: &'a mut ResolvedNames,
    pub(super) functions: IndexMap<Symbol, PolyFunction>,
    specializations: IndexMap<Symbol, Vec<Specialization>>,
    specialization_intern: FxHashMap<Symbol, FxHashMap<SpecializationKey, Symbol>>,
    pending_specializations: Vec<(Symbol, Specialization)>,
}

#[allow(clippy::expect_used)]
impl<'a> Monomorphizer<'a> {
    pub fn new(lowerer: Lowerer<'a>) -> Self {
        Monomorphizer {
            ast: lowerer.ast,
            types: lowerer.types,
            symbols: lowerer.symbols,
            resolved_names: lowerer.resolved_names,
            functions: lowerer.functions,
            specializations: lowerer.specializations,
            specialization_intern: lowerer.specialization_intern,
            pending_specializations: Vec::new(),
            config: lowerer.config,
        }
    }

    #[instrument(skip(self))]
    pub fn monomorphize(&mut self) -> IndexMap<Symbol, Function<IrTy>> {
        let mut result = IndexMap::<Symbol, Function<IrTy>>::default();

        for (base, specs) in self.specializations.clone() {
            for spec in specs {
                self.pending_specializations.push((base, spec));
            }
        }

        let functions = self.functions.clone();
        for func in functions.into_values() {
            self.monomorphize_func(func, &mut result);
        }

        while let Some((base_sym, specialization)) = self.pending_specializations.pop() {
            if result.contains_key(&specialization.name) {
                continue;
            }
            self.ensure_polyfunction(base_sym);
            let Some(base_func) = self.functions.get(&base_sym).cloned() else {
                continue;
            };
            self.generate_specialized_function(&base_func, &specialization, &mut result);
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
            let Some(module_id) = callee.module_id() else {
                tracing::warn!("Trying to import {callee:?}, no module ID found");
                continue;
            };

            if module_id != self.config.module_id
                && !result.contains_key(callee)
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
        let func = Function {
            name: func.name,
            ty: self.monomorphize_ty(func.ty, &Default::default()),
            params: func.params.into(),
            blocks: func
                .blocks
                .into_iter()
                .map(|b| self.monomorphize_block(b, &Default::default()))
                .collect(),
            register_count: func.register_count,
        };

        result.insert(func.name, func);
    }

    fn ensure_polyfunction(&mut self, symbol: Symbol) {
        if self.functions.contains_key(&symbol) {
            return;
        }

        let Some(module_id) = symbol.module_id() else {
            return;
        };
        if module_id == ModuleId::Current || module_id == self.config.module_id {
            return;
        }

        if let Some(program) = self.config.modules.program_for(module_id)
            && let Some(func) = program.polyfunctions.get(&symbol).cloned()
        {
            self.functions.insert(symbol, func);
        }
    }

    #[instrument(skip(self, block), fields(block = %block))]
    fn monomorphize_block(
        &mut self,
        block: BasicBlock<Ty>,
        substitutions: &Substitutions,
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
                .map(|i| self.monomorphize_instruction(i, substitutions))
                .collect(),
            terminator: self.monomorphize_terminator(block.terminator, substitutions),
        }
    }

    #[instrument(skip(self))]
    fn monomorphize_terminator(
        &mut self,
        terminator: Terminator<Ty>,
        substitutions: &Substitutions,
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
        substitutions: &Substitutions,
    ) -> Instruction<IrTy> {
        if let Instruction::Call {
            dest,
            ty,
            callee,
            args,
            meta,
        } = instruction
        {
            let (call_instantiations, meta_items) = self.split_call_instantiations(meta);
            let mut callee = callee;

            if let Some(call_instantiations) = call_instantiations {
                if !call_instantiations.is_empty()
                    && !matches!(call_instantiations.callee, Symbol::MethodRequirement(_))
                {
                    let callee_substitutions =
                        self.substitutions_for_call(&call_instantiations, substitutions);
                    let has_instantiations = !callee_substitutions.ty.is_empty()
                        || !callee_substitutions.row.is_empty()
                        || !callee_substitutions.witnesses.is_empty();
                    if has_instantiations && self.substitutions_are_concrete(&callee_substitutions)
                    {
                        let name = self.monomorphize_name(
                            call_instantiations.callee,
                            &callee_substitutions,
                        );
                        if let Ok(sym) = name.symbol() {
                            callee = self.replace_callee_symbol(callee, sym);
                        }
                    }
                }
            }

            // Substitute MethodRequirement callees based on witness instantiations.
            let callee = match &callee {
                Value::Func(sym @ Symbol::MethodRequirement(_)) => {
                    if let Some(impl_sym) = substitutions.witnesses.get(sym) {
                        Value::Func(*impl_sym)
                    } else {
                        if !substitutions.witnesses.is_empty() {
                            tracing::error!("did not get witness for {sym:?}, {substitutions:?}");
                        }
                        callee
                    }
                }
                _ => callee,
            };

            return Instruction::Call {
                dest,
                ty: self.monomorphize_ty(ty, substitutions),
                callee,
                args,
                meta: meta_items.into(),
            };
        }

        instruction.map_type(|ty| self.monomorphize_ty(ty, substitutions))
    }

    fn split_call_instantiations(
        &self,
        meta: List<InstructionMeta>,
    ) -> (Option<CallInstantiations>, Vec<InstructionMeta>) {
        let mut call_instantiations = None;
        let mut meta_items = Vec::with_capacity(meta.items.len());
        for item in meta.items {
            match item {
                InstructionMeta::CallInstantiations(call) => {
                    call_instantiations = Some(call);
                }
                other => meta_items.push(other),
            }
        }
        (call_instantiations, meta_items)
    }

    fn substitutions_for_call(
        &self,
        call_instantiations: &CallInstantiations,
        caller_substitutions: &Substitutions,
    ) -> Substitutions {
        let mut substitutions = Substitutions::default();
        for (param_id, ty) in &call_instantiations.instantiations.ty {
            substitutions
                .ty
                .insert(Ty::Param(*param_id), substitute(ty.clone(), caller_substitutions));
        }
        for (row_param_id, row) in &call_instantiations.instantiations.row {
            substitutions.row.insert(
                *row_param_id,
                substitute_row(row.clone(), caller_substitutions),
            );
        }
        substitutions
            .witnesses
            .extend(call_instantiations.witnesses.iter().map(|(k, v)| (*k, *v)));
        substitutions
    }

    fn substitutions_are_concrete(&self, substitutions: &Substitutions) -> bool {
        substitutions.ty.values().all(is_concrete_ty)
            && substitutions
                .row
                .iter()
                .all(|(param, row)| *row == Row::Param(*param) || is_concrete_row(row))
    }

    fn replace_callee_symbol(&self, callee: Value, symbol: Symbol) -> Value {
        match callee {
            Value::Func(_) => Value::Func(symbol),
            Value::Closure { env, .. } => Value::Closure { func: symbol, env },
            Value::Ref(reference) => match reference {
                Reference::Func(_) => Value::Ref(Reference::Func(symbol)),
                Reference::Closure(_, env) => Value::Ref(Reference::Closure(symbol, env)),
                Reference::Register { frame, register } => Value::Ref(Reference::Register {
                    frame,
                    register,
                }),
            },
            other => other,
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    #[instrument(skip(self))]
    fn monomorphize_ty(&mut self, ty: Ty, substitutions: &Substitutions) -> IrTy {
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
            Ty::Param(_param) => {
                if let Some(replaced) = substitutions.ty.get(&ty).cloned() {
                    self.monomorphize_ty(replaced, substitutions)
                } else {
                    //unreachable!("did not specialize {ty:?}");

                    #[allow(unreachable_code)]
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

                let properties = nominal.substitute_properties(&type_args);

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

    fn resolve_name(&self, sym: &Symbol) -> Option<&str> {
        if matches!(sym, Symbol::Main) {
            return Some("main");
        }

        if matches!(sym, Symbol::Library) {
            return Some("lib");
        }

        if let Some(string) = self.resolved_names.symbol_names.get(sym) {
            return Some(string);
        }

        if let Some(string) = self.config.modules.resolve_name(sym) {
            return Some(string);
        }

        None
    }

    fn monomorphize_name(&mut self, symbol: Symbol, instantiations: &Substitutions) -> Name {
        let name = Name::Resolved(
            symbol,
            self.resolve_name(&symbol)
                .unwrap_or_else(|| unreachable!("did not get symbol name: {symbol:?}"))
                .to_string(),
        );

        let key = SpecializationKey::new(instantiations);
        if key.is_empty() {
            return name;
        }

        if let Some(existing) = self
            .specialization_intern
            .get(&symbol)
            .and_then(|m| m.get(&key))
            .copied()
        {
            let parts = key.parts();
            let new_name_str = format!("{}[{}]", name.name_str(), parts.join(", "));
            return Name::Resolved(existing, new_name_str);
        }

        let new_symbol: Symbol = self.symbols.next_synthesized(self.config.module_id).into();
        self.resolved_names
            .symbol_names
            .insert(new_symbol, name.name_str());
        let parts = key.parts();
        let new_name_str = format!("{}[{}]", name.name_str(), parts.join(", "));
        let new_name = Name::Resolved(new_symbol, new_name_str.clone());

        tracing::trace!("monomorphized {name:?} -> {new_name:?}");
        self.resolved_names
            .symbol_names
            .insert(new_symbol, new_name_str);

        self.specialization_intern
            .entry(symbol)
            .or_default()
            .insert(key, new_symbol);

        let specialization = Specialization {
            name: new_symbol,
            substitutions: instantiations.clone(),
        };

        self.specializations
            .entry(symbol)
            .or_default()
            .push(specialization.clone());
        self.pending_specializations
            .push((symbol, specialization));

        new_name
    }

    #[instrument(skip(self, result))]
    fn generate_specialized_function(
        &mut self,
        func: &PolyFunction,
        specialization: &Specialization,
        result: &mut IndexMap<Symbol, Function<IrTy>>,
    ) {
        let specialized_func = Function {
            name: specialization.name,
            ty: self.monomorphize_ty(func.ty.clone(), &specialization.substitutions),
            params: func.params.clone().into(),
            register_count: func.register_count,
            blocks: func
                .blocks
                .clone()
                .into_iter()
                .map(|b| self.monomorphize_block(b, &specialization.substitutions))
                .collect(),
        };

        result.insert(specialization.name, specialized_func);

        let mut checked = IndexSet::default();
        self.check_imports(&specialization.name, result, &mut checked);
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
