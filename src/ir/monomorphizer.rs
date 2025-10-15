use indexmap::IndexMap;
use tracing::instrument;

use crate::{
    ast::AST,
    compiling::driver::Source,
    ir::{
        basic_block::BasicBlock,
        function::Function,
        instruction::Instruction,
        ir_ty::IrTy,
        lowerer::{Lowerer, PolyFunction, Specialization, Substitutions},
        terminator::Terminator,
    },
    label::Label,
    name_resolution::{name_resolver::NameResolved, symbol::Symbol},
    types::{ty::Ty, type_session::Types},
};

#[allow(dead_code)]
pub struct Monomorphizer {
    asts: IndexMap<Source, AST<NameResolved>>,
    types: Types,
    functions: IndexMap<Symbol, PolyFunction>,
    specializations: IndexMap<Symbol, Vec<Specialization>>,
}

impl Monomorphizer {
    pub fn new(lowerer: Lowerer) -> Self {
        Monomorphizer {
            asts: lowerer.asts,
            types: lowerer.types,
            functions: lowerer.functions,
            specializations: lowerer.specializations,
        }
    }

    #[instrument(skip(self))]
    pub fn monomorphize(&mut self) -> IndexMap<Symbol, Function<IrTy, Label>> {
        let mut result = IndexMap::<Symbol, Function<IrTy, Label>>::default();
        let functions = self.functions.clone();
        for func in functions.into_values() {
            self.monomorphize_func(func, &mut result);
        }
        result
    }

    #[instrument(skip(self))]
    fn monomorphize_func(
        &mut self,
        func: PolyFunction,
        result: &mut IndexMap<Symbol, Function<IrTy, Label>>,
    ) {
        for specialization in self
            .specializations
            .get(&func.name.symbol().unwrap())
            .cloned()
            .unwrap_or_default()
        {
            self.generate_specialized_function(&func, &specialization, result);
        }

        let func = Function {
            name: func.name,
            ty: self.monomorphize_ty(func.ty, &Default::default()),
            params: func.params.into(),
            blocks: func
                .blocks
                .into_iter()
                .map(|b| self.monomorphize_block(b, &Default::default()))
                .collect(),
        };

        result.insert(func.name.symbol().unwrap(), func);
    }

    #[instrument(skip(self, block), fields(block = %block))]
    fn monomorphize_block(
        &mut self,
        block: BasicBlock<Ty, Label>,
        substitutions: &Substitutions,
    ) -> BasicBlock<IrTy, Label> {
        BasicBlock {
            id: block.id,
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
            Terminator::Unreachable => Terminator::Unreachable,
        }
    }

    #[instrument(skip(self, instruction), fields(instruction = %instruction), ret)]
    fn monomorphize_instruction(
        &mut self,
        instruction: Instruction<Ty, Label>,
        substitutions: &Substitutions,
    ) -> Instruction<IrTy, Label> {
        instruction.map_type(|ty| self.monomorphize_ty(ty, substitutions))
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
                _ => unreachable!(),
            },
            Ty::Param(param) => {
                if let Some(replaced) = substitutions.ty.get(&param).cloned() {
                    self.monomorphize_ty(replaced, substitutions)
                } else {
                    IrTy::Void
                }
            }
            Ty::Constructor {
                params, box ret, ..
            } => IrTy::Func(
                params
                    .into_iter()
                    .map(|p| self.monomorphize_ty(p, substitutions))
                    .collect(),
                self.monomorphize_ty(ret, substitutions).into(),
            ),
            Ty::Func(param, ret) => {
                let (params, final_ret) = uncurry_function(Ty::Func(param, ret));
                IrTy::Func(
                    params
                        .into_iter()
                        .map(|p| self.monomorphize_ty(p, substitutions))
                        .collect(),
                    self.monomorphize_ty(final_ret, substitutions).into(),
                )
            }
            Ty::Tuple(..) => todo!(),
            Ty::Record(..) => todo!(),
            Ty::Nominal { row, .. } => {
                let closed = row.close();
                IrTy::Record(
                    closed
                        .values()
                        .map(|v| self.monomorphize_ty(v.clone(), substitutions))
                        .collect(),
                )
            }
        }
    }

    #[instrument(skip(self))]
    fn generate_specialized_function(
        &mut self,
        func: &PolyFunction,
        specialization: &Specialization,
        result: &mut IndexMap<Symbol, Function<IrTy, Label>>,
    ) {
        let specialized_func = Function {
            name: specialization.name.clone(),
            ty: self.monomorphize_ty(func.ty.clone(), &specialization.substitutions),
            params: func.params.clone().into(),
            blocks: func
                .blocks
                .clone()
                .into_iter()
                .map(|b| self.monomorphize_block(b, &specialization.substitutions))
                .collect(),
        };

        result.insert(specialization.name.symbol().unwrap(), specialized_func);
    }
}

pub fn uncurry_function(ty: Ty) -> (Vec<Ty>, Ty) {
    match ty {
        Ty::Func(box param, box ret) => {
            let (mut params, final_ret) = uncurry_function(ret);
            if param != Ty::Void {
                params.insert(0, param);
            }
            (params, final_ret)
        }
        other => (vec![], other),
    }
}
