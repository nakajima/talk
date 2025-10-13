use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    compiling::driver::Source,
    ir::{
        basic_block::BasicBlock,
        function::Function,
        instruction::Instruction,
        ir_ty::IrTy,
        lowerer::{Lowerer, PolyFunction},
        terminator::Terminator,
    },
    label::Label,
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::Symbol},
    node_id::NodeID,
    types::{
        scheme::ForAll,
        ty::Ty,
        type_session::{TypeEntry, Types},
    },
};

#[allow(dead_code)]
pub struct Monomorphizer {
    asts: IndexMap<Source, AST<NameResolved>>,
    types: Types,
    functions: FxHashMap<Symbol, PolyFunction>,
    needs_monomorphization: Vec<Name>,
    instantiations: FxHashMap<NodeID, FxHashMap<ForAll, Ty>>,
}

impl Monomorphizer {
    pub fn new(lowerer: Lowerer) -> Self {
        Monomorphizer {
            asts: lowerer.asts,
            types: lowerer.types,
            functions: lowerer.functions,
            needs_monomorphization: lowerer.needs_monomorphization,
            instantiations: lowerer.instantiations,
        }
    }

    pub fn monomorphize(&mut self) -> FxHashMap<Symbol, Function<IrTy, Label>> {
        let mut result = FxHashMap::<Symbol, Function<IrTy, Label>>::default();
        for (name, func) in self.functions.clone() {
            result.insert(name, self.monomorphize_func(func));
        }
        result
    }

    fn monomorphize_func(&mut self, func: PolyFunction) -> Function<IrTy, Label> {
        Function {
            name: func.name,
            ty: self.monomorphize_ty(func.ty),
            params: func.params.into(),
            blocks: func
                .blocks
                .into_iter()
                .map(|b| self.monomorphize_block(b))
                .collect(),
        }
    }

    fn monomorphize_block(&mut self, block: BasicBlock<Ty, Label>) -> BasicBlock<IrTy, Label> {
        BasicBlock {
            id: block.id,
            instructions: block
                .instructions
                .into_iter()
                .map(|i| self.monomorphize_instruction(i))
                .collect(),
            terminator: self.monomorphize_terminator(block.terminator),
        }
    }

    fn monomorphize_terminator(&mut self, terminator: Terminator<Ty>) -> Terminator<IrTy> {
        match terminator {
            Terminator::Ret { val, ty } => Terminator::Ret {
                val,
                ty: self.monomorphize_ty(ty),
            },
            Terminator::Unreachable => Terminator::Unreachable,
        }
    }

    fn monomorphize_instruction(
        &mut self,
        instruction: Instruction<Ty, Label>,
    ) -> Instruction<IrTy, Label> {
        instruction.map_type(|ty| self.monomorphize_ty(ty))
    }

    #[allow(clippy::only_used_in_recursion)]
    fn monomorphize_ty(&mut self, ty: Ty) -> IrTy {
        match ty {
            Ty::Primitive(symbol) => match symbol {
                Symbol::Int => IrTy::Int,
                Symbol::Float => IrTy::Float,
                Symbol::Bool => IrTy::Bool,
                Symbol::Void => IrTy::Void,
                _ => unreachable!(),
            },
            Ty::Param(..) => {
                // todo!("param?? {ty:?}");
                IrTy::Void
            }
            Ty::Constructor {
                params, box ret, ..
            } => IrTy::Func(
                params
                    .into_iter()
                    .map(|p| self.monomorphize_ty(p))
                    .collect(),
                self.monomorphize_ty(ret).into(),
            ),
            Ty::Func(param, ret) => {
                let (params, final_ret) = uncurry_function(Ty::Func(param, ret));
                IrTy::Func(
                    params
                        .into_iter()
                        .map(|p| self.monomorphize_ty(p))
                        .collect(),
                    self.monomorphize_ty(final_ret).into(),
                )
            }
            Ty::Tuple(..) => todo!(),
            Ty::Record(..) => todo!(),
            Ty::Nominal { symbol, .. } => {
                if let Some(properties) = self.types.catalog.properties.get(&symbol).cloned() {
                    IrTy::Record(
                        properties
                            .values()
                            .map(|v| match self.types.get_symbol(v).unwrap() {
                                TypeEntry::Mono(ty) => self.monomorphize_ty(ty.clone()),
                                TypeEntry::Poly(scheme) => self.monomorphize_ty(scheme.ty.clone()),
                            })
                            .collect(),
                    )
                } else {
                    todo!("don't know how to handle {ty:?}");
                }
            }
        }
    }
}

fn uncurry_function(ty: Ty) -> (Vec<Ty>, Ty) {
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
