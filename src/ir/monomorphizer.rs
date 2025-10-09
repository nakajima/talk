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
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::Symbol},
    node_id::NodeID,
    types::{scheme::ForAll, ty::Ty, type_session::Types},
};

#[allow(dead_code)]
pub struct Monomorphizer {
    asts: FxHashMap<Source, AST<NameResolved>>,
    types: Types,
    functions: FxHashMap<Name, PolyFunction>,
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

    pub fn monomorphize(&mut self) -> FxHashMap<Name, Function<IrTy>> {
        let mut result = FxHashMap::<Name, Function<IrTy>>::default();
        for (name, func) in self.functions.clone() {
            result.insert(name, self.monomorphize_func(func));
        }
        result
    }

    fn monomorphize_func(&mut self, func: PolyFunction) -> Function<IrTy> {
        Function {
            name: func.name,
            ty: self.monomorphize_ty(func.ty),
            blocks: func
                .blocks
                .into_iter()
                .map(|b| self.monomorphize_block(b))
                .collect(),
        }
    }

    fn monomorphize_block(&mut self, block: BasicBlock<Ty>) -> BasicBlock<IrTy> {
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

    fn monomorphize_instruction(&mut self, instruction: Instruction<Ty>) -> Instruction<IrTy> {
        match instruction {
            Instruction::ConstantInt(r, v, m) => Instruction::ConstantInt(r, v, m),
            Instruction::ConstantFloat(r, v, m) => Instruction::ConstantFloat(r, v, m),
            Instruction::Add { .. } => todo!(),
            Instruction::Sub { .. } => todo!(),
            Instruction::Mul { .. } => todo!(),
            Instruction::Div { .. } => todo!(),
        }
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
            Ty::Param(..) => todo!(),
            Ty::Constructor { .. } => todo!(),
            Ty::Func(param, ret) => IrTy::Func(
                param
                    .uncurry_params()
                    .into_iter()
                    .map(|p| self.monomorphize_ty(p))
                    .collect(),
                self.monomorphize_ty(*ret).into(),
            ),
            Ty::Tuple(..) => todo!(),
            Ty::Record(..) => todo!(),
            Ty::Nominal { .. } => todo!(),
        }
    }
}
