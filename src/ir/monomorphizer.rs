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

pub struct Monomorphizer<'a> {
    asts: &'a FxHashMap<Source, AST<NameResolved>>,
    types: &'a Types,
    functions: FxHashMap<Name, PolyFunction>,
    needs_monomorphization: Vec<Name>,
    instantiations: FxHashMap<NodeID, FxHashMap<ForAll, Ty>>,
}

impl<'a> Monomorphizer<'a> {
    pub fn new(lowerer: Lowerer<'a>) -> Self {
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
        }
    }

    fn monomorphize_instruction(&mut self, instruction: Instruction<Ty>) -> Instruction<IrTy> {
        match instruction {
            Instruction::ConstantInt(r, v, m) => Instruction::ConstantInt(r, v, m),
            Instruction::ConstantFloat(r, v, m) => Instruction::ConstantFloat(r, v, m),
            Instruction::Add {
                dest,
                ty,
                a,
                b,
                meta,
            } => todo!(),
            Instruction::Sub {
                dest,
                ty,
                a,
                b,
                meta,
            } => todo!(),
            Instruction::Mul {
                dest,
                ty,
                a,
                b,
                meta,
            } => todo!(),
            Instruction::Div {
                dest,
                ty,
                a,
                b,
                meta,
            } => todo!(),
        }
    }

    fn monomorphize_ty(&mut self, ty: Ty) -> IrTy {
        match ty {
            Ty::Primitive(symbol) => match symbol {
                Symbol::Int => IrTy::Int,
                Symbol::Float => IrTy::Float,
                Symbol::Bool => IrTy::Bool,
                Symbol::Void => IrTy::Void,
                _ => unreachable!(),
            },
            Ty::Param(type_param_id) => todo!(),
            Ty::Constructor {
                symbol,
                params,
                ret,
            } => todo!(),
            Ty::Func(param, ret) => IrTy::Func(
                param
                    .uncurry_params()
                    .into_iter()
                    .map(|p| self.monomorphize_ty(p))
                    .collect(),
                self.monomorphize_ty(*ret).into(),
            ),
            Ty::Tuple(items) => todo!(),
            Ty::Record(row) => todo!(),
            Ty::Nominal {
                symbol,
                type_args,
                row,
            } => todo!(),
        }
    }
}
