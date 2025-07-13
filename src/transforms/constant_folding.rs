use std::collections::{HashMap, HashSet};

use crate::lowering::{
    instr::Instr,
    ir_function::IRFunction,
    ir_module::IRModule,
    ir_type::IRType,
    register::Register,
    phi_predecessors::PhiPredecessors,
};

#[derive(Default)]
pub struct ConstantFolder;

#[derive(Clone, Debug, PartialEq)]
enum ConstValue {
    Int(i64),
    Float(f64),
    Bool(bool),
}

impl ConstantFolder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn run(self, mut module: IRModule) -> IRModule {
        for func in &mut module.functions {
            Self::fold_function(func);
        }
        module
    }

    fn fold_function(func: &mut IRFunction) {
        let mut consts: HashMap<Register, ConstValue> = HashMap::new();
        let mut removed_blocks = HashSet::new();

        for block in &mut func.blocks {
            let mut new_instructions = Vec::new();
            for instr in std::mem::take(&mut block.instructions) {
                let mut instr = instr;
                match instr {
                    Instr::ConstantInt(dest, val) => {
                        consts.insert(dest, ConstValue::Int(val));
                    }
                    Instr::ConstantFloat(dest, val) => {
                        consts.insert(dest, ConstValue::Float(val));
                    }
                    Instr::ConstantBool(dest, val) => {
                        consts.insert(dest, ConstValue::Bool(val));
                    }
                    Instr::Add(dest, ref ty, r1, r2) => {
                        if let Some(val) = Self::fold_int_binop(
                            r1,
                            r2,
                            &consts,
                            |a, b| a + b,
                        ) {
                            let new = Self::make_const(dest, ty.clone(), val.clone());
                            consts.insert(dest, val);
                            instr = new;
                        }
                    }
                    Instr::Sub(dest, ref ty, r1, r2) => {
                        if let Some(val) = Self::fold_int_binop(
                            r1,
                            r2,
                            &consts,
                            |a, b| a - b,
                        ) {
                            let new = Self::make_const(dest, ty.clone(), val.clone());
                            consts.insert(dest, val);
                            instr = new;
                        }
                    }
                    Instr::Mul(dest, ref ty, r1, r2) => {
                        if let Some(val) = Self::fold_int_binop(
                            r1,
                            r2,
                            &consts,
                            |a, b| a * b,
                        ) {
                            let new = Self::make_const(dest, ty.clone(), val.clone());
                            consts.insert(dest, val);
                            instr = new;
                        }
                    }
                    Instr::Div(dest, ref ty, r1, r2) => {
                        if let Some(val) = Self::fold_int_binop(
                            r1,
                            r2,
                            &consts,
                            |a, b| a / b,
                        ) {
                            let new = Self::make_const(dest, ty.clone(), val.clone());
                            consts.insert(dest, val);
                            instr = new;
                        }
                    }
                    Instr::Eq(dest, _, r1, r2) => {
                        if let Some(val) = Self::fold_cmp_binop(r1, r2, &consts, |a, b| a == b) {
                            instr = Instr::ConstantBool(dest, val);
                            consts.insert(dest, ConstValue::Bool(val));
                        }
                    }
                    Instr::Ne(dest, _, r1, r2) => {
                        if let Some(val) = Self::fold_cmp_binop(r1, r2, &consts, |a, b| a != b) {
                            instr = Instr::ConstantBool(dest, val);
                            consts.insert(dest, ConstValue::Bool(val));
                        }
                    }
                    Instr::LessThan(dest, _, r1, r2) => {
                        if let Some(val) = Self::fold_cmp_binop(r1, r2, &consts, |a, b| a < b) {
                            instr = Instr::ConstantBool(dest, val);
                            consts.insert(dest, ConstValue::Bool(val));
                        }
                    }
                    Instr::LessThanEq(dest, _, r1, r2) => {
                        if let Some(val) = Self::fold_cmp_binop(r1, r2, &consts, |a, b| a <= b) {
                            instr = Instr::ConstantBool(dest, val);
                            consts.insert(dest, ConstValue::Bool(val));
                        }
                    }
                    Instr::GreaterThan(dest, _, r1, r2) => {
                        if let Some(val) = Self::fold_cmp_binop(r1, r2, &consts, |a, b| a > b) {
                            instr = Instr::ConstantBool(dest, val);
                            consts.insert(dest, ConstValue::Bool(val));
                        }
                    }
                    Instr::GreaterThanEq(dest, _, r1, r2) => {
                        if let Some(val) = Self::fold_cmp_binop(r1, r2, &consts, |a, b| a >= b) {
                            instr = Instr::ConstantBool(dest, val);
                            consts.insert(dest, ConstValue::Bool(val));
                        }
                    }
                    Instr::Branch { cond, true_target, false_target } => {
                        if let Some(ConstValue::Bool(b)) = consts.get(&cond) {
                            let taken = if *b { true_target } else { false_target };
                            let removed = if *b { false_target } else { true_target };
                            instr = Instr::Jump(taken);
                            removed_blocks.insert(removed);
                        }
                    }
                    Instr::Phi(dest, ref ty, mut preds) => {
                        preds.0.retain(|(_, bb)| !removed_blocks.contains(bb));
                        if let Some(val) = Self::fold_phi(&preds, &consts) {
                            instr = Self::make_const(dest, ty.clone(), val.clone());
                            consts.insert(dest, val);
                        } else {
                            instr = Instr::Phi(dest, ty.clone(), preds);
                        }
                    }
                    _ => {}
                }
                new_instructions.push(instr);
            }
            block.instructions = new_instructions;
        }

        // Second pass to remove phi predecessors that reference removed blocks
        for block in &mut func.blocks {
            for instr in &mut block.instructions {
                if let Instr::Phi(_, _, preds) = instr {
                    preds.0.retain(|(_, bb)| !removed_blocks.contains(bb));
                }
            }
        }
    }

    fn fold_phi(preds: &PhiPredecessors, consts: &HashMap<Register, ConstValue>) -> Option<ConstValue> {
        if preds.0.is_empty() {
            return None;
        }
        let mut iter = preds.0.iter().filter_map(|(reg, _)| consts.get(reg));
        let first = iter.next()?.clone();
        if iter.all(|c| *c == first) {
            Some(first)
        } else {
            None
        }
    }

    fn fold_int_binop<F>(r1: Register, r2: Register, consts: &HashMap<Register, ConstValue>, op: F) -> Option<ConstValue>
    where
        F: FnOnce(i64, i64) -> i64,
    {
        match (consts.get(&r1), consts.get(&r2)) {
            (Some(ConstValue::Int(a)), Some(ConstValue::Int(b))) => Some(ConstValue::Int(op(*a, *b))),
            _ => None,
        }
    }

    fn fold_cmp_binop<F>(r1: Register, r2: Register, consts: &HashMap<Register, ConstValue>, op: F) -> Option<bool>
    where
        F: FnOnce(i64, i64) -> bool,
    {
        match (consts.get(&r1), consts.get(&r2)) {
            (Some(ConstValue::Int(a)), Some(ConstValue::Int(b))) => Some(op(*a, *b)),
            _ => None,
        }
    }

    fn make_const(dest: Register, ty: IRType, val: ConstValue) -> Instr {
        match (ty, val) {
            (IRType::Int, ConstValue::Int(v)) => Instr::ConstantInt(dest, v),
            (IRType::Float, ConstValue::Float(v)) => Instr::ConstantFloat(dest, v),
            (IRType::Bool, ConstValue::Bool(v)) => Instr::ConstantBool(dest, v),
            (_, ConstValue::Int(v)) => Instr::ConstantInt(dest, v),
            (_, ConstValue::Float(v)) => Instr::ConstantFloat(dest, v),
            (_, ConstValue::Bool(v)) => Instr::ConstantBool(dest, v),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ConstantFolder;
    use crate::lowering::{
        instr::{Instr},
        ir_function::IRFunction,
        ir_module::IRModule,
        ir_type::IRType,
        lowerer::{BasicBlock, BasicBlockID},
        phi_predecessors::PhiPredecessors,
        register::Register,
    };

    #[test]
    fn folds_constants() {
        let module = IRModule {
            functions: vec![IRFunction {
                debug_info: Default::default(),
                name: "@main".into(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                blocks: vec![
                    BasicBlock {
                        id: BasicBlockID::ENTRY,
                        instructions: vec![
                            Instr::ConstantBool(Register(0), false),
                            Instr::Branch { cond: Register(0), true_target: BasicBlockID(1), false_target: BasicBlockID(2) },
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(1),
                        instructions: vec![
                            Instr::ConstantInt(Register(1), 1),
                            Instr::ConstantInt(Register(2), 2),
                            Instr::Add(Register(3), IRType::Int, Register(1), Register(2)),
                            Instr::Jump(BasicBlockID(3)),
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(2),
                        instructions: vec![
                            Instr::ConstantInt(Register(4), 3),
                            Instr::ConstantInt(Register(5), 4),
                            Instr::Add(Register(6), IRType::Int, Register(4), Register(5)),
                            Instr::Jump(BasicBlockID(3)),
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(3),
                        instructions: vec![
                            Instr::Phi(Register(7), IRType::Int, PhiPredecessors(vec![(Register(3), BasicBlockID(1)), (Register(6), BasicBlockID(2))])),
                            Instr::ConstantInt(Register(8), 2),
                            Instr::ConstantInt(Register(9), 3),
                            Instr::Mul(Register(10), IRType::Int, Register(9), Register(9)),
                            Instr::Add(Register(11), IRType::Int, Register(8), Register(10)),
                            Instr::Ret(IRType::Int, Some(Register(11).into())),
                        ],
                    },
                ],
                env_ty: None,
                env_reg: None,
                size: 1,
            }],
            constants: vec![],
        };

        let optimized = ConstantFolder::new().run(module);
        let func = optimized.functions.iter().find(|f| f.name == "@main").unwrap();
        assert_eq!(func.blocks[0].instructions[1], Instr::Jump(BasicBlockID(2)));
        if let Instr::ConstantInt(_, 7) = func.blocks[3].instructions[0] { } else { panic!("phi not folded"); }
        if let Instr::ConstantInt(_, 11) = func.blocks[3].instructions[4] { } else { panic!("mul/add not folded"); }
    }

}
