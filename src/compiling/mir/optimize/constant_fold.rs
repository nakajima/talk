//! Local constant propagation and scalar folding over MIR.

use rustc_hash::FxHashMap;

use crate::compiling::mir::build::{
    CmpKind, Constant, Function, Inst, LocalId, Operand, ScalarOp, Slot, Term, visit_inst,
};

use super::PassResult;

struct ConstantFolder {
    values: FxHashMap<LocalId, Constant>,
}

impl ConstantFolder {
    fn new() -> Self {
        Self {
            values: FxHashMap::default(),
        }
    }

    fn resolve(&self, operand: &mut Operand) -> bool {
        let Operand::Local(local) = *operand else {
            return false;
        };
        let Some(constant) = self.values.get(&local).copied() else {
            return false;
        };
        *operand = Operand::Const(constant);
        true
    }

    fn scalar(op: ScalarOp, a: Constant, b: Option<Constant>) -> Option<Constant> {
        use Constant::{Bool, Float, Int};
        use ScalarOp::*;

        match (op, a, b) {
            (IntAdd, Int(a), Some(Int(b))) => Some(Int(a.wrapping_add(b))),
            (IntSub, Int(a), Some(Int(b))) => Some(Int(a.wrapping_sub(b))),
            (IntMul, Int(a), Some(Int(b))) => Some(Int(a.wrapping_mul(b))),
            (IntDiv, Int(_), Some(Int(0))) => None,
            (IntDiv, Int(a), Some(Int(b))) => Some(Int(a.wrapping_div(b))),
            (FloatAdd, Float(a), Some(Float(b))) => Some(Float(a + b)),
            (FloatSub, Float(a), Some(Float(b))) => Some(Float(a - b)),
            (FloatMul, Float(a), Some(Float(b))) => Some(Float(a * b)),
            (FloatDiv, Float(a), Some(Float(b))) => Some(Float(a / b)),
            (IntAnd, Int(a), Some(Int(b))) => Some(Int(a & b)),
            (IntOr, Int(a), Some(Int(b))) => Some(Int(a | b)),
            (IntXor, Int(a), Some(Int(b))) => Some(Int(a ^ b)),
            (IntShl, Int(a), Some(Int(b))) => Some(Int(a.wrapping_shl(b as u32))),
            (IntShr, Int(a), Some(Int(b))) => Some(Int(a.wrapping_shr(b as u32))),
            (IntNot, Int(a), None) => Some(Int(!a)),
            (IntCmp(kind), Int(a), Some(Int(b))) => Some(Bool(Self::compare(kind, a, b))),
            (FloatCmp(kind), Float(a), Some(Float(b))) => Some(Bool(Self::compare(kind, a, b))),
            (BoolCmp(CmpKind::Eq), Bool(a), Some(Bool(b))) => Some(Bool(a == b)),
            (BoolCmp(CmpKind::Ne), Bool(a), Some(Bool(b))) => Some(Bool(a != b)),
            (FloatToIntTrunc, Float(value), None) => Some(Int(value as i64)),
            (IntToFloat, Int(value), None) => Some(Float(value as f64)),
            _ => None,
        }
    }

    fn compare<T: PartialOrd + PartialEq>(kind: CmpKind, a: T, b: T) -> bool {
        match kind {
            CmpKind::Eq => a == b,
            CmpKind::Ne => a != b,
            CmpKind::Lt => a < b,
            CmpKind::Le => a <= b,
            CmpKind::Gt => a > b,
            CmpKind::Ge => a >= b,
        }
    }

    fn instruction(&mut self, inst: &mut Inst) -> PassResult {
        let mut defs = Vec::new();
        visit_inst(inst, &mut |slot, local| {
            if slot == Slot::Def {
                defs.push(*local);
            }
        });
        let mut definition = None;
        let mut applied = 0;
        let changed = match inst {
            Inst::Copy { dest, src } => {
                let changed = self.resolve(src);
                if let Operand::Const(constant) = src {
                    definition = Some((*dest, *constant));
                }
                changed
            }
            Inst::Scalar { dest, op, a, b } => {
                let mut changed = self.resolve(a);
                if let Some(b) = b {
                    changed |= self.resolve(b);
                }
                let folded = match (*a, *b) {
                    (Operand::Const(a), Some(Operand::Const(b))) => Self::scalar(*op, a, Some(b)),
                    (Operand::Const(a), None) => Self::scalar(*op, a, None),
                    _ => None,
                };
                if let Some(result) = folded {
                    definition = Some((*dest, result));
                    *inst = Inst::Copy {
                        dest: *dest,
                        src: Operand::Const(result),
                    };
                    applied = 1;
                    changed = true;
                }
                changed
            }
            _ => false,
        };
        for dest in defs {
            self.values.remove(&dest);
        }
        if let Some((dest, constant)) = definition {
            self.values.insert(dest, constant);
        }
        PassResult { changed, applied }
    }

    fn terminator(&self, term: &mut Term) -> bool {
        match term {
            Term::Goto(_, args) => {
                let mut changed = false;
                for arg in args {
                    changed |= self.resolve(arg);
                }
                changed
            }
            Term::Branch { cond, .. } | Term::Switch { tag: cond, .. } | Term::Return(cond) => {
                self.resolve(cond)
            }
            Term::Trap(_) | Term::UnwindRet => false,
        }
    }
}

pub(super) fn run(function: &mut Function) -> PassResult {
    let mut result = PassResult::default();
    for block in &mut function.blocks {
        let mut folder = ConstantFolder::new();
        for inst in &mut block.insts {
            result.include(folder.instruction(inst));
        }
        if let Some(term) = &mut block.term {
            result.include(PassResult::changed(folder.terminator(term)));
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiling::mir::build::{BlockData, ScalarOp};

    #[test]
    fn folds_constant_scalar_chains_and_return_operands() {
        let mut function = Function {
            debug_names: None,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "fold".into(),
            arity: 0,
            locals: crate::compiling::mir::build::LocalInfo::uniform(2),
            blocks: vec![BlockData {
                debug: None,
                params: Vec::new(),
                insts: vec![
                    Inst::Copy {
                        dest: 0,
                        src: Operand::Const(Constant::Int(20)),
                    },
                    Inst::Scalar {
                        dest: 1,
                        op: ScalarOp::IntAdd,
                        a: Operand::Local(0),
                        b: Some(Operand::Const(Constant::Int(22))),
                    },
                ],
                term: Some(Term::Return(Operand::Local(1))),
            }],
        };

        let stats = run(&mut function);
        assert!(stats.changed);
        assert_eq!(stats.applied, 1);
        assert!(matches!(
            function.blocks[0].insts[1],
            Inst::Copy {
                dest: 1,
                src: Operand::Const(Constant::Int(42))
            }
        ));
        assert!(matches!(
            function.blocks[0].term,
            Some(Term::Return(Operand::Const(Constant::Int(42))))
        ));
    }

    #[test]
    fn does_not_fold_trapping_integer_division() {
        let mut function = Function {
            debug_names: None,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "divide".into(),
            arity: 0,
            locals: crate::compiling::mir::build::LocalInfo::uniform(1),
            blocks: vec![BlockData {
                debug: None,
                params: Vec::new(),
                insts: vec![Inst::Scalar {
                    dest: 0,
                    op: ScalarOp::IntDiv,
                    a: Operand::Const(Constant::Int(1)),
                    b: Some(Operand::Const(Constant::Int(0))),
                }],
                term: Some(Term::Return(Operand::Local(0))),
            }],
        };

        let stats = run(&mut function);
        assert!(!stats.changed);
        assert_eq!(stats.applied, 0);
        assert!(matches!(function.blocks[0].insts[0], Inst::Scalar { .. }));
    }
}
