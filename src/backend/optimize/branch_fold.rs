//! Fold branches whose destination is known without executing the branch.

use crate::backend::mir::{Constant, Function, Operand, Term};

use super::PassResult;

pub(super) fn run(function: &mut Function) -> PassResult {
    let mut applied = 0;
    for block in &mut function.blocks {
        let replacement = match block.term.as_ref() {
            Some(Term::Branch {
                cond: Operand::Const(Constant::Bool(value)),
                then_block,
                else_block,
            }) => Some(Term::Goto(
                if *value { *then_block } else { *else_block },
                Vec::new(),
            )),
            Some(Term::Branch {
                then_block,
                else_block,
                ..
            }) if then_block == else_block => Some(Term::Goto(*then_block, Vec::new())),
            _ => None,
        };
        if let Some(term) = replacement {
            block.term = Some(term);
            applied += 1;
        }
    }
    PassResult::applied(applied)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::mir::BlockData;

    #[test]
    fn constant_branch_becomes_goto() {
        let mut function = Function {
            name: "branch".into(),
            arity: 0,
            n_locals: 1,
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Branch {
                        cond: Operand::Const(Constant::Bool(false)),
                        then_block: 1,
                        else_block: 2,
                    }),
                },
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Return(Operand::Const(Constant::Unit))),
                },
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Return(Operand::Const(Constant::Unit))),
                },
            ],
        };

        assert_eq!(run(&mut function).applied, 1);
        assert!(
            matches!(function.blocks[0].term, Some(Term::Goto(2, ref args)) if args.is_empty())
        );
    }
}
