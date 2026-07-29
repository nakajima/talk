//! Fold known branches and canonicalize Boolean comparisons feeding branches.

use crate::backend::mir::{CmpKind, Constant, Function, Inst, Operand, ScalarOp, Term};

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
            Some(Term::Branch {
                cond: Operand::Local(cond),
                then_block,
                else_block,
            }) => block.insts.last().and_then(|inst| {
                let Inst::Scalar {
                    dest,
                    op: ScalarOp::BoolCmp(kind @ (CmpKind::Eq | CmpKind::Ne)),
                    a,
                    b: Some(b),
                } = inst
                else {
                    return None;
                };
                if dest != cond {
                    return None;
                }
                let (source, expected) = match (*a, *b) {
                    (source @ Operand::Local(_), Operand::Const(Constant::Bool(expected)))
                    | (Operand::Const(Constant::Bool(expected)), source @ Operand::Local(_)) => {
                        (source, expected)
                    }
                    _ => return None,
                };
                if source == Operand::Local(*dest) {
                    return None;
                }
                let inverted = matches!(
                    (*kind, expected),
                    (CmpKind::Eq, false) | (CmpKind::Ne, true)
                );
                Some(Term::Branch {
                    cond: source,
                    then_block: if inverted { *else_block } else { *then_block },
                    else_block: if inverted { *then_block } else { *else_block },
                })
            }),
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

    #[test]
    fn boolean_comparison_feeding_branch_uses_the_source_directly() {
        for (kind, expected, constant_first, then_block, else_block) in [
            (CmpKind::Eq, true, false, 1, 2),
            (CmpKind::Eq, false, false, 2, 1),
            (CmpKind::Ne, true, false, 2, 1),
            (CmpKind::Ne, false, true, 1, 2),
        ] {
            let (a, b) = if constant_first {
                (Operand::Const(Constant::Bool(expected)), Operand::Local(0))
            } else {
                (Operand::Local(0), Operand::Const(Constant::Bool(expected)))
            };
            let mut function = Function {
                name: "bool_branch".into(),
                arity: 1,
                n_locals: 2,
                blocks: vec![
                    BlockData {
                        params: Vec::new(),
                        insts: vec![Inst::Scalar {
                            dest: 1,
                            op: ScalarOp::BoolCmp(kind),
                            a,
                            b: Some(b),
                        }],
                        term: Some(Term::Branch {
                            cond: Operand::Local(1),
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
            assert!(matches!(
                function.blocks[0].term,
                Some(Term::Branch {
                    cond: Operand::Local(0),
                    then_block: actual_then,
                    else_block: actual_else,
                }) if actual_then == then_block && actual_else == else_block
            ));
        }
    }

    #[test]
    fn comparison_that_overwrites_its_source_is_not_rewritten() {
        let mut function = Function {
            name: "overwriting_bool_branch".into(),
            arity: 1,
            n_locals: 1,
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: vec![Inst::Scalar {
                        dest: 0,
                        op: ScalarOp::BoolCmp(CmpKind::Eq),
                        a: Operand::Local(0),
                        b: Some(Operand::Const(Constant::Bool(false))),
                    }],
                    term: Some(Term::Branch {
                        cond: Operand::Local(0),
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

        assert_eq!(run(&mut function).applied, 0);
    }
}
