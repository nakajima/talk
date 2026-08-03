//! Fold known branches, canonicalize Boolean comparisons feeding branches,
//! and thread edges whose branch outcome is already known.

use crate::compiling::mir::build::{
    BlockId, CmpKind, Constant, Function, Inst, Operand, ScalarOp, Term,
};

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

    // Entering an empty branch block through an edge controlled by the same
    // operand makes that block's outcome known. Redirect only that incoming
    // edge, so other predecessors can continue to use the repeated test.
    let threaded: Vec<Option<(BlockId, BlockId, u64)>> = function
        .blocks
        .iter()
        .enumerate()
        .map(|(source, block)| {
            let Some(Term::Branch {
                cond,
                then_block,
                else_block,
            }) = block.term.as_ref()
            else {
                return None;
            };
            let thread = |target: BlockId, value: bool| {
                if target == source {
                    return None;
                }
                let target_block = function.blocks.get(target)?;
                if !target_block.params.is_empty() || !target_block.insts.is_empty() {
                    return None;
                }
                let Some(Term::Branch {
                    cond: repeated,
                    then_block,
                    else_block,
                }) = target_block.term.as_ref()
                else {
                    return None;
                };
                if repeated != cond {
                    return None;
                }
                let threaded = if value { *then_block } else { *else_block };
                if threaded == source || threaded == target {
                    return None;
                }
                Some(threaded)
            };
            let new_then = thread(*then_block, true).unwrap_or(*then_block);
            let new_else = thread(*else_block, false).unwrap_or(*else_block);
            let changes = u64::from(new_then != *then_block) + u64::from(new_else != *else_block);
            (changes > 0).then_some((new_then, new_else, changes))
        })
        .collect();
    for (block, replacement) in function.blocks.iter_mut().zip(threaded) {
        let Some((then_block, else_block, changes)) = replacement else {
            continue;
        };
        let Some(Term::Branch {
            then_block: current_then,
            else_block: current_else,
            ..
        }) = block.term.as_mut()
        else {
            continue;
        };
        *current_then = then_block;
        *current_else = else_block;
        applied += changes;
    }

    PassResult::applied(applied)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiling::mir::build::BlockData;

    #[test]
    fn constant_branch_becomes_goto() {
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "branch".into(),
            arity: 0,
            locals: crate::compiling::mir::build::LocalInfo::uniform(1),
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
                frame_sites: Default::default(),
                param_reprs: Vec::new(),
                return_repr: None,
                name: "bool_branch".into(),
                arity: 1,
                locals: crate::compiling::mir::build::LocalInfo::uniform(2),
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
    fn threads_true_and_false_edges_through_repeated_tests() {
        let terminal = || BlockData {
            params: Vec::new(),
            insts: Vec::new(),
            term: Some(Term::Return(Operand::Const(Constant::Unit))),
        };
        let repeated = |then_block, else_block| BlockData {
            params: Vec::new(),
            insts: Vec::new(),
            term: Some(Term::Branch {
                cond: Operand::Local(0),
                then_block,
                else_block,
            }),
        };
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "thread_branches".into(),
            arity: 1,
            locals: crate::compiling::mir::build::LocalInfo::uniform(1),
            blocks: vec![
                repeated(1, 2),
                repeated(3, 4),
                repeated(5, 6),
                terminal(),
                terminal(),
                terminal(),
                terminal(),
            ],
        };

        assert_eq!(run(&mut function).applied, 2);
        assert!(matches!(
            function.blocks[0].term,
            Some(Term::Branch {
                then_block: 3,
                else_block: 6,
                ..
            })
        ));
    }

    #[test]
    fn threading_one_incoming_edge_preserves_other_predecessors() {
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "shared_branch".into(),
            arity: 1,
            locals: crate::compiling::mir::build::LocalInfo::uniform(1),
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Branch {
                        cond: Operand::Local(0),
                        then_block: 3,
                        else_block: 2,
                    }),
                },
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Goto(2, Vec::new())),
                },
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Branch {
                        cond: Operand::Local(0),
                        then_block: 3,
                        else_block: 4,
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
            Some(Term::Branch { else_block: 4, .. })
        ));
        assert!(matches!(function.blocks[1].term, Some(Term::Goto(2, _))));
        assert!(matches!(function.blocks[2].term, Some(Term::Branch { .. })));
    }

    #[test]
    fn does_not_thread_instructionful_parameterized_or_cyclic_blocks() {
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "unsafe_threads".into(),
            arity: 1,
            locals: crate::compiling::mir::build::LocalInfo::uniform(2),
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: Vec::new(),
                    term: Some(Term::Branch {
                        cond: Operand::Local(0),
                        then_block: 1,
                        else_block: 2,
                    }),
                },
                BlockData {
                    params: Vec::new(),
                    insts: vec![Inst::Copy {
                        dest: 1,
                        src: Operand::Const(Constant::Unit),
                    }],
                    term: Some(Term::Branch {
                        cond: Operand::Local(0),
                        then_block: 3,
                        else_block: 4,
                    }),
                },
                BlockData {
                    params: vec![1],
                    insts: Vec::new(),
                    term: Some(Term::Branch {
                        cond: Operand::Local(0),
                        then_block: 3,
                        else_block: 4,
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

        function.blocks[0].term = Some(Term::Branch {
            cond: Operand::Local(0),
            then_block: 1,
            else_block: 3,
        });
        function.blocks[1].insts.clear();
        function.blocks[1].term = Some(Term::Branch {
            cond: Operand::Local(1),
            then_block: 3,
            else_block: 4,
        });
        assert_eq!(run(&mut function).applied, 0);

        function.blocks[0].term = Some(Term::Branch {
            cond: Operand::Local(0),
            then_block: 3,
            else_block: 2,
        });
        function.blocks[2].params.clear();
        function.blocks[2].term = Some(Term::Branch {
            cond: Operand::Local(0),
            then_block: 3,
            else_block: 0,
        });
        assert_eq!(run(&mut function).applied, 0);
    }

    #[test]
    fn threads_after_boolean_comparison_target_inversion() {
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "inverted_thread".into(),
            arity: 1,
            locals: crate::compiling::mir::build::LocalInfo::uniform(2),
            blocks: vec![
                BlockData {
                    params: Vec::new(),
                    insts: vec![Inst::Scalar {
                        dest: 1,
                        op: ScalarOp::BoolCmp(CmpKind::Eq),
                        a: Operand::Local(0),
                        b: Some(Operand::Const(Constant::Bool(false))),
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
                    term: Some(Term::Branch {
                        cond: Operand::Local(0),
                        then_block: 3,
                        else_block: 4,
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

        assert_eq!(run(&mut function).applied, 2);
        assert!(matches!(
            function.blocks[0].term,
            Some(Term::Branch {
                cond: Operand::Local(0),
                then_block: 3,
                else_block: 1,
            })
        ));
    }

    #[test]
    fn comparison_that_overwrites_its_source_is_not_rewritten() {
        let mut function = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "overwriting_bool_branch".into(),
            arity: 1,
            locals: crate::compiling::mir::build::LocalInfo::uniform(1),
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
