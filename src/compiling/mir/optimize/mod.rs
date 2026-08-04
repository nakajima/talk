//! MIR optimization pipeline.
//!
//! Each coherent optimization owns one file. This module owns pass order and
//! bounded repetition; callers see one optimization seam.

mod branch_fold;
mod constant_fold;
mod dead_code;
mod dead_functions;
mod dead_handlers;
mod forward_calls;
mod inline_small;
mod match_switch;
mod simplify_block_params;
mod unreachable_blocks;

use super::build::{Function, Program};
use super::{OptimizationPassStats, OptimizationStats};

const MAX_SIMPLIFY_ROUNDS: usize = 8;

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct PassResult {
    pub changed: bool,
    pub applied: u64,
}

impl PassResult {
    pub fn unchanged() -> Self {
        Self::default()
    }

    pub fn changed(changed: bool) -> Self {
        Self {
            changed,
            applied: 0,
        }
    }

    pub fn applied(applied: u64) -> Self {
        Self {
            changed: applied > 0,
            applied,
        }
    }

    pub fn include(&mut self, other: Self) {
        self.changed |= other.changed;
        self.applied += other.applied;
    }
}

#[derive(Default)]
struct Counters {
    constant_fold: u64,
    branch_fold: u64,
    dead_code: u64,
    dead_functions: u64,
    dead_handlers: u64,
    forward_calls: u64,
    inline_small: u64,
    match_switch: u64,
    simplify_block_params: u64,
    unreachable_blocks: u64,
}

impl Counters {
    fn finish(self) -> OptimizationStats {
        OptimizationStats {
            passes: vec![
                OptimizationPassStats {
                    name: "constant_fold",
                    applied: self.constant_fold,
                },
                OptimizationPassStats {
                    name: "branch_fold",
                    applied: self.branch_fold,
                },
                OptimizationPassStats {
                    name: "dead_code",
                    applied: self.dead_code,
                },
                OptimizationPassStats {
                    name: "dead_functions",
                    applied: self.dead_functions,
                },
                OptimizationPassStats {
                    name: "dead_handlers",
                    applied: self.dead_handlers,
                },
                OptimizationPassStats {
                    name: "forward_calls",
                    applied: self.forward_calls,
                },
                OptimizationPassStats {
                    name: "inline_small",
                    applied: self.inline_small,
                },
                OptimizationPassStats {
                    name: "match_switch",
                    applied: self.match_switch,
                },
                OptimizationPassStats {
                    name: "simplify_block_params",
                    applied: self.simplify_block_params,
                },
                OptimizationPassStats {
                    name: "unreachable_blocks",
                    applied: self.unreachable_blocks,
                },
            ],
        }
    }
}

fn simplify(function: &mut Function, counters: &mut Counters) {
    for _ in 0..MAX_SIMPLIFY_ROUNDS {
        let constant_fold = constant_fold::run(function);
        counters.constant_fold += constant_fold.applied;
        let branch_fold = branch_fold::run(function);
        counters.branch_fold += branch_fold.applied;
        let match_switch = match_switch::run(function);
        counters.match_switch += match_switch.applied;
        let unreachable_blocks = unreachable_blocks::run(function);
        counters.unreachable_blocks += unreachable_blocks.applied;
        let simplify_block_params = simplify_block_params::run(function);
        counters.simplify_block_params += simplify_block_params.applied;
        let dead_code = dead_code::run(function);
        counters.dead_code += dead_code.applied;

        if !constant_fold.changed
            && !branch_fold.changed
            && !match_switch.changed
            && !unreachable_blocks.changed
            && !simplify_block_params.changed
            && !dead_code.changed
        {
            break;
        }
    }
}

pub(crate) fn run(program: &mut Program) -> OptimizationStats {
    let mut counters = Counters::default();
    for function in &mut program.functions {
        simplify(function, &mut counters);
    }
    counters.forward_calls += forward_calls::run(program).applied;
    counters.inline_small += inline_small::run(program).applied;
    for function in &mut program.functions {
        simplify(function, &mut counters);
    }
    counters.dead_functions += dead_functions::run(program).applied;
    let dead_handlers = dead_handlers::run(program);
    counters.dead_handlers += dead_handlers.applied;
    if dead_handlers.changed {
        for function in &mut program.functions {
            simplify(function, &mut counters);
        }
        counters.dead_functions += dead_functions::run(program).applied;
    }
    counters.finish()
}
