use crate::{
    common::metrics,
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        conformance::ConformanceKey,
        constraints::{constraint::Constraint, store::ConstraintStore},
        infer_ty::{Level, Meta},
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, unify},
        type_session::TypeSession,
    },
};

#[derive(Debug, PartialEq)]
pub enum DeferralReason {
    WaitingOnMeta(Meta),
    WaitingOnSymbol(Symbol),
    WaitingOnSymbols(Vec<Symbol>),
    WaitingOnConformance(ConformanceKey),
    Multi(Vec<DeferralReason>),
    Unknown,
}

#[derive(Debug, PartialEq)]
pub enum SolveResult {
    Solved(Vec<Meta>),
    Defer(DeferralReason),
    Err(TypeError),
}

#[derive(Debug)]
pub struct ConstraintSolver<'a> {
    context: &'a mut SolveContext,
}

#[cfg(feature = "metrics")]
#[derive(Default)]
struct ConstraintSolverMetrics {
    iterations: u64,
    processed: u64,
    solved: u64,
    deferred: u64,
    errors: u64,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(context: &'a mut SolveContext) -> Self {
        Self { context }
    }

    pub fn solve(
        self,
        level: Level,
        constraints: &mut ConstraintStore,
        session: &mut TypeSession,
        mut substitutions: UnificationSubstitutions,
    ) -> Vec<AnyDiagnostic> {
        let _timer = metrics::timer("typecheck.constraints.solve");
        #[cfg(feature = "metrics")]
        let mut metrics = ConstraintSolverMetrics::default();
        let mut diagnostics = Vec::default();
        substitutions.extend(&self.context.substitutions);
        while !constraints.is_stalled() {
            #[cfg(feature = "metrics")]
            {
                metrics.iterations += 1;
            }
            let mut solved_metas = vec![];
            let worklist = constraints.worklist();
            #[cfg(feature = "metrics")]
            {
                metrics.processed += worklist.len() as u64;
            }
            for want_id in worklist {
                let want = constraints.get(&want_id).clone();
                let constraint = want.apply(&mut self.context.substitutions, session);
                let solution = match constraint {
                    Constraint::DefaultTy(ref c) => c.solve(self.context, session),
                    Constraint::Equals(ref equals) => {
                        match unify(&equals.lhs, &equals.rhs, self.context, session) {
                            Ok(metas) => SolveResult::Solved(metas),
                            Err(e) => SolveResult::Err(e.with_optional_cause(equals.cause)),
                        }
                    }
                    Constraint::Call(ref call) => call.solve(constraints, self.context, session),
                    Constraint::HasField(ref has_field) => {
                        has_field.solve(constraints, self.context, session)
                    }
                    Constraint::Member(ref member) => {
                        member.solve(constraints, self.context, session)
                    }
                    Constraint::Conforms(ref conforms) => {
                        conforms.solve(constraints, self.context, session)
                    }
                    Constraint::TypeMember(ref type_member) => {
                        type_member.solve(constraints, self.context, session)
                    }
                    Constraint::Projection(ref projection) => {
                        projection.solve(level, constraints, self.context, session)
                    }
                    Constraint::RowSubset(ref c) => c.solve(constraints, self.context, session),
                };

                match solution {
                    SolveResult::Solved(metas) => {
                        #[cfg(feature = "metrics")]
                        {
                            metrics.solved += 1;
                        }
                        constraints.solve(want_id);
                        solved_metas.extend(metas)
                    }
                    SolveResult::Defer(reason) => {
                        #[cfg(feature = "metrics")]
                        {
                            metrics.deferred += 1;
                        }
                        constraints.defer(want_id, reason);
                    }
                    SolveResult::Err(e) => {
                        #[cfg(feature = "metrics")]
                        {
                            metrics.errors += 1;
                        }
                        tracing::error!("Error solving constraint: {constraint:?} {e:?}");
                        //unimplemented!("Error solving constraint: {constraint:?} {e:?}");
                        let diagnostic = AnyDiagnostic::Typing(Diagnostic {
                            id: constraint
                                .diagnostic_node_id()
                                .unwrap_or(NodeID::SYNTHESIZED),
                            severity: Severity::Error,
                            kind: e,
                        });

                        diagnostics.push(diagnostic);
                    }
                }
            }

            constraints.wake_metas(&solved_metas);
        }

        #[cfg(feature = "metrics")]
        {
            let store_metrics = constraints.metrics_snapshot();
            tracing::info!(
                target: "metrics",
                metric = "typecheck.constraints",
                iterations = metrics.iterations,
                processed = metrics.processed,
                solved = metrics.solved,
                deferred = metrics.deferred,
                errors = metrics.errors,
                created = store_metrics.created,
                store_solved = store_metrics.solved,
                store_deferred = store_metrics.deferred,
                woken = store_metrics.woken,
                woken_metas = store_metrics.woken_metas,
                woken_symbols = store_metrics.woken_symbols,
                woken_conformances = store_metrics.woken_conformances,
                unsolved = constraints.unsolved().len() as u64
            );
        }

        diagnostics
    }
}
