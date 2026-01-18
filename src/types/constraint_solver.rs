use crate::{
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
        let mut diagnostics = Vec::default();
        substitutions.extend(&self.context.substitutions);
        while !constraints.is_stalled() {
            let mut solved_metas = vec![];
            let worklist = constraints.worklist();
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
                        constraints.solve(want_id);
                        solved_metas.extend(metas)
                    }
                    SolveResult::Defer(reason) => {
                        constraints.defer(want_id, reason);
                    }
                    SolveResult::Err(e) => {
                        // Check if this constraint is in a non-universal configuration.
                        // If so, record it as an error constraint for resolution phase
                        // rather than immediately failing.
                        let config = constraints
                            .meta
                            .get(&want_id)
                            .map(|m| m.config.clone())
                            .unwrap_or_default();

                        if config.is_universal() {
                            // Universal constraint failed - this is a real error
                            tracing::error!("Error solving constraint: {constraint:?} {e:?}");
                            let diagnostic = AnyDiagnostic::Typing(Diagnostic {
                                id: constraint
                                    .diagnostic_node_id()
                                    .unwrap_or(NodeID::SYNTHESIZED),
                                severity: Severity::Error,
                                kind: e,
                            });
                            diagnostics.push(diagnostic);
                        } else {
                            // Non-universal constraint failed - record for resolution
                            tracing::debug!(
                                "Recording error constraint in config {:?}: {constraint:?} {e:?}",
                                config
                            );
                            session.error_constraints.record(config, e, want_id);
                        }

                        // Mark as solved so we don't keep retrying
                        constraints.solve(want_id);
                    }
                }
            }

            constraints.wake_metas(&solved_metas);
        }

        diagnostics
    }
}
