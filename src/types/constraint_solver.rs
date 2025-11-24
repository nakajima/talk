use indexmap::IndexSet;

use crate::{
    ast::AST,
    diagnostic::{AnyDiagnostic, Diagnostic},
    name_resolution::{name_resolver::NameResolved, symbol::Symbol},
    node_id::NodeID,
    types::{
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
    asts: &'a mut [AST<NameResolved>],
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(context: &'a mut SolveContext, asts: &'a mut [AST<NameResolved>]) -> Self {
        Self { context, asts }
    }

    pub fn solve(
        self,
        level: Level,
        constraints: &mut ConstraintStore,
        session: &mut TypeSession,
        mut substitutions: UnificationSubstitutions,
    ) -> IndexSet<Constraint> {
        substitutions.extend(&self.context.substitutions);
        while !constraints.is_stalled() {
            let mut solved_metas = vec![];
            let worklist = constraints.worklist();
            for want_id in worklist {
                let want = constraints.get(&want_id).clone();
                tracing::trace!("solving {want:?}");
                let constraint = want.apply(&mut self.context.substitutions);
                let solution = match constraint {
                    Constraint::Equals(ref equals) => {
                        match unify(&equals.lhs, &equals.rhs, self.context, session) {
                            Ok(metas) => SolveResult::Solved(metas),
                            Err(e) => SolveResult::Err(e),
                        }
                    }
                    Constraint::Call(ref call) => call.solve(constraints, self.context, session),
                    Constraint::HasField(ref has_field) => has_field.solve(level, constraints),
                    Constraint::Member(ref member) => {
                        member.solve(constraints, self.context, session)
                    }
                    Constraint::Conforms(ref conforms) => {
                        conforms.solve(self.context, session, false)
                    }
                    Constraint::TypeMember(ref type_member) => {
                        type_member.solve(constraints, self.context, session, self.asts)
                    }
                    Constraint::Projection(ref projection) => {
                        projection.solve(level, constraints, self.context, session, self.asts)
                    }
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
                        tracing::error!("Error solving constraint: {e:?}");
                        let diagnostic = AnyDiagnostic::Typing(Diagnostic {
                            id: NodeID::SYNTHESIZED,
                            kind: e,
                        });
                        if !self.asts[0].diagnostics.contains(&diagnostic) {
                            tracing::error!("Just adding it to the first constraint. Fixme.");
                            self.asts[0].diagnostics.push(diagnostic);
                        }
                    }
                }
            }

            tracing::trace!("solved: {solved_metas:?}");
            constraints.wake_metas(&solved_metas);
        }

        constraints.take_deferred()
    }
}
