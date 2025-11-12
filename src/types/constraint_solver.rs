use indexmap::IndexSet;

use crate::{
    ast::AST,
    diagnostic::{AnyDiagnostic, Diagnostic},
    name_resolution::name_resolver::NameResolved,
    types::{
        constraints::constraint::Constraint, solve_context::SolveContext, type_operations::unify,
        type_session::TypeSession,
    },
};

pub struct ConstraintSolver<'a> {
    context: &'a mut SolveContext,
    ast: &'a mut AST<NameResolved>,
    unsolved: IndexSet<Constraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(context: &'a mut SolveContext, ast: &'a mut AST<NameResolved>) -> Self {
        Self {
            context,
            unsolved: Default::default(),
            ast,
        }
    }

    pub fn solve(mut self, session: &mut TypeSession) -> IndexSet<Constraint> {
        let mut remaining_attempts = 5;
        while remaining_attempts >= 0 {
            let mut made_progress = false;

            for unsolved in std::mem::take(&mut self.unsolved) {
                self.context.wants.push(unsolved);
            }

            let mut wants = std::mem::take(&mut self.context.wants);

            while let Some(want) = wants.pop()
                && remaining_attempts >= 0
            {
                tracing::trace!("solving {want:?}");
                let constraint = want.apply(&mut self.context.substitutions);
                let solution = match constraint {
                    Constraint::Equals(ref equals) => {
                        unify(&equals.lhs, &equals.rhs, self.context, session)
                    }
                    Constraint::Call(ref call) => call.solve(self.context, session),
                    Constraint::HasField(ref has_field) => has_field.solve(self.context),
                    Constraint::Member(ref member) => member.solve(self.context, session),
                    Constraint::Conforms(ref conforms) => conforms.solve(self.context),
                    Constraint::TypeMember(ref type_member) => {
                        type_member.solve(self.context, session, self.ast)
                    }
                    Constraint::Projection(ref projection) => {
                        projection.solve(self.ast, self.context, session)
                    }
                };

                match solution {
                    Ok(true) => {
                        made_progress |= true;
                    } // We're good
                    Ok(false) => {
                        self.unsolved.insert(constraint);
                    }
                    Err(e) => {
                        tracing::error!("Error solving constraint: {e:?}");
                        let diagnostic = AnyDiagnostic::Typing(Diagnostic {
                            span: constraint.span(),
                            kind: e,
                        });
                        if !self.ast.diagnostics.contains(&diagnostic) {
                            self.ast.diagnostics.push(diagnostic);
                        }
                    }
                }
            }

            if !made_progress {
                remaining_attempts -= 1;
            }

            if self.context.wants.is_empty() {
                tracing::trace!("no more wants found, breaking");
                break;
            }

            if remaining_attempts == 0 {
                tracing::warn!("did not make forward progress, moving on.");
            }
        }

        self.unsolved
    }
}
