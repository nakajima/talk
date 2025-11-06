use indexmap::IndexSet;

use crate::{
    ast::AST,
    diagnostic::{AnyDiagnostic, Diagnostic},
    name_resolution::name_resolver::NameResolved,
    types::{
        constraints::constraint::Constraint,
        infer_ty::{InferTy, Level},
        predicate::Predicate,
        type_operations::{UnificationSubstitutions, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

pub struct ConstraintSolver<'a> {
    wants: Wants,
    givens: &'a IndexSet<Predicate<InferTy>>,
    substitutions: UnificationSubstitutions,
    session: &'a mut TypeSession,
    ast: &'a mut AST<NameResolved>,
    level: Level,
    unsolved: IndexSet<Constraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(
        wants: Wants,
        givens: &'a IndexSet<Predicate<InferTy>>,
        level: Level,
        session: &'a mut TypeSession,
        ast: &'a mut AST<NameResolved>,
    ) -> Self {
        Self {
            wants,
            givens,
            substitutions: UnificationSubstitutions::new(session.meta_levels.clone()),
            session,
            level,
            unsolved: Default::default(),
            ast,
        }
    }

    pub fn solve(mut self) -> (UnificationSubstitutions, IndexSet<Constraint>) {
        let mut remaining_attempts = 5;
        while remaining_attempts >= 0 {
            let mut made_progress = false;
            let mut next_wants = Wants::default();
            while let Some(want) = self.wants.pop()
                && remaining_attempts >= 0
            {
                println!("remaining: {remaining_attempts:?}");
                tracing::trace!("solving {want:?}");
                let constraint = want.apply(&mut self.substitutions);
                let solution = match constraint {
                    Constraint::Equals(ref equals) => unify(
                        &equals.lhs,
                        &equals.rhs,
                        &mut self.substitutions,
                        self.session,
                    ),
                    Constraint::Call(ref call) => {
                        call.solve(self.session, &mut next_wants, &mut self.substitutions)
                    }
                    Constraint::HasField(ref has_field) => has_field.solve(
                        self.session,
                        self.level,
                        &mut next_wants,
                        &mut self.substitutions,
                    ),
                    Constraint::Member(ref member) => member.solve(
                        self.session,
                        self.level,
                        self.givens,
                        &mut next_wants,
                        &mut self.substitutions,
                    ),
                    Constraint::Construction(ref construction) => construction.solve(
                        self.session,
                        self.level,
                        &mut next_wants,
                        &mut self.substitutions,
                    ),
                    Constraint::Conforms(ref conforms) => {
                        conforms.solve(self.session, &mut next_wants, &mut self.substitutions)
                    }
                    Constraint::AssociatedEquals(ref associated_equals) => associated_equals.solve(
                        self.session,
                        self.level,
                        &mut next_wants,
                        &mut self.substitutions,
                    ),
                    Constraint::TypeMember(ref type_member) => type_member.solve(
                        self.session,
                        self.level,
                        &mut next_wants,
                        &mut self.substitutions,
                    ),
                };

                match solution {
                    Ok(true) => {
                        println!("made progress on {constraint:?}");
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

            if next_wants.is_empty() {
                tracing::trace!("no more wants found, breaking");
                break;
            }

            if remaining_attempts == 0 {
                tracing::error!("did not make forward progress!");
            }

            // Add any new constraints generated during solving
            self.wants.extend(next_wants);
        }

        (self.substitutions, self.unsolved)
    }
}
