use crate::{
    ast::AST,
    diagnostic::{AnyDiagnostic, Diagnostic},
    name_resolution::name_resolver::NameResolved,
    types::{
        constraints::constraint::Constraint,
        infer_ty::Level,
        type_operations::{UnificationSubstitutions, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

pub struct ConstraintSolver<'a> {
    wants: Wants,
    substitutions: UnificationSubstitutions,
    session: &'a mut TypeSession,
    ast: &'a mut AST<NameResolved>,
    level: Level,
    unsolved: Vec<Constraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(
        wants: Wants,
        level: Level,
        session: &'a mut TypeSession,
        ast: &'a mut AST<NameResolved>,
    ) -> Self {
        Self {
            wants,
            substitutions: UnificationSubstitutions::new(session.meta_levels.clone()),
            session,
            level,
            unsolved: Default::default(),
            ast,
        }
    }

    pub fn solve(mut self) -> (UnificationSubstitutions, Vec<Constraint>) {
        let mut remaining_attempts = 5;
        while remaining_attempts >= 0 {
            let mut next_wants = Wants::default();
            while let Some(want) = self.wants.pop() {
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
                    Ok(true) => (), // We're good
                    Ok(false) => {
                        self.unsolved.push(constraint);
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

            // Add any new constraints generated during solving
            self.wants.extend(next_wants);
            remaining_attempts -= 1;
        }

        (self.substitutions, self.unsolved)
    }
}
