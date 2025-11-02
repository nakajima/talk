use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic},
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
    level: Level,
    unsolved: Vec<Constraint>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(wants: Wants, level: Level, session: &'a mut TypeSession) -> Self {
        Self {
            wants,
            substitutions: UnificationSubstitutions::new(session.meta_levels.clone()),
            session,
            level,
            unsolved: Default::default(),
        }
    }

    pub fn solve(mut self) -> UnificationSubstitutions {
        let mut remaining_attempts = 5;
        while remaining_attempts >= 0 {
            let mut next_wants = Wants::default();
            while let Some(want) = self.wants.pop() {
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
                    Constraint::Construction(construction) => todo!(),
                    Constraint::Conforms(ref conforms) => {
                        conforms.solve(self.session, &mut next_wants, &mut self.substitutions)
                    }
                    Constraint::AssociatedEquals(associated_equals) => todo!(),
                    Constraint::TypeMember(type_member) => todo!(),
                };

                match solution {
                    Ok(true) => (), // We're good
                    Ok(false) => {
                        self.unsolved.push(constraint);
                    }
                    Err(e) => {
                        tracing::error!("Error solving constraint: {e:?}");
                        // let file_id = if self.asts.len() >= constraint.span().file_id.0 as usize {
                        //     constraint.span().file_id.0 as usize
                        // } else {
                        //     self.asts.len() - 1
                        // };
                        // let diagnostic = AnyDiagnostic::Typing(Diagnostic {
                        //     span: constraint.span(),
                        //     kind: e,
                        // });
                        // if !self.asts[file_id].diagnostics.contains(&diagnostic) {
                        //     self.asts[file_id].diagnostics.push(diagnostic);
                        // }
                    }
                }

                // Add any new constraints generated during solving
            }

            self.wants.extend(next_wants);
            remaining_attempts -= 1;
        }

        self.substitutions
    }
}
