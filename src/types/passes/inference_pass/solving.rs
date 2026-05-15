use indexmap::IndexSet;

use super::{InferencePass, ProtocolAssociatedTypeRequirements};
use crate::{
    name_resolution::symbol::Symbol,
    types::{
        constraint_solver::ConstraintSolver,
        infer_ty::Ty,
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        solve_context::{SolveContext, SolveContextKind},
        term_environment::EnvEntry,
    },
};

impl InferencePass<'_> {
    pub(super) fn apply_protocol_associated_type_requirements(
        &self,
        entry: EnvEntry,
        requirements: &ProtocolAssociatedTypeRequirements,
    ) -> EnvEntry {
        if requirements.is_empty() {
            return entry;
        }

        match entry {
            EnvEntry::Mono(ty) => {
                let mut foralls: IndexSet<ForAll> = ty.collect_foralls().into_iter().collect();
                for param in &requirements.assoc_params {
                    foralls.insert(ForAll::Ty(*param));
                }

                EnvEntry::Scheme(Scheme {
                    foralls,
                    predicates: requirements.predicates.iter().cloned().collect(),
                    ty,
                })
            }
            EnvEntry::Scheme(mut scheme) => {
                for param in &requirements.assoc_params {
                    scheme.foralls.insert(ForAll::Ty(*param));
                }

                let mut predicates: IndexSet<Predicate> = scheme.predicates.into_iter().collect();
                predicates.extend(requirements.predicates.iter().cloned());
                scheme.predicates = predicates.into_iter().collect();

                EnvEntry::Scheme(scheme)
            }
        }
    }

    pub(super) fn solve(
        &mut self,
        context: &mut SolveContext,
        binders: Vec<Symbol>,
        placeholders: Vec<Ty>,
    ) {
        context.substitutions_mut().extend(&self.substitutions);

        let level = context.level();
        let solver = ConstraintSolver::new(context);
        let diagnostics = solver.solve(
            level,
            &mut self.constraints,
            self.session,
            self.substitutions.clone(),
        );

        self.diagnostics.extend(diagnostics);

        let generalizable = self.constraints.generalizable_for(context);

        let protocol_requirements = match context.kind() {
            SolveContextKind::Protocol { protocol_id, .. } => self
                .protocol_associated_type_requirements
                .get(&protocol_id)
                .cloned(),
            _ => None,
        };

        for (i, binder) in binders.iter().enumerate() {
            let ty = self
                .session
                .apply(&placeholders[i], &mut context.substitutions_mut());
            let entry = self
                .session
                .generalize(ty, context, &generalizable, &mut self.constraints);
            let entry = if let Some(requirements) = &protocol_requirements {
                self.apply_protocol_associated_type_requirements(entry, requirements)
            } else {
                entry
            };
            self.session.promote(*binder, entry, &mut self.constraints);
        }

        self.substitutions.extend(&context.substitutions_mut());
        self.session.apply_all(&mut self.substitutions);
    }
}
