use tracing::instrument;

use crate::{
    name_resolution::symbol::{AssociatedTypeId, TypeId},
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        passes::dependencies_pass::SCCResolved,
        row::normalize_row,
        term_environment::EnvEntry,
        ty::{Level, Ty},
        type_catalog::{ConformanceKey, NominalForm},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct AssociatedEquals {
    pub subject: Ty,
    pub protocol_id: TypeId,
    pub associated_type_id: AssociatedTypeId,
    pub output: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl AssociatedEquals {
    #[instrument(skip(session, substitutions))]
    pub fn solve(
        &self,
        session: &mut TypeSession<SCCResolved>,
        level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        // 1) We only know how to discharge this when the subject is a concrete nominal.
        let subject = apply(self.subject.clone(), substitutions);
        let Ty::Nominal { id: subject_id, .. } = &subject else {
            println!("cannot solve associated equals: {subject:?}");
            // Defer until the subject becomes nominal.
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };
        let subject_id = *subject_id;

        // 2) Look up the conformance for (protocol_id, subject_id).
        let key = ConformanceKey {
            protocol_id: self.protocol_id,
            conforming_id: subject_id,
        };
        let Some(conformance) = session.phase.type_catalog.conformances.get(&key) else {
            // No conformance yet; defer.
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };

        // 3) Find the associated type witness symbol that satisfies `associated_type_id`.
        tracing::debug!(
            "conformance associated_types: {:?}",
            conformance.associated_types
        );
        let Some(witness_sym) = conformance.associated_types.get(&self.associated_type_id) else {
            // The extension/decl did not provide a witness yet; defer.
            tracing::debug!(
                "no witness for associated type {:?}, deferring",
                self.associated_type_id
            );
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };
        tracing::debug!("found witness_sym: {witness_sym:?}");

        // 4) Resolve the witness symbol to a Ty from the term environment.
        //    For typealiases nested in the conforming type we store them in the term env as a Mono.
        let Some(entry) = session.term_env.lookup(witness_sym).cloned() else {
            // If the alias was not lowered yet, try again later.
            tracing::debug!("witness symbol {witness_sym:?} not found in term_env, deferring");
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };

        // 5) Instantiate at this site (respecting current level).
        let witness_ty = match entry {
            EnvEntry::Mono(t) => t,
            EnvEntry::Scheme(s) => {
                s.inference_instantiate(session, level, next_wants, self.span)
                    .0
            }
        };

        // 6) If the witness is a type parameter, we need to find its concrete instantiation
        //    by looking at the subject's row. The row contains concrete types for properties,
        //    and we can map those back to their declared types (which are type parameters).
        let witness_ty = if let Ty::Param(_witness_param_id) = &witness_ty {
            // Build a substitution map from type parameters to concrete types by examining the subject's row
            if let Ty::Nominal { row, .. } = &subject
                && let Some(nominal) = session.phase.type_catalog.nominals.get(&subject_id)
                && let NominalForm::Struct { properties, .. } = &nominal.form
            {
                // Extract concrete types from the row
                let (row_map, _) = normalize_row(*row.clone(), substitutions);

                // For each property, check if its declared type is a type parameter
                // that matches our witness parameter
                for (label, concrete_ty) in row_map {
                    if let Some(prop_sym) = properties.get(&label)
                        && let Some(EnvEntry::Mono(prop_ty)) =
                            session.term_env.lookup(prop_sym).cloned()
                        && let Ty::Param(prop_param_id) = prop_ty
                    {
                        // Both the witness and this property reference type parameters.
                        // They might be the same logical parameter (Person's A) even if they have different IDs.
                        // For now, assume the first type parameter property we find is the one we need.
                        // TODO: This is a simplification - we should match parameters more precisely.
                        tracing::debug!(
                            "found property {label:?} with param {prop_param_id:?}, concrete type {concrete_ty:?}"
                        );
                        return unify(
                            &apply(concrete_ty, substitutions),
                            &apply(self.output.clone(), substitutions),
                            substitutions,
                            session,
                        );
                    }
                }
            }
            witness_ty
        } else {
            witness_ty
        };

        tracing::debug!(
            "unifying witness_ty {witness_ty:?} with output {:?}",
            self.output
        );

        // 7) Finally, unify with `output`.
        unify(
            &apply(witness_ty, substitutions),
            &apply(self.output.clone(), substitutions),
            substitutions,
            session,
        )
    }
}
