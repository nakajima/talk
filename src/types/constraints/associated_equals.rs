use tracing::instrument;

use crate::{
    name_resolution::symbol::{AssociatedTypeId, ProtocolId},
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
    pub protocol_id: ProtocolId,
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
        let Ty::Nominal {
            id: subject_id,
            row: box subject_row,
            ..
        } = &subject
        else {
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };
        let subject_id = *subject_id;

        // 2) Look up the conformance.
        let key = ConformanceKey {
            protocol_id: self.protocol_id,
            conforming_id: subject_id.into(),
        };
        let Some(conformance) = session.phase.type_catalog.conformances.get(&key) else {
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };

        // 3) Get the associated witness symbol (e.g., the nested type alias symbol).
        let Some(witness_symbol) = conformance.associated_types.get(&self.associated_type_id)
        else {
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };

        // 4) Try to reify the alias parameter from the subject row if possible.
        //    This handles the very common case: `typealias T = A` and a property `let age: A`.
        let mut reified_witness_type: Option<Ty> = None;

        if let Some(EnvEntry::Scheme(scheme)) = session.term_env.lookup(witness_symbol)
            && matches!(scheme.ty, Ty::Param(_))
        {
            // Normalize the subject row so we can read actual field types.
            let (subject_fields, _tail) = normalize_row(subject_row.clone(), substitutions);

            // Load the nominal shape to see declared properties and their types.
            if let Some(nominal) = session.phase.type_catalog.nominals.get(&subject_id.into()) {
                // We only try the struct path here; enums will just fall back.
                if let NominalForm::Struct { properties, .. } = &nominal.form {
                    // Find a property whose declared type mentions the SAME Ty::Param as the alias scheme.ty
                    let alias_param = match &scheme.ty {
                        Ty::Param(p) => *p,
                        _ => unreachable!(),
                    };

                    'scan_props: for (label, property_symbol) in properties {
                        if let Some(property_entry) = session.term_env.lookup(property_symbol) {
                            let declared_property_type = match property_entry {
                                EnvEntry::Mono(t) => t.clone(),
                                EnvEntry::Scheme(s) => s.ty.clone(),
                            };

                            // Quick check: does this property type directly reference that param?
                            let mut mentions_param = false;
                            declared_property_type.fold(&mut |ty| {
                                if let Ty::Param(pid) = ty {
                                    if *pid == alias_param {
                                        mentions_param = true;
                                    }
                                }
                                ty.clone()
                            });

                            if !mentions_param {
                                continue;
                            }

                            // If the subject actually has this field, use its concrete type as the witness.
                            if let Some(actual_field_type) = subject_fields.get(label).cloned() {
                                reified_witness_type = Some(actual_field_type);
                                break 'scan_props;
                            }
                        }
                    }
                }
            }
        }

        // 5) Resolve witness type either from the reified fast-path or via scheme instantiation.
        let witness_type = if let Some(concrete) = reified_witness_type {
            concrete
        } else {
            // Fallback: instantiate the alias as you already did.
            let Some(entry) = session.term_env.lookup(witness_symbol).cloned() else {
                next_wants.push(Constraint::AssociatedEquals(self.clone()));
                return Ok(false);
            };
            match entry {
                EnvEntry::Mono(t) => t,
                EnvEntry::Scheme(s) => {
                    s.solver_instantiate(session, level, next_wants, self.span, substitutions)
                        .0
                }
            }
        };

        // 6) Unify with the expected output.
        unify(
            &apply(witness_type, substitutions),
            &apply(self.output.clone(), substitutions),
            substitutions,
            session,
        )
    }
}
