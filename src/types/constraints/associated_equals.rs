//SLOPFILE

use tracing::instrument;

use crate::{
    name_resolution::symbol::{AssociatedTypeId, ProtocolId},
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_row::normalize_row,
        infer_ty::{InferTy, Level},
        term_environment::EnvEntry,
        type_catalog::ConformanceKey,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct AssociatedEquals {
    pub subject: InferTy,
    pub protocol_id: ProtocolId,
    pub associated_type_id: AssociatedTypeId,
    pub output: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl AssociatedEquals {
    #[instrument(skip(session, substitutions))]
    pub fn solve(
        &self,
        session: &mut TypeSession,
        level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let subject = apply(self.subject.clone(), substitutions);
        let InferTy::Nominal {
            symbol: subject_id,
            row: box subject_row,
            ..
        } = &subject
        else {
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };
        let subject_id = *subject_id;

        let key = ConformanceKey {
            protocol_id: self.protocol_id,
            conforming_id: subject_id,
        };
        let Some(conformance) = session.type_catalog.conformances.get(&key).cloned() else {
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };

        let Some(witness_symbol) = conformance.associated_types.get(&self.associated_type_id)
        else {
            next_wants.push(Constraint::AssociatedEquals(self.clone()));
            return Ok(false);
        };

        let mut reified_witness_type: Option<InferTy> = None;

        if let Some(EnvEntry::Scheme(scheme)) = session.lookup(witness_symbol)
            && matches!(scheme.ty, InferTy::Param(_))
        {
            let (subject_fields, _tail) = normalize_row(subject_row.clone(), substitutions);

            if let Some(properties) = session.type_catalog.properties.get(&subject_id).cloned() {
                let alias_param = match &scheme.ty {
                    InferTy::Param(p) => *p,
                    _ => unreachable!(),
                };

                'scan_props: for (label, property_symbol) in properties {
                    if let Some(property_entry) = session.lookup(&property_symbol) {
                        let declared_property_type = match property_entry {
                            EnvEntry::Mono(t) => t.clone(),
                            EnvEntry::Scheme(s) => s.ty.clone(),
                        };

                        let mut mentions_param = false;
                        declared_property_type.fold(&mut |ty| {
                            if let InferTy::Param(pid) = ty
                                && *pid == alias_param
                            {
                                mentions_param = true;
                            }
                            ty.clone()
                        });

                        if !mentions_param {
                            continue;
                        }

                        if let Some(actual_field_type) = subject_fields.get(&label).cloned() {
                            reified_witness_type = Some(actual_field_type);
                            break 'scan_props;
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
            let Some(entry) = session.lookup(witness_symbol) else {
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
