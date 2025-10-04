use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    name_resolution::symbol::{ProtocolId, TypeId},
    span::Span,
    types::{
        constraints::constraint::Constraint,
        passes::{
            dependencies_pass::{ConformanceRequirement, SCCResolved},
            inference_pass::Meta,
        },
        term_environment::EnvEntry,
        ty::{Level, Ty},
        type_catalog::ConformanceKey,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct Conforms {
    pub type_id: TypeId,
    pub protocol_id: ProtocolId,
    pub span: Span,
}

impl Conforms {
    pub fn solve(
        &self,
        session: &mut TypeSession<SCCResolved>,
        next_wants: &mut Wants,
        _substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let conformance = session
            .phase
            .type_catalog
            .conformances
            .get_mut(&ConformanceKey {
                protocol_id: self.protocol_id,
                conforming_id: self.type_id.into(),
            })
            .expect("didn't get conformance");

        let unfulfilled = conformance
            .requirements
            .iter_mut()
            .filter(|(_, s)| matches!(s, ConformanceRequirement::Unfulfilled(_)))
            .collect::<FxHashMap<_, _>>();

        let nominal = session
            .phase
            .type_catalog
            .nominals
            .get(&self.type_id.into())
            .expect("didn't get nominal for conformance");

        let mut still_unfulfilled = vec![];
        for (label, requirement) in unfulfilled {
            let ConformanceRequirement::Unfulfilled(req_symbol) = requirement else {
                unreachable!()
            };

            let impl_symbol = nominal
                .member_symbol(label)
                .expect("didn't get member impl symbol");

            let Some(protocol_entry) = session.term_env.lookup(req_symbol) else {
                // We don't have our protocol typed yet
                tracing::trace!("didn't get {label} requirement entry");
                next_wants.push(Constraint::Conforms(self.clone()));
                return Ok(false);
            };

            let Some(entry) = session.term_env.lookup(impl_symbol) else {
                tracing::trace!("didn't get {label} impl entry");
                still_unfulfilled.push(label);
                continue;
            };

            tracing::trace!("checking {label} conformance: {protocol_entry:?} <> {entry:?}");

            if self.check_method_satisfaction(
                protocol_entry,
                entry,
                session.meta_levels.clone(),
                next_wants,
            )? {
                *requirement = ConformanceRequirement::Fulfilled {
                    symbol: *impl_symbol,
                }
            } else {
                still_unfulfilled.push(label)
            }
        }

        if still_unfulfilled.is_empty() {
            Ok(true)
        } else {
            next_wants.push(Constraint::Conforms(self.clone()));
            Ok(false)
        }
    }

    #[instrument(skip(self))]
    fn check_method_satisfaction(
        &self,
        requirement: &EnvEntry,
        implementation: &EnvEntry,
        meta_levels: FxHashMap<Meta, Level>,
        next_wants: &mut Wants,
    ) -> Result<bool, TypeError> {
        // This is gross. We should just make it easier to generate type vars off something that isn't a whole-ass session.
        let mut session = TypeSession::<SCCResolved> {
            vars: Default::default(),
            synthsized_ids: Default::default(),
            skolem_map: Default::default(),
            phase: SCCResolved {
                graph: Default::default(),
                annotation_map: Default::default(),
                rhs_map: Default::default(),
                type_catalog: Default::default(),
            },
            term_env: Default::default(),
            meta_levels,
            skolem_bounds: Default::default(),
            type_param_bounds: Default::default(),
            types_by_node: Default::default(),
            typealiases: Default::default(),
        };

        // Instantiate both at the same level
        let level = Level(999); // High level so nothing escapes

        // Use a temporary Wants that we discard - we're just checking unification, not solving constraints
        let mut temp_wants = Wants::default();

        let req_ty = match requirement {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(s) => {
                s.inference_instantiate(&mut session, level, &mut temp_wants, self.span)
                    .0
            }
        };

        let impl_ty = match implementation {
            EnvEntry::Mono(ty) => ty.clone(),
            EnvEntry::Scheme(s) => {
                s.inference_instantiate(&mut session, level, &mut temp_wants, self.span)
                    .0
            }
        };

        let req_ty = match req_ty {
            Ty::Func(box param, box ret) => {
                // If the parameter is already the correct nominal, keep it;
                // otherwise replace it with the concrete conforming nominal and a fresh row meta.
                let adjusted_param = match param {
                    Ty::Nominal { id, .. } if id == self.type_id => param,
                    _ => {
                        let row = session.new_row_meta_var(level);
                        Ty::Nominal {
                            id: self.type_id,
                            row: Box::new(row),
                            type_args: vec![],
                        }
                    }
                };
                Ty::Func(Box::new(adjusted_param), Box::new(ret))
            }
            other => other,
        };

        // Try to unify in a sandbox
        let mut temp_subs = UnificationSubstitutions::new(session.meta_levels.clone());
        match unify(&req_ty, &impl_ty, &mut temp_subs, &mut session) {
            Ok(_) => Ok(true),
            Err(_) => Ok(false), // Don't propagate error, just say "doesn't conform"
        }
    }
}
