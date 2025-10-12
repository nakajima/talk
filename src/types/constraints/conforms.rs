use std::rc::Rc;

use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    name_resolution::symbol::{ProtocolId, Symbol},
    span::Span,
    types::{
        constraints::constraint::Constraint,
        infer_ty::{InferTy, Level},
        passes::{dependencies_pass::ConformanceRequirement, inference_pass::Meta},
        term_environment::EnvEntry,
        type_catalog::ConformanceKey,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct Conforms {
    pub symbol: Symbol,
    pub protocol_id: ProtocolId,
    pub span: Span,
}

impl Conforms {
    pub fn solve(
        &self,
        session: &mut TypeSession,
        next_wants: &mut Wants,
        _substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let mut conformances = TakeToSlot::new(&mut session.type_catalog.conformances);
        let conformance = conformances
            .get_mut(&ConformanceKey {
                protocol_id: self.protocol_id,
                conforming_id: self.symbol,
            })
            .expect("didn't get conformance");

        let unfulfilled = conformance
            .requirements
            .iter_mut()
            .filter(|(_, s)| matches!(s, ConformanceRequirement::Unfulfilled(_)))
            .collect::<FxHashMap<_, _>>();

        let mut still_unfulfilled = vec![];
        for (label, requirement) in unfulfilled {
            let ConformanceRequirement::Unfulfilled(req_symbol) = requirement else {
                unreachable!()
            };

            let impl_symbol = session
                .lookup_member(&self.symbol, label)
                .expect("didn't get member impl symbol");

            let Some(protocol_entry) = session.lookup(req_symbol) else {
                // We don't have our protocol typed yet
                tracing::trace!("didn't get {label} requirement entry");
                next_wants.push(Constraint::Conforms(self.clone()));
                return Ok(false);
            };

            let Some(entry) = session.lookup(&impl_symbol) else {
                tracing::trace!("didn't get {label} impl entry");
                still_unfulfilled.push(label);
                continue;
            };

            tracing::trace!("checking {label} conformance: {protocol_entry:?} <> {entry:?}");

            if self.check_method_satisfaction(
                &protocol_entry,
                &entry,
                session.meta_levels.clone(),
                next_wants,
            )? {
                *requirement = ConformanceRequirement::Fulfilled {
                    symbol: impl_symbol,
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

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn check_method_satisfaction(
        &self,
        requirement: &EnvEntry,
        implementation: &EnvEntry,
        meta_levels: FxHashMap<Meta, Level>,
        next_wants: &mut Wants,
    ) -> Result<bool, TypeError> {
        // This is gross. We should just make it easier to generate type vars off something that isn't a whole-ass session.
        let mut session = TypeSession::new(Rc::new(Default::default()));

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
            InferTy::Func(box param, box ret) => {
                // If the parameter is already the correct nominal, keep it;
                // otherwise replace it with the concrete conforming nominal and a fresh row meta.
                let adjusted_param = match param {
                    InferTy::Nominal { symbol, .. } if symbol == self.symbol => param,
                    _ => {
                        let row = session.new_row_meta_var(level);
                        InferTy::Nominal {
                            symbol: self.symbol,
                            row: Box::new(row),
                            type_args: vec![],
                        }
                    }
                };
                InferTy::Func(Box::new(adjusted_param), Box::new(ret))
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
use std::{
    mem,
    ops::{Deref, DerefMut},
    ptr,
};

pub struct TakeToSlot<T> {
    slot_raw_pointer: *mut T,
    stored_value: Option<T>,
}

impl<T: Default> TakeToSlot<T> {
    pub fn new(slot: &mut T) -> Self {
        let value = mem::take(slot); // requires T: Default only here
        Self {
            slot_raw_pointer: slot as *mut T,
            stored_value: Some(value),
        }
    }
}

// Optional: support non-Default T by providing a replacement explicitly
impl<T> TakeToSlot<T> {
    pub fn with_replacement(slot: &mut T, replacement: T) -> Self {
        let value = mem::replace(slot, replacement);
        Self {
            slot_raw_pointer: slot as *mut T,
            stored_value: Some(value),
        }
    }
}

impl<T> Deref for TakeToSlot<T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.stored_value.as_ref().unwrap()
    }
}

impl<T> DerefMut for TakeToSlot<T> {
    fn deref_mut(&mut self) -> &mut T {
        self.stored_value.as_mut().unwrap()
    }
}

impl<T> Drop for TakeToSlot<T> {
    fn drop(&mut self) {
        if let Some(value) = self.stored_value.take() {
            // Move `value` back into the slot, returning and dropping the placeholder in the slot.
            unsafe {
                ptr::replace(self.slot_raw_pointer, value);
            }
        }
    }
}
