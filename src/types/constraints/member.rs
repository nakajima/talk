use crate::{
    label::Label,
    span::Span,
    types::{
        constraint::{Constraint, ConstraintCause},
        passes::{dependencies_pass::SCCResolved, inference_pass::curry},
        row::Row,
        term_environment::EnvEntry,
        ty::{Level, Primitive, Ty},
        type_catalog::NominalForm,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, unify},
        type_session::{TypeDefKind, TypeSession},
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct Member {
    pub receiver: Ty,
    pub label: Label,
    pub ty: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl Member {
    pub fn solve(
        &self,
        session: &mut TypeSession<SCCResolved>,
        level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let receiver = apply(self.receiver.clone(), substitutions);
        let ty = apply(self.ty.clone(), substitutions);

        if matches!(receiver, Ty::UnificationVar { .. }) {
            // If we don't know what the receiver is yet, we can't do much
            next_wants.push(Constraint::Member(self.clone()));
            return Ok(false);
        }

        if let Ty::Nominal { id: type_id, .. } = &receiver
            && let Some(nominal) = session.phase.type_catalog.nominals.get(type_id).cloned()
            && let Some(sym) = nominal.member_symbol(&self.label)
            && let Some(entry) = session.term_env.lookup(sym).cloned()
        {
            match &nominal.form {
                NominalForm::Struct { .. } => {
                    // EXISTING method logic (strip self, etc.)
                    let method_ty = entry.solver_instantiate(
                        session,
                        Level(1),
                        substitutions,
                        next_wants,
                        self.span,
                    );

                    let applied_method_ty = if let Ty::Func(param, rest) = method_ty {
                        unify(&receiver, &param, substitutions, &mut session.vars)?;
                        if !matches!(*rest, Ty::Func(..)) {
                            Ty::Func(Box::new(Ty::Void), rest)
                        } else {
                            *rest
                        }
                    } else {
                        unreachable!()
                    };

                    return unify(&ty, &applied_method_ty, substitutions, &mut session.vars);
                }

                NominalForm::Enum { variants, .. } => {
                    // Variant constructor: build (payload) -> Fizz{ all variants }
                    // 1) payload type is what resolve_variants stored under the variant symbol:
                    let payload_ty = entry.solver_instantiate(
                        session,
                        Level(1),
                        substitutions,
                        next_wants,
                        self.span,
                    );

                    if let Ty::Func(param, rest) = payload_ty {
                        // It's an instance method on the enum. Strip `self` like struct methods.
                        unify(&receiver, &param, substitutions, &mut session.vars)?;
                        let applied = if !matches!(*rest, Ty::Func(..)) {
                            Ty::Func(Box::new(Ty::Void), rest)
                        } else {
                            *rest
                        };
                        return unify(&ty, &applied, substitutions, &mut session.vars);
                    }

                    // 2) build the CLOSED enum row from the catalog (all variants):
                    let mut row = Row::Empty(TypeDefKind::Enum);
                    // iter in reverse to produce left-extended row
                    for (label, sym) in variants.iter() {
                        let vty = match session
                            .term_env
                            .lookup(sym)
                            .expect("variant missing")
                            .clone()
                        {
                            EnvEntry::Mono(t) => t,
                            EnvEntry::Scheme(s) => s.ty, // should be Mono in your setup
                        };
                        row = Row::Extend {
                            row: Box::new(row),
                            label: label.clone(),
                            ty: vty,
                        };
                    }

                    let result_enum = Ty::Nominal {
                        id: *type_id,
                        row: Box::new(row),
                    };

                    // 3) constructor function type from payload to enum result:
                    let ctor_ty = match &payload_ty {
                        // No payload → the member *is a value* of the enum type
                        Ty::Primitive(Primitive::Void) => result_enum.clone(),
                        Ty::Tuple(items) if items.is_empty() => result_enum.clone(),

                        // One argument → simple function
                        Ty::Tuple(items) if items.len() == 1 => {
                            Ty::Func(Box::new(items[0].clone()), Box::new(result_enum.clone()))
                        }

                        // Multiple arguments packed in a tuple → curry them
                        Ty::Tuple(items) => curry(items.clone(), result_enum.clone()),

                        // Single non-tuple payload
                        other => Ty::Func(Box::new(other.clone()), Box::new(result_enum.clone())),
                    };

                    return unify(&ty, &ctor_ty, substitutions, &mut session.vars);
                }
            }
        }

        // If it's not a method, figure out the row and emit a has field constraint
        let (Ty::Record(row) | Ty::Nominal { row, .. }) = receiver else {
            return Err(TypeError::ExpectedRow(receiver));
        };

        next_wants._has_field(
            *row,
            self.label.clone(),
            self.ty.clone(),
            self.cause,
            self.span,
        );

        Ok(true)
    }
}
