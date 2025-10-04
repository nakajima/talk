use crate::{
    name_resolution::symbol::Symbol,
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        passes::inference_pass::curry,
        term_environment::EnvEntry,
        ty::{Level, Ty},
        type_catalog::NominalForm,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct Call {
    pub callee: Ty,
    pub args: Vec<Ty>,
    pub returns: Ty,
    pub receiver: Option<Ty>, // If it's a method
    pub span: Span,
    pub cause: ConstraintCause,
}

impl Call {
    pub fn solve(
        &self,
        session: &mut TypeSession,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        if matches!(&self.callee, Ty::UnificationVar { .. }) {
            tracing::trace!(
                "unable to determine callee type: {:?}, substitutions: {substitutions:?}",
                self.callee
            );
            // We don't know the callee yet, defer
            next_wants.push(Constraint::Call(self.clone()));
            return Ok(false);
        }

        let mut args = self.args.to_vec();

        if let Some(receiver) = &self.receiver
            && !matches!(receiver, Ty::Constructor { .. })
        {
            args.insert(0, receiver.clone());
        }

        match &self.callee {
            Ty::Constructor { type_id: id, .. } => {
                let Some(nominal) = session.type_catalog.nominals.get(&id.into()) else {
                    panic!("type not found in catalog");
                };

                let init_ty = match &nominal.form {
                    NominalForm::Struct { initializers, .. } => {
                        let ctor_sym = initializers
                            .values()
                            .next()
                            .copied()
                            .expect("struct must have an initializer symbol");
                        let entry = session
                            .term_env
                            .lookup(&ctor_sym)
                            .cloned()
                            .expect("constructor scheme missing");
                        entry.inference_instantiate(session, Level(1), next_wants, self.span)
                    }
                    NominalForm::Enum { .. } => {
                        match session
                            .term_env
                            .lookup(&Symbol::Type(*id))
                            .cloned()
                            .expect("enum type missing from env")
                        {
                            EnvEntry::Mono(ty) => ty,
                            EnvEntry::Scheme(s) => s.ty.clone(),
                        }
                    }
                };
                unify(
                    &init_ty,
                    &curry(args, self.returns.clone()),
                    substitutions,
                    session,
                )
            }
            Ty::Func(..) => {
                if args.is_empty() {
                    unify(
                        &self.callee,
                        &Ty::Func(Ty::Void.into(), self.returns.clone().into()),
                        substitutions,
                        session,
                    )
                } else {
                    unify(
                        &self.callee,
                        &curry(args, self.returns.clone()),
                        substitutions,
                        session,
                    )
                }
            }
            ty => Err(TypeError::CalleeNotCallable(ty.clone())),
        }
    }
}
