use crate::{
    name_resolution::symbol::Symbol,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        passes::{dependencies_pass::SCCResolved, inference_pass::curry},
        row::Row,
        term_environment::EnvEntry,
        ty::{Level, Ty},
        type_catalog::NominalForm,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, instantiate_ty, unify},
        type_session::{TypeDefKind, TypeSession},
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct Construction {
    pub callee: Ty,
    pub args: Vec<Ty>,
    pub returns: Ty,
    pub type_symbol: Symbol,
    pub span: Span,
    pub cause: ConstraintCause,
}

impl Construction {
    pub fn solve(
        &self,
        session: &mut TypeSession<SCCResolved>,
        level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let Symbol::Type(type_id) = self.type_symbol else {
            todo!()
        };

        let Some(nominal) = session.phase.type_catalog.nominals.get(&type_id).cloned() else {
            return Err(TypeError::TypeNotFound("".into()));
        };

        let NominalForm::Struct {
            initializers,
            properties,
            ..
        } = &nominal.form
        else {
            return Err(TypeError::TypeConstructorNotFound(type_id));
        };

        let Some((_, init_sym)) = initializers.iter().next() else {
            unreachable!("didn't synthesize init");
        };

        let Some(init_entry) = session.term_env.lookup(init_sym).cloned() else {
            unreachable!("didn't synthesize init");
        };

        let (init_ty, inst_subs) = match init_entry {
            EnvEntry::Mono(ty) => (ty, Default::default()),
            EnvEntry::Scheme(s) => {
                s.solver_instantiate(session, level, next_wants, self.span, substitutions)
            }
        };

        let mut row = Row::Empty(TypeDefKind::Struct);
        for (label, ty_sym) in properties {
            let entry = session.term_env.lookup(ty_sym).cloned().ok_or_else(|| {
                TypeError::MemberNotFound(self.returns.clone(), label.to_string())
            })?;

            // Get the *raw* property type (param if generic), then instantiate with inst_subs
            let base_ty = match entry {
                EnvEntry::Mono(t) => t,
                EnvEntry::Scheme(s) => s.ty, // property schemes unlikely, but safe
            };
            let prop_ty = instantiate_ty(base_ty, &inst_subs, level);

            row = Row::Extend {
                row: Box::new(row),
                label: label.clone(),
                ty: prop_ty,
            };
        }

        let instance = Ty::Nominal {
            id: type_id,
            type_args: vec![],
            row: Box::new(row),
        };

        let mut args_with_self = self.args.clone();
        args_with_self.insert(0, instance.clone());

        unify(&self.returns, &instance, substitutions, session)?;
        unify(
            &curry(args_with_self, instance),
            &init_ty,
            substitutions,
            session,
        )
    }
}
