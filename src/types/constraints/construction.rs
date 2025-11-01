use crate::{
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::InferRow,
        infer_ty::{InferTy, Level},
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, curry, instantiate_ty, unify},
        type_session::{TypeDefKind, TypeSession},
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub struct Construction {
    pub callee_id: NodeID,
    pub callee: InferTy,
    pub args: Vec<InferTy>,
    pub returns: InferTy,
    pub type_symbol: Symbol,
    pub span: Span,
    pub cause: ConstraintCause,
}

impl Construction {
    pub fn solve(
        &self,
        session: &mut TypeSession,
        level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let initializers = session
            .lookup_initializers(&self.type_symbol)
            .unwrap_or_else(|| panic!("didn't get initializers for {:?}", self.type_symbol));

        let properties = session
            .lookup_properties(&self.type_symbol)
            .expect("didn't get properties");

        let Some((_, init_sym)) = initializers.iter().next() else {
            unreachable!("didn't synthesize init");
        };

        let Some(init_entry) = session.lookup(init_sym) else {
            unreachable!("didn't synthesize init");
        };

        let (init_ty, inst_subs) = match init_entry {
            EnvEntry::Mono(ty) => (ty, Default::default()),
            EnvEntry::Scheme(s) => {
                s.instantiate(self.callee_id, session, level, next_wants, self.span)
            }
        };

        let mut row = InferRow::Empty(TypeDefKind::Struct);
        for (label, ty_sym) in properties {
            let entry = session.lookup(&ty_sym).ok_or_else(|| {
                TypeError::MemberNotFound(self.returns.clone(), label.to_string())
            })?;

            // Get the *raw* property type (param if generic), then instantiate with inst_subs
            let base_ty = match entry {
                EnvEntry::Mono(t) => t,
                EnvEntry::Scheme(s) => s.ty, // property schemes unlikely, but safe
            };
            let prop_ty = instantiate_ty(base_ty, &inst_subs, level);

            row = InferRow::Extend {
                row: Box::new(row),
                label: label.clone(),
                ty: prop_ty,
            };
        }

        let instance = InferTy::Nominal {
            symbol: self.type_symbol,
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
