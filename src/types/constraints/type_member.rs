use crate::{
    ast::AST,
    label::Label,
    name_resolution::name_resolver::NameResolved,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_ty::{InferTy, TypeParamId},
        predicate::Predicate,
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::unify,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeMember {
    pub base: InferTy,
    pub name: Label,
    pub node_id: NodeID,
    pub generics: Vec<InferTy>,
    pub result: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl TypeMember {
    pub fn solve(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
        ast: &AST<NameResolved>,
    ) -> Result<bool, TypeError> {
        match &self.base {
            InferTy::Var { .. } => todo!(),
            InferTy::Param(type_param_id) => {
                self.lookup_for_type_param(context, session, ast, *type_param_id)
            }
            InferTy::Rigid(skolem_id) => {
                let Some(InferTy::Param(type_param_id)) =
                    session.skolem_map.get(&InferTy::Rigid(*skolem_id))
                else {
                    unreachable!();
                };

                self.lookup_for_type_param(context, session, ast, *type_param_id)
            }
            InferTy::Constructor { .. } => todo!(),
            InferTy::Nominal { .. } => todo!(),
            _ => Err(TypeError::TypeNotFound(format!(
                "Could not find child type {:?} for {:?}",
                self.name, self.base
            ))),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lookup_for_type_param(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
        ast: &AST<NameResolved>,
        type_param_id: TypeParamId,
    ) -> Result<bool, TypeError> {
        let mut candidates = vec![];
        for given in &context.givens {
            if let Predicate::Conforms {
                param, protocol_id, ..
            } = given
                && param == &type_param_id
            {
                candidates.push(protocol_id);
            };
        }

        for candidate in candidates {
            if let Some(child_types) = ast.phase.child_types.get(&candidate.into())
                && let Some(child_sym) = child_types.get(&self.name)
            {
                let child_entry = session.lookup(child_sym).unwrap();
                let child_ty = child_entry.instantiate(self.node_id, context, session, self.span);
                println!("child_ty: {child_ty:?}");
                return unify(&child_ty, &self.result, context, session);
            }
        }

        Ok(false)
    }
}
