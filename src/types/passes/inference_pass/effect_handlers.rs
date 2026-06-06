use super::{HandlerContext, InferencePass, TypedRet};
use crate::{
    name::Name,
    node_kinds::{block::Block, stmt::Stmt},
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::Row,
        passes::uncurry_function,
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::curry,
        typed_ast::{TypedFunc, TypedStmt, TypedStmtKind},
    },
};

impl InferencePass<'_> {
    pub(super) fn visit_handler_stmt(
        &mut self,
        expr: &Stmt,
        effect_name: &Name,
        body: &Block,
        context: &mut SolveContext,
    ) -> TypedRet<TypedStmt> {
        let effect_symbol = effect_name
            .symbol()
            .map_err(|_| TypeError::NameNotResolved(effect_name.clone()))?;

        let Some(effect) = self.session.lookup_effect(&effect_symbol) else {
            return Err(TypeError::EffectNotFound(effect_name.name_str()));
        };

        let handler_symbol = self
            .session
            .resolved_names
            .effect_handler_definitions
            .get(&expr.id)
            .copied()
            .ok_or_else(|| {
                TypeError::TypeNotFound(format!(
                    "Effect handler symbol not found for {:?}",
                    effect_name
                ))
            })?;

        let typed_params = self.visit_params(&body.args, context)?;
        let (_, effect_ret, _effects_row) = uncurry_function(effect.clone());

        self.handler_contexts
            .push(HandlerContext { ret: effect_ret });
        let typed_body = self.infer_block_with_returns(body, context);
        self.handler_contexts.pop();
        let typed_body = typed_body?;

        // Track that this effect is now handled for subsequent calls in this scope
        self.handled_effects.insert(effect_symbol);

        let body_func = curry(
            typed_params.iter().map(|p| p.ty.clone()),
            typed_body.ret.clone(),
            self.session.new_row_meta_var(context.level()).into(),
        );

        self.constraints.wants_equals_at_with_cause(
            expr.id,
            effect.clone(),
            body_func,
            &context.group_info(),
            Some(ConstraintCause::Internal),
        );

        self.session.insert(
            handler_symbol,
            curry(
                typed_params.iter().map(|p| p.ty.clone()),
                typed_body.ret.clone(),
                Row::Empty.into(),
            ),
            &mut Default::default(),
        );

        Ok(TypedStmt {
            id: expr.id,
            ty: effect.clone(),
            kind: TypedStmtKind::Handler {
                effect: effect_symbol,
                func: TypedFunc {
                    name: handler_symbol,
                    foralls: Default::default(),
                    params: typed_params,
                    effects: Default::default(),
                    effects_row: Row::Empty,
                    ret: typed_body.ret.clone(),
                    body: typed_body,
                },
            },
        })
    }
}
