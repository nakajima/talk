use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    label::Label,
    node_kinds::{
        block::Block, func::EffectSet, parameter::Parameter, type_annotation::TypeAnnotation,
    },
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::Row,
        infer_ty::Ty,
        solve_context::SolveContext,
        type_error::TypeError,
        typed_ast::{TypedBlock, TypedEffect},
    },
};

#[must_use]
pub(super) struct ReturnToken {}

impl InferencePass<'_> {
    #[instrument(level = tracing::Level::TRACE, skip(self, block, context))]
    pub(super) fn infer_block(
        &mut self,
        block: &Block,
        context: &mut SolveContext,
    ) -> TypedRet<TypedBlock> {
        let mut ret = Ty::Void;

        let mut nodes = vec![];
        for node in block.body.iter() {
            let typed_node = self.visit_node(node, context)?;
            ret = typed_node.ty();
            nodes.push(typed_node);
        }

        Ok(TypedBlock {
            id: block.id,
            body: nodes,
            ret,
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block, context))]
    pub(super) fn infer_block_with_returns(
        &mut self,
        block: &Block,
        context: &mut SolveContext,
    ) -> TypedRet<TypedBlock> {
        let tok = self.tracking_returns();
        let block = self.infer_block(block, context)?;
        self.verify_returns(tok, block.ret.clone(), context);
        Ok(block)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block, context))]
    pub(super) fn check_block(
        &mut self,
        block: &Block,
        expected: Ty,
        context: &mut SolveContext,
    ) -> TypedRet<TypedBlock> {
        let tok = self.tracking_returns();
        let ret = self.infer_block(block, context)?;
        self.verify_returns(tok, ret.ret.clone(), context);
        self.constraints.wants_equals_at_with_cause(
            block.id,
            ret.ret.clone(),
            expected,
            &context.group_info(),
            Some(ConstraintCause::Annotation(block.id)),
        );
        Ok(ret)
    }

    // Checks
    #[allow(clippy::too_many_arguments)]
    #[allow(dead_code)]
    #[instrument(skip(self, body, context))]
    fn check_func(
        &mut self,
        params: &[Parameter],
        ret: &Option<TypeAnnotation>,
        body: &Block,
        expected_params: Vec<Ty>,
        expected_ret: Ty,
        context: &mut SolveContext,
    ) -> TypedRet<()> {
        for (param, expected_param_ty) in params.iter().zip(expected_params) {
            let Ok(sym) = param.name.symbol() else {
                self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                    id: param.id,
                    severity: Severity::Error,
                    kind: TypeError::NameNotResolved(param.name.clone()),
                }));
                continue;
            };

            self.session
                .insert_mono(sym, expected_param_ty, &mut self.constraints);
        }

        if let Some(ret) = ret {
            let ret_ty = self.visit_type_annotation(ret, context)?;
            self.constraints.wants_equals_at_with_cause(
                ret.id,
                ret_ty,
                expected_ret.clone(),
                &context.group_info(),
                Some(ConstraintCause::Annotation(ret.id)),
            );
        }

        self.check_block(body, expected_ret.clone(), context)?;

        Ok(())
    }

    fn tracking_returns(&mut self) -> ReturnToken {
        self.tracked_returns.push(Default::default());
        ReturnToken {}
    }

    pub(super) fn tracking_effects(
        &mut self,
        effect_set: &EffectSet,
        context: &mut SolveContext,
    ) -> Result<(ReturnToken, Vec<TypedEffect>), TypeError> {
        let mut effects = vec![];
        for effect in effect_set.names.iter() {
            let Ok(symbol) = effect.symbol() else {
                return Err(TypeError::NameNotResolved(effect.clone()));
            };

            let Some(effect) = self.session.lookup_effect(&symbol) else {
                return Err(TypeError::EffectNotFound(effect.name_str()));
            };

            effects.push(TypedEffect {
                name: symbol,
                ty: effect,
            });
        }

        let mut effects_row = if effect_set.is_open {
            self.session.new_row_meta_var(context.level())
        } else {
            Row::Empty
        };
        for effect in effects.iter() {
            effects_row = Row::Extend {
                row: effects_row.into(),
                label: Label::_Symbol(effect.name),
                ty: effect.ty.clone(),
            };
        }

        self.tracked_effect_rows.push(effects_row);

        Ok((ReturnToken {}, effects))
    }

    fn verify_returns(&mut self, _tok: ReturnToken, ret: Ty, context: &mut SolveContext) {
        for tracked_ret in self.tracked_returns.pop().unwrap_or_else(|| unreachable!()) {
            self.constraints.wants_equals_at(
                tracked_ret.0,
                tracked_ret.1,
                ret.clone(),
                &context.group_info(),
            );
        }
    }
}
