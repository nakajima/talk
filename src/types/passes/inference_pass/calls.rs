use itertools::Itertools;
use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{block::Block, call_arg::CallArg, expr::Expr, type_annotation::TypeAnnotation},
    span::Span,
    types::{
        call_site::{CallReceiver, CallReceiverKind, CallShape, CallSiteId},
        constraints::constraint::ConstraintCause,
        infer_row::Row,
        infer_ty::{Meta, Ty},
        passes::uncurry_function,
        scheme::Scheme,
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::curry,
        typed_ast::{TypedExpr, TypedExprKind, TypedFunc},
    },
};

impl InferencePass<'_> {
    fn call_receiver_info(&mut self, expr: &TypedExpr) -> (Ty, Option<Symbol>) {
        let TypedExprKind::Variable(symbol) = &expr.kind else {
            return (expr.ty.clone(), None);
        };

        let ty = self
            .session
            .lookup(symbol)
            .map(|entry| entry._as_ty())
            .unwrap_or_else(|| expr.ty.clone());
        (ty, Some(*symbol))
    }

    pub(super) fn visit_call_effect(
        &mut self,
        expr: &Expr,
        effect_name: &Name,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let Ok(effect_sym) = effect_name.symbol() else {
            return Err(TypeError::NameNotResolved(effect_name.clone()));
        };

        let Some(effect) = self.session.type_catalog.lookup_effect(&effect_sym) else {
            return Err(TypeError::EffectNotFound(effect_name.name_str()));
        };

        // Process explicit type args
        let type_arg_tys: Vec<_> = type_args
            .iter()
            .map(|a| self.visit_type_annotation(a, context))
            .try_collect()?;

        // Instantiate the effect signature (replace Params with fresh meta vars)
        let foralls = effect.collect_foralls();
        let instantiated_effect = if foralls.is_empty() {
            effect.clone()
        } else {
            // Build a scheme from the foralls and instantiate it
            let scheme = Scheme::new(foralls.into_iter().collect(), vec![], effect.clone());
            let (instantiated, subs) = scheme.instantiate_with_args(
                expr.id,
                &type_arg_tys
                    .iter()
                    .zip(type_args.iter())
                    .map(|(ty, ann)| (ty.clone(), ann.id))
                    .collect::<Vec<_>>(),
                self.session,
                context,
                &mut self.constraints,
            );
            // Store instantiations for explicit type-argument checking in this pass.
            self.instantiations.insert(expr.id, subs);
            instantiated
        };

        let mut typed_args = vec![];
        let (params, ret, _effects) = uncurry_function(instantiated_effect.clone());
        for (effect_ty, arg) in params.iter().zip(args) {
            let typed_arg = self.visit_expr(&arg.value, context)?;
            self.constraints.wants_equals_at_with_cause(
                arg.id,
                effect_ty.clone(),
                typed_arg.ty.clone(),
                &context.group_info(),
                Some(ConstraintCause::Call(expr.id)),
            );
            typed_args.push(typed_arg);
        }

        // Only require effect in row if it's not already handled by a handler
        if !self.handled_effects.contains(&effect_sym)
            && let Some(current_effect_row) = self.tracked_effect_rows.last()
        {
            self.constraints._has_field(
                current_effect_row.clone(),
                Label::_Symbol(effect_sym),
                instantiated_effect,
                Some(expr.id),
                &context.group_info(),
            );
        }

        let typed = TypedExpr {
            id: expr.id,
            ty: ret.clone(),
            kind: TypedExprKind::CallEffect {
                effect: effect_sym,
                type_args: type_arg_tys,
                args: typed_args,
            },
        };
        self.session.record_effect_call_site(
            CallSiteId::from_effect(&typed),
            self.current_caller,
            effect_sym,
        );
        Ok(typed)
    }

    fn resolved_call_shape_for(
        &mut self,
        callee_ty: &TypedExpr,
        arg_tys: &[TypedExpr],
        context: &SolveContext,
    ) -> CallShape {
        let TypedExprKind::Member { receiver, .. } = &callee_ty.kind else {
            return CallShape::as_written(None);
        };

        if let TypedExprKind::Constructor(Symbol::Protocol(protocol_id), ..) = &receiver.kind {
            return match arg_tys {
                [receiver_arg, ..] => {
                    self.constraints.wants_conforms(
                        receiver.id,
                        receiver_arg.ty.clone(),
                        *protocol_id,
                        &context.group_info(),
                    );
                    let (ty, symbol) = self.call_receiver_info(receiver_arg);
                    CallShape::as_written(Some(CallReceiver {
                        kind: CallReceiverKind::Argument { index: 0 },
                        id: receiver_arg.id,
                        ty,
                        symbol,
                    }))
                }
                [] => CallShape::as_written(None),
            };
        }

        let (ty, symbol) = self.call_receiver_info(receiver);
        let receiver_source = CallReceiver {
            kind: CallReceiverKind::CalleeReceiver,
            id: receiver.id,
            ty,
            symbol,
        };
        if matches!(
            &receiver.kind,
            TypedExprKind::Constructor(..) | TypedExprKind::Hole
        ) {
            CallShape::as_written(Some(receiver_source))
        } else {
            CallShape::prepend_receiver(receiver_source, receiver.id)
        }
    }

    fn record_call_site_for_callee(
        &mut self,
        call_site_id: CallSiteId,
        callee: &TypedExpr,
        shape: CallShape,
    ) {
        match &callee.kind {
            TypedExprKind::Variable(sym) => {
                self.session
                    .record_direct_call_site(call_site_id, self.current_caller, *sym)
            }
            TypedExprKind::Constructor(sym, _) => {
                self.session
                    .record_initializer_call_site(call_site_id, self.current_caller, *sym)
            }
            TypedExprKind::Member { label, .. } => self.session.record_method_call_shape(
                call_site_id,
                self.current_caller,
                label.clone(),
                shape,
            ),
            _ => {}
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, ))]
    pub(super) fn visit_call(
        &mut self,
        id: NodeID,
        callee: &Expr,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        trailing_block: Option<&Block>,
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let callee_ty = self.visit_expr(callee, context)?;

        let mut arg_tys: Vec<_> = args
            .iter()
            .map(|a| self.visit_expr(&a.value, context))
            .try_collect()?;

        // If there's a trailing block, convert it to a function-typed argument
        if let Some(block) = trailing_block {
            // First, visit the block parameters to register their types
            let typed_params = self.visit_params(&block.args, context)?;
            let param_tys: Vec<Ty> = typed_params.iter().map(|p| p.ty.clone()).collect();

            // Create a synthesized symbol for this anonymous function
            let anon_sym = Symbol::Synthesized(
                self.session
                    .symbols
                    .next_synthesized(self.session.current_module_id),
            );

            // Now infer the block body (parameters are now in scope)
            let typed_block = self.with_current_caller(
                crate::types::call_site::CallerContext::Callable(anon_sym),
                |this| this.infer_block(block, context),
            )?;

            // Build the function type: (param_types) -> return_type
            let func_ty = curry(
                param_tys.iter().cloned(),
                typed_block.ret.clone(),
                Row::Empty.into(),
            );

            // Register the symbol name for debugging/error messages
            self.session
                .resolved_names
                .symbol_names
                .insert(anon_sym, "<trailing_block>".to_string());

            // Register the function type for the synthesized symbol
            self.session
                .insert(anon_sym, func_ty.clone(), &mut Default::default());

            // Wrap the block in a TypedFunc so it's lowered as a callable
            let typed_func = TypedFunc {
                name: anon_sym,
                foralls: Default::default(),
                params: typed_params,
                effects: vec![],
                effects_row: Row::Empty,
                body: typed_block.clone(),
                ret: typed_block.ret.clone(),
            };

            arg_tys.push(TypedExpr {
                id: block.id,
                ty: func_ty,
                kind: TypedExprKind::Func(typed_func),
            });
        }

        let resolved_call_shape = self.resolved_call_shape_for(&callee_ty, &arg_tys, context);
        let call_site_id = CallSiteId::from_callee_node(callee.id);
        self.record_call_site_for_callee(call_site_id, &callee_ty, resolved_call_shape.clone());

        // Record call arg label spans immediately for Constructor callees
        // The struct symbol is available now, so we can resolve directly
        if let TypedExprKind::Constructor(struct_sym, _) = &callee_ty.kind {
            for arg in args {
                if let Label::Named(_) = &arg.label
                    && arg.label_span != Span::SYNTHESIZED
                    && let Some(prop_sym) = self
                        .session
                        .type_catalog
                        .properties
                        .get(struct_sym)
                        .and_then(|p| p.get(&arg.label))
                {
                    let _ = prop_sym;
                }
            }
        }

        let type_arg_tys: Vec<_> = type_args
            .iter()
            .map(|a| self.visit_type_annotation(a, context))
            .try_collect()?;

        let receiver = match &callee_ty.kind {
            TypedExprKind::Member { receiver, .. } => Some(receiver.as_ref().clone()),
            _ => None,
        };

        let ret = self.session.new_ty_meta_var(context.level());
        let instantiations = self
            .instantiations
            .get(&callee.id)
            .cloned()
            .unwrap_or_default();
        for ((type_arg, type_arg_ty), instantiated) in type_args
            .iter()
            .zip(type_arg_tys.iter())
            .zip(instantiations.ty_mappings(&callee.id).values())
        {
            self.constraints.wants_equals_at_with_cause(
                type_arg.id,
                type_arg_ty.clone(),
                Ty::Var {
                    id: *instantiated,
                    level: self
                        .session
                        .meta_levels
                        .borrow()
                        .get(&Meta::Ty(*instantiated))
                        .copied()
                        .unwrap_or_default(),
                },
                &context.group_info(),
                Some(ConstraintCause::CallTypeArg(type_arg.id)),
            );
        }

        // if matches!(callee_ty, Ty::Constructor { .. }) {
        //     arg_tys.insert(0, ret.clone());
        // }
        let callee_ty_var = self.session.new_ty_meta_var(context.level());

        self.constraints.wants_call(
            id,
            callee.id,
            callee_ty.ty.clone(),
            arg_tys.iter().map(|a| a.ty.clone()).collect_vec(),
            type_arg_tys.clone(),
            ret.clone(),
            callee_ty_var.clone(),
            receiver.map(|r| r.ty.clone()),
            &context.group_info(),
            self.tracked_effect_rows
                .last()
                .cloned()
                .unwrap_or(self.session.new_row_meta_var(context.level())),
        );

        Ok(TypedExpr {
            id,
            ty: ret.clone(),
            kind: TypedExprKind::Call {
                callee: callee_ty.into(),
                callee_ty: callee_ty_var,
                type_args: type_arg_tys,
                args: arg_tys,
                callee_sym: None,
            },
        })
    }
}
