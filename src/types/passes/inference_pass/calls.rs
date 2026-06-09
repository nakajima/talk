use itertools::Itertools;
use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        call_arg::CallArg,
        expr::{Expr, ExprKind},
        type_annotation::TypeAnnotation,
    },
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::Row,
        infer_ty::Ty,
        passes::uncurry_function,
        scheme::Scheme,
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::curry,
        typed_ast::{TypedExpr, TypedExprKind, TypedFunc},
    },
};

impl InferencePass<'_> {
    fn call_receiver_ty(&self, expr: &TypedExpr) -> Ty {
        expr.ty.clone()
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
            let instantiated = scheme
                .instantiate_with_checked_args(
                    expr.id,
                    &type_arg_tys
                        .iter()
                        .zip(type_args.iter())
                        .map(|(ty, ann)| (ty.clone(), ann.id))
                        .collect::<Vec<_>>(),
                    self.session,
                    context,
                    &mut self.constraints,
                )
                .map_err(|e| self.report_error(expr.id, e))?;
            self.instantiations
                .insert(expr.id, instantiated.type_args.clone());
            instantiated.value
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
        self.session.record_effect_callee(
            expr.id,
            effect_sym,
            self.instantiations
                .get(&expr.id)
                .cloned()
                .unwrap_or_default(),
        );
        if let Some(owner) = self.current_callable {
            self.session.record_callee_owner(expr.id, owner);
        }
        Ok(typed)
    }

    fn visit_member_callee(
        &mut self,
        expr: &Expr,
        receiver: &Option<Box<Expr>>,
        label: &Label,
        label_span: Span,
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let receiver_ty = if let Some(receiver) = receiver {
            self.visit_expr(receiver, context)?
        } else {
            TypedExpr {
                id: expr.id,
                ty: self.session.new_ty_meta_var(context.level().next()),
                kind: TypedExprKind::Hole,
            }
        };

        Ok(TypedExpr {
            id: expr.id,
            ty: self.session.new_ty_meta_var(context.level().next()),
            kind: TypedExprKind::Member {
                receiver: Box::new(receiver_ty),
                label: label.clone(),
                label_span,
            },
        })
    }

    fn method_self_type_for_call(
        &mut self,
        callee_ty: &TypedExpr,
        arg_tys: &[TypedExpr],
        context: &SolveContext,
    ) -> Option<Ty> {
        let TypedExprKind::Member { receiver, .. } = &callee_ty.kind else {
            return None;
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
                    Some(self.call_receiver_ty(receiver_arg))
                }
                [] => None,
            };
        }

        Some(self.call_receiver_ty(receiver))
    }

    fn record_callee_for_call(&mut self, call_id: NodeID, callee: &TypedExpr, args: &[TypedExpr]) {
        match &callee.kind {
            TypedExprKind::Variable(sym @ Symbol::MethodRequirement(_)) => {
                if let Some(first_arg) = args.first() {
                    let self_ty = self.call_receiver_ty(first_arg);
                    self.session.record_method_callee(
                        call_id,
                        *sym,
                        self_ty,
                        self.instantiations
                            .get(&callee.id)
                            .cloned()
                            .unwrap_or_default(),
                    );
                } else {
                    self.session.record_function_callee(
                        call_id,
                        *sym,
                        self.instantiations
                            .get(&callee.id)
                            .cloned()
                            .unwrap_or_default(),
                    );
                }
            }
            TypedExprKind::Variable(sym) => self.session.record_function_callee(
                call_id,
                *sym,
                self.instantiations
                    .get(&callee.id)
                    .cloned()
                    .unwrap_or_default(),
            ),
            TypedExprKind::Constructor(sym, _) => {
                self.session.record_initializer_callee(call_id, *sym)
            }
            TypedExprKind::Member { .. } => {}
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
        let callee_ty = match &callee.kind {
            ExprKind::Member(receiver, label, label_span) => {
                self.visit_member_callee(callee, receiver, label, *label_span, context)?
            }
            _ => self.visit_expr(callee, context)?,
        };

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
            let typed_block =
                self.with_current_callable(anon_sym, |this| this.infer_block(block, context))?;

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

        let ret = self.session.new_ty_meta_var(context.level());
        let method_self_ty = self.method_self_type_for_call(&callee_ty, &arg_tys, context);
        if let TypedExprKind::Member {
            receiver, label, ..
        } = &callee_ty.kind
        {
            self.constraints.wants_member_call(
                id,
                callee_ty.id,
                receiver.ty.clone(),
                method_self_ty
                    .clone()
                    .unwrap_or_else(|| receiver.ty.clone()),
                label.clone(),
                callee_ty.ty.clone(),
                ret.clone(),
                matches!(receiver.kind, TypedExprKind::Hole),
                &context.group_info(),
            );
        } else {
            self.record_callee_for_call(id, &callee_ty, &arg_tys);
        }
        if let Some(owner) = self.current_callable {
            self.session.record_callee_owner(id, owner);
        }

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

        let instantiations = self
            .instantiations
            .get(&callee.id)
            .cloned()
            .unwrap_or_default();
        let ty_mappings = instantiations.ty.clone();
        if !type_args.is_empty()
            && !matches!(callee_ty.kind, TypedExprKind::Constructor(..))
            && !ty_mappings.is_empty()
            && type_args.len() != ty_mappings.len()
        {
            return Err(self.report_error(
                type_args.first().map(|arg| arg.id).unwrap_or(id),
                TypeError::GenericArgCount {
                    expected: ty_mappings.len() as u8,
                    actual: type_args.len() as u8,
                },
            ));
        }
        for ((type_arg, type_arg_ty), instantiated) in type_args
            .iter()
            .zip(type_arg_tys.iter())
            .zip(ty_mappings.values())
        {
            self.constraints.wants_equals_at_with_cause(
                type_arg.id,
                type_arg_ty.clone(),
                instantiated.clone(),
                &context.group_info(),
                Some(ConstraintCause::CallTypeArg(type_arg.id)),
            );
        }

        let callee_ty_var = self.session.new_ty_meta_var(context.level());

        self.constraints.wants_call(
            id,
            callee.id,
            callee_ty.ty.clone(),
            arg_tys.iter().map(|a| a.ty.clone()).collect_vec(),
            type_arg_tys.clone(),
            ret.clone(),
            callee_ty_var.clone(),
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
