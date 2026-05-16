use itertools::Itertools;
use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    formatter,
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{
        expr::{Expr, ExprKind},
        inline_ir_instruction::{InlineIRInstruction, TypedInlineIRInstruction},
        record_field::RecordField,
        type_annotation::TypeAnnotation,
    },
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::Row,
        infer_ty::{Level, Ty},
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::curry,
        typed_ast::{TypedExpr, TypedExprKind, TypedRecordField},
    },
};

impl InferencePass<'_> {
    fn visit_inline_ir(
        &mut self,
        instr: &InlineIRInstruction,
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        for bind in instr.binds.iter() {
            self.visit_expr(bind, context)?;
        }

        let ty = self.session.new_ty_meta_var(context.level());

        Ok(TypedExpr {
            id: instr.id,
            ty,
            kind: TypedExprKind::InlineIR(
                TypedInlineIRInstruction {
                    id: instr.id,
                    span: instr.span,
                    binds: instr
                        .binds
                        .iter()
                        .map(|e| self.visit_expr(e, context))
                        .try_collect()?,
                    instr_name_span: instr.instr_name_span,
                    kind: instr.kind.clone(),
                }
                .into(),
            ),
        })
    }

    fn visit_as(
        &mut self,
        lhs: &Expr,
        rhs: &TypeAnnotation,
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let lhs_ty = self.visit_expr(lhs, context)?;
        let Ok(Symbol::Protocol(id)) = rhs.symbol() else {
            return Err(TypeError::MissingConformanceRequirement(format!(
                "Protocol not found: {rhs:?}"
            )));
        };

        self.constraints
            .wants_conforms(lhs.id, lhs_ty.ty.clone(), id, &context.group_info());

        Ok(lhs_ty)
    }

    fn visit_array(
        &mut self,
        expr: &Expr,
        items: &[Expr],
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let Some(first_item) = items.first() else {
            let id = self.session.new_ty_meta_var_id(context.level());

            return Ok(TypedExpr {
                id: expr.id,
                ty: Ty::Array(Ty::Var {
                    id,
                    level: context.level(),
                }),
                kind: TypedExprKind::LiteralArray(vec![]),
            });
        };

        let item_ty = self.visit_expr(first_item, context)?;

        let mut typed_items = vec![item_ty.clone()];
        for expr in items[1..].iter() {
            let ty = self.visit_expr(expr, context)?;
            self.constraints.wants_equals_at_with_cause(
                expr.id,
                item_ty.ty.clone(),
                ty.ty.clone(),
                &context.group_info(),
                Some(ConstraintCause::Literal(expr.id)),
            );
            typed_items.push(ty);
        }

        Ok(TypedExpr {
            id: expr.id,
            ty: Ty::Array(item_ty.ty),
            kind: TypedExprKind::LiteralArray(typed_items),
        })
    }

    fn visit_constructor(
        &mut self,
        expr: &Expr,
        name: &Name,
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let symbol = name
            .symbol()
            .map_err(|_| TypeError::NameNotResolved(name.clone()))?;

        let ret = self.session.new_ty_meta_var(context.level()).into();

        let ty = Ty::Constructor {
            name: name.clone(),
            params: vec![],
            ret,
        };

        Ok(TypedExpr {
            id: expr.id,
            ty,
            kind: TypedExprKind::Constructor(symbol, vec![]),
        })
    }

    fn visit_member(
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

        let ret = self.session.new_ty_meta_var(context.level().next());

        self.constraints.wants_member(
            expr.id,
            receiver_ty.ty.clone(),
            label.clone(),
            ret.clone(),
            &context.group_info(),
        );

        Ok(TypedExpr {
            id: expr.id,
            ty: ret,
            kind: TypedExprKind::Member {
                receiver: Box::new(receiver_ty),
                label: label.clone(),
                label_span,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn infer_record_literal(
        &mut self,
        id: NodeID,
        fields: &[RecordField],
        spread: &Option<Box<Expr>>,
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let mut row = Row::Empty;
        let mut typed_fields = vec![];
        for field in fields.iter().rev() {
            let typed_field = self.visit_expr(&field.value, context)?;
            row = Row::Extend {
                row: Box::new(row),
                label: field.label.name_str().into(),
                ty: typed_field.ty.clone(),
            };

            typed_fields.push(TypedRecordField {
                name: field.label.name_str().into(),
                value: typed_field,
            });
        }
        // We iterate `fields` in reverse to build a row whose closed order matches the source
        // order, but we still want to evaluate and lower the record fields in source order.
        typed_fields.reverse();

        Ok(TypedExpr {
            id,
            ty: Ty::Record(None, Box::new(row)),
            kind: TypedExprKind::RecordLiteral {
                fields: typed_fields,
            },
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr, context))]
    fn visit_variable(
        &mut self,
        expr: &Expr,
        name: &Name,
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let Ok(sym) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        let Some(entry) = self.session.lookup(&sym) else {
            return Err(TypeError::TypeNotFound(format!(
                "Entry not found for variable {:?}",
                name
            )));
        };

        let ty = entry.instantiate(expr.id, &mut self.constraints, context, self.session);

        self.instantiations
            .insert(expr.id, context.instantiations_mut().clone());

        Ok(TypedExpr {
            id: expr.id,
            ty,
            kind: TypedExprKind::Variable(sym),
        })
    }
    #[instrument(level = tracing::Level::TRACE, skip(self, expr, context), fields(expr.id = ?expr.id, expr = formatter::format_node(&expr.into(), &self.asts[0].meta)))]
    pub(super) fn visit_expr(
        &mut self,
        expr: &Expr,
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let expr = match &expr.kind {
            ExprKind::Incomplete(incomplete) => {
                use crate::node_kinds::incomplete_expr::IncompleteExpr;
                match incomplete {
                    IncompleteExpr::Member(Some(receiver)) => {
                        let _ = self.visit_expr(receiver, context)?;
                    }
                    IncompleteExpr::Member(None) => {}
                    IncompleteExpr::Func { .. } => {}
                }

                TypedExpr {
                    id: expr.id,
                    ty: Ty::Void,
                    kind: TypedExprKind::Hole,
                }
            }
            ExprKind::CallEffect {
                effect_name,
                type_args,
                args,
                ..
            } => self.visit_call_effect(expr, effect_name, type_args, args, context)?,
            ExprKind::LiteralArray(items) => self.visit_array(expr, items, context)?,
            ExprKind::LiteralInt(v) => TypedExpr {
                id: expr.id,
                ty: self.meta_with_default(
                    expr.id,
                    context.level(),
                    Ty::Int,
                    vec![Ty::Int, Ty::Byte],
                ),
                kind: TypedExprKind::LiteralInt(v.to_string()),
            },
            ExprKind::LiteralFloat(v) => TypedExpr {
                id: expr.id,
                ty: self.meta_with_default(expr.id, context.level(), Ty::Float, vec![Ty::Float]),
                kind: TypedExprKind::LiteralFloat(v.to_string()),
            },
            ExprKind::LiteralTrue => TypedExpr {
                id: expr.id,
                ty: Ty::Bool,
                kind: TypedExprKind::LiteralTrue,
            },
            ExprKind::LiteralFalse => TypedExpr {
                id: expr.id,
                ty: Ty::Bool,
                kind: TypedExprKind::LiteralFalse,
            },
            ExprKind::LiteralString(val) => TypedExpr {
                id: expr.id,
                ty: self.meta_with_default(
                    expr.id,
                    context.level(),
                    Ty::String(),
                    vec![Ty::String()],
                ),
                kind: TypedExprKind::LiteralString(val.to_string()),
            },
            ExprKind::Tuple(exprs) => match exprs.len() {
                0 => TypedExpr {
                    id: expr.id,
                    ty: Ty::Void,
                    kind: TypedExprKind::Tuple(Default::default()),
                },
                1 => self.visit_expr(&exprs[0], context)?,
                _ => {
                    let typed_exprs: Vec<_> = exprs
                        .iter()
                        .map(|e| self.visit_expr(e, context))
                        .try_collect()?;
                    TypedExpr {
                        id: expr.id,
                        ty: Ty::Tuple(typed_exprs.iter().map(|t| t.ty.clone()).collect_vec()),
                        kind: TypedExprKind::Tuple(typed_exprs),
                    }
                }
            },
            ExprKind::Block(block) => {
                let typed_block = self.infer_block(block, context)?;
                TypedExpr {
                    id: expr.id,
                    ty: typed_block.ret.clone(),
                    kind: TypedExprKind::Block(typed_block),
                }
            }
            ExprKind::Unary(..) | ExprKind::Binary(..) => {
                unreachable!("these are lowered to calls earlier")
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
                trailing_block,
            } => self.visit_call(
                expr.id,
                callee,
                type_args,
                args,
                trailing_block.as_ref(),
                &mut context.next(),
            )?,
            ExprKind::Member(receiver, label, label_span) => {
                self.visit_member(expr, receiver, label, *label_span, context)?
            }
            ExprKind::Func(func) => {
                let func = self.visit_func(func, context)?;
                TypedExpr {
                    id: expr.id,
                    ty: curry(
                        func.params.iter().map(|p| p.ty.clone()),
                        func.ret.clone(),
                        func.effects_row.clone().into(),
                    ),
                    kind: TypedExprKind::Func(func),
                }
            }
            ExprKind::Variable(name) => self.visit_variable(expr, name, &mut context.next())?,
            ExprKind::Constructor(name) => self.visit_constructor(expr, name, context)?,
            ExprKind::If(cond, conseq, alt) => {
                self.infer_if_expr(expr.id, cond, conseq, alt, context)?
            }
            ExprKind::Match(scrutinee, arms) => {
                self.infer_match(expr.id, scrutinee, arms, context)?
            }
            ExprKind::RecordLiteral { fields, spread } => {
                self.infer_record_literal(expr.id, fields, spread, context)?
            }
            ExprKind::RowVariable(name) => {
                return Err(TypeError::UnsupportedFeature(format!(
                    "row variable expression `{}` outside of a row context",
                    name.name_str()
                )));
            }
            ExprKind::As(box lhs, rhs) => self.visit_as(lhs, rhs, context)?,
            ExprKind::InlineIR(instr) => self.visit_inline_ir(instr, context)?,
        };

        self.session.types_by_node.insert(expr.id, expr.ty.clone());

        Ok(expr)
    }

    fn meta_with_default(&mut self, id: NodeID, level: Level, ty: Ty, allowed: Vec<Ty>) -> Ty {
        let var = self.session.new_ty_meta_var(level);
        self.constraints.wants_default(id, var.clone(), ty, allowed);
        var
    }
}
