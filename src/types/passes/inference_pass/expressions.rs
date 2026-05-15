use itertools::Itertools;
use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{
        expr::Expr,
        inline_ir_instruction::{InlineIRInstruction, TypedInlineIRInstruction},
        record_field::RecordField,
        type_annotation::TypeAnnotation,
    },
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::Row,
        infer_ty::Ty,
        solve_context::SolveContext,
        type_error::TypeError,
        typed_ast::{TypedExpr, TypedExprKind, TypedRecordField},
    },
};

impl InferencePass<'_> {
    pub(super) fn visit_inline_ir(
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

    pub(super) fn visit_as(
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

    pub(super) fn visit_array(
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

    pub(super) fn visit_constructor(
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

    pub(super) fn visit_member(
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
    pub(super) fn infer_record_literal(
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
    pub(super) fn visit_variable(
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
}
