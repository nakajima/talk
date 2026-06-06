use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    node_id::NodeID,
    node_kinds::{expr::Expr, pattern::Pattern, type_annotation::TypeAnnotation},
    types::{
        constraints::constraint::ConstraintCause,
        solve_context::SolveContext,
        typed_ast::{TypedDecl, TypedDeclKind},
    },
};

impl InferencePass<'_> {
    #[instrument(level = tracing::Level::TRACE, skip(self, context, rhs))]
    pub(super) fn visit_let(
        &mut self,
        id: NodeID,
        lhs: &Pattern,
        type_annotation: &Option<TypeAnnotation>,
        rhs: &Option<Expr>,
        context: &mut SolveContext,
    ) -> TypedRet<TypedDecl> {
        let typed_rhs = if let Some(rhs) = rhs {
            Some(self.visit_expr(rhs, context)?)
        } else {
            None
        };

        let (ty, initializer) = match (&type_annotation, typed_rhs) {
            (None, Some(expr)) => (expr.ty.clone(), Some(expr)),
            (Some(annotation), None) => (self.visit_type_annotation(annotation, context)?, None),
            (Some(annotation), Some(rhs_ty)) => {
                let annotated_ty = self.visit_type_annotation(annotation, context)?;
                self.constraints.wants_equals_at_with_cause(
                    rhs_ty.id,
                    annotated_ty.clone(),
                    rhs_ty.ty.clone(),
                    &context.group_info(),
                    Some(ConstraintCause::Annotation(rhs_ty.id)),
                );
                (annotated_ty, Some(rhs_ty))
            }
            (None, None) => (self.session.new_ty_meta_var(context.level().next()), None),
        };

        let typed_pattern = self.check_pattern(lhs, &ty, context)?;

        Ok(TypedDecl {
            id,
            ty: ty.clone(),
            kind: TypedDeclKind::Let {
                pattern: typed_pattern,
                initializer,
                ty,
            },
        })
    }
}
