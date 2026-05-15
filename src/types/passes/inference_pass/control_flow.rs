use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    node_id::NodeID,
    node_kinds::{block::Block, expr::Expr, match_arm::MatchArm, stmt::Stmt},
    types::{
        constraints::constraint::ConstraintCause,
        infer_ty::Ty,
        solve_context::SolveContext,
        typed_ast::{
            TypedBlock, TypedExpr, TypedExprKind, TypedMatchArm, TypedStmt, TypedStmtKind,
        },
    },
};

impl InferencePass<'_> {
    pub(super) fn visit_return(
        &mut self,
        stmt: &Stmt,
        expr: &Option<Expr>,
        context: &mut SolveContext,
    ) -> TypedRet<TypedStmt> {
        let ty_expr = if let Some(expr) = expr {
            Some(self.visit_expr(expr, context)?)
        } else {
            None
        };

        if let Some(returns) = self.tracked_returns.last_mut()
            && let Some(ty_expr) = &ty_expr
        {
            returns.insert((stmt.id, ty_expr.ty.clone()));
        }

        Ok(TypedStmt {
            id: stmt.id,
            ty: ty_expr.as_ref().map(|t| t.ty.clone()).unwrap_or(Ty::Void),
            kind: TypedStmtKind::Return(ty_expr),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, scrutinee, arms, context))]
    pub(super) fn infer_match(
        &mut self,
        id: NodeID,
        scrutinee: &Expr,
        arms: &[MatchArm],
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let mut last_arm_ty: Option<Ty> = None;
        let scrutinee_ty = self.visit_expr(scrutinee, context)?;
        let mut typed_arms = vec![];

        for arm in arms {
            let pattern = self.check_pattern(&arm.pattern, &scrutinee_ty.ty.clone(), context)?;
            let arm_ty = self.infer_block(&arm.body, context)?;

            if let Some(last_arm_ty) = &last_arm_ty {
                self.constraints.wants_equals_at_with_cause(
                    arm.id,
                    arm_ty.ret.clone(),
                    last_arm_ty.clone(),
                    &context.group_info(),
                    Some(ConstraintCause::MatchArm(arm.id)),
                );
            }

            last_arm_ty = Some(arm_ty.ret.clone());
            typed_arms.push(TypedMatchArm {
                pattern,
                body: arm_ty,
            });
        }

        let ty = last_arm_ty.unwrap_or(Ty::Void);

        Ok(TypedExpr {
            id,
            ty,
            kind: TypedExprKind::Match(Box::new(scrutinee_ty), typed_arms),
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt, context))]
    pub(super) fn infer_if_expr(
        &mut self,
        id: NodeID,
        cond: &Expr,
        conseq: &Block,
        alt: &Block,
        context: &mut SolveContext,
    ) -> TypedRet<TypedExpr> {
        let cond_ty = self.visit_expr(cond, context)?;
        self.constraints.wants_equals_at_with_cause(
            cond.id,
            cond_ty.ty.clone(),
            Ty::Bool,
            &context.group_info(),
            Some(ConstraintCause::Condition(cond.id)),
        );

        let conseq_ty = self.infer_block(conseq, context)?;
        let alt_ty = self.infer_block(alt, context)?;
        self.constraints.wants_equals_at(
            id,
            conseq_ty.ret.clone(),
            alt_ty.ret.clone(),
            &context.group_info(),
        );

        Ok(TypedExpr {
            id,
            ty: conseq_ty.ret.clone(),
            kind: TypedExprKind::If(cond_ty.into(), conseq_ty, alt_ty),
        })
    }

    // TODO: We should be smarter about whether we've got an if stmt vs an if expr
    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt, context))]
    pub(super) fn visit_if_stmt(
        &mut self,
        id: NodeID,
        cond: &Expr,
        conseq: &Block,
        alt: &Option<Block>,
        context: &mut SolveContext,
    ) -> TypedRet<TypedStmt> {
        let cond_ty = self.visit_expr(cond, context)?;
        self.constraints.wants_equals_at_with_cause(
            cond.id,
            cond_ty.ty.clone(),
            Ty::Bool,
            &context.group_info(),
            Some(ConstraintCause::Condition(cond.id)),
        );

        let conseq_ty = self.infer_block(conseq, context)?;

        let (alt_ty, result_ty) = if let Some(alt) = alt {
            let alt_ty = self.infer_block(alt, context)?;
            self.constraints.wants_equals_at(
                id,
                conseq_ty.ret.clone(),
                alt_ty.ret.clone(),
                &context.group_info(),
            );
            (alt_ty, conseq_ty.ret.clone())
        } else {
            (
                TypedBlock {
                    id: NodeID(id.0, self.asts[id.0.0 as usize].node_ids.next_id()),
                    body: vec![],
                    ret: Ty::Void,
                },
                Ty::Void,
            )
        };

        Ok(TypedStmt {
            id,
            ty: result_ty.clone(),
            kind: TypedStmtKind::Expr(TypedExpr {
                id,
                ty: result_ty,
                kind: TypedExprKind::If(cond_ty.into(), conseq_ty, alt_ty),
            }),
        })
    }
}
