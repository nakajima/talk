use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    node::Node,
    node_kinds::{
        decl::{Decl, DeclKind},
        stmt::{Stmt, StmtKind},
    },
    types::{
        constraints::constraint::ConstraintCause,
        infer_ty::Ty,
        solve_context::SolveContext,
        type_error::TypeError,
        typed_ast::{
            TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedNode, TypedStmt, TypedStmtKind,
        },
    },
};

impl InferencePass<'_> {
    #[instrument(level = tracing::Level::TRACE, skip(self, node, context), fields(node.id = ?node.node_id()))]
    pub(super) fn visit_node(
        &mut self,
        node: &Node,
        context: &mut SolveContext,
    ) -> TypedRet<TypedNode> {
        match &node {
            Node::Decl(decl) => Ok(TypedNode::Decl(self.visit_decl(decl, context)?)),
            Node::Stmt(stmt) => Ok(TypedNode::Stmt(self.visit_stmt(stmt, context)?)),
            Node::Expr(expr) => Ok(TypedNode::Expr(self.visit_expr(expr, context)?)),
            _ => Err(TypeError::TypeNotFound(format!(
                "No type checking for {node:?}"
            ))),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, context), fields(decl.id = ?decl.id))]
    pub(super) fn visit_decl(
        &mut self,
        decl: &Decl,
        context: &mut SolveContext,
    ) -> TypedRet<TypedDecl> {
        match &decl.kind {
            DeclKind::Effect { name, .. } => Ok(TypedDecl {
                id: decl.id,
                ty: Ty::Void,
                kind: TypedDeclKind::Extend {
                    symbol: name
                        .symbol()
                        .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                    instance_methods: Default::default(),
                    typealiases: Default::default(),
                },
            }),
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => self.visit_let(decl.id, lhs, type_annotation, rhs, context),
            DeclKind::Struct {
                name,
                generics,
                body,
                ..
            } => self.visit_nominal(decl, name, generics, Default::default(), body, context),
            DeclKind::Protocol {
                name,
                generics,
                body,
                conformances,
                ..
            } => Ok(self
                .visit_protocol(decl, name, generics, conformances, body, context)?
                .0),
            DeclKind::Extend {
                name,
                conformances,
                generics,
                body,
                ..
            } => self.visit_nominal(decl, name, generics, conformances, body, context),
            DeclKind::Enum {
                name,
                generics,
                body,
                ..
            } => self.visit_nominal(decl, name, generics, Default::default(), body, context),
            DeclKind::Import(_) => Ok(TypedDecl {
                id: decl.id,
                ty: Ty::Void,
                kind: TypedDeclKind::Import,
            }),
            DeclKind::Func(..)
            | DeclKind::Init { .. }
            | DeclKind::TypeAlias(..)
            | DeclKind::Associated { .. }
            | DeclKind::Method { .. }
            | DeclKind::Property { .. }
            | DeclKind::MethodRequirement(..)
            | DeclKind::FuncSignature(..)
            | DeclKind::EnumVariant(..) => unreachable!("skipped: {decl:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, stmt, context), fields(stmt.id = ?stmt.id))]
    pub(super) fn visit_stmt(
        &mut self,
        stmt: &Stmt,
        context: &mut SolveContext,
    ) -> TypedRet<TypedStmt> {
        let ty = match &stmt.kind {
            StmtKind::Expr(expr) => {
                let typed_expr = self.visit_expr(expr, context)?;
                TypedStmt {
                    id: stmt.id,
                    ty: typed_expr.ty.clone(),
                    kind: TypedStmtKind::Expr(typed_expr),
                }
            }
            StmtKind::If(cond, conseq, alt) => {
                self.visit_if_stmt(stmt.id, cond, conseq, alt, context)?
            }
            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.visit_expr(lhs, context)?;
                let rhs_ty = self.visit_expr(rhs, context)?;
                self.constraints.wants_equals_at_with_cause(
                    stmt.id,
                    lhs_ty.ty.clone(),
                    rhs_ty.ty.clone(),
                    &context.group_info(),
                    Some(ConstraintCause::Assignment(stmt.id)),
                );
                TypedStmt {
                    id: stmt.id,
                    ty: lhs_ty.ty.clone(),
                    kind: TypedStmtKind::Assignment(lhs_ty, rhs_ty),
                }
            }
            StmtKind::Return(expr) => self.visit_return(stmt, expr, context)?,
            StmtKind::Break => TypedStmt {
                id: stmt.id,
                ty: Ty::Void,
                kind: TypedStmtKind::Break,
            },
            StmtKind::Continue(expr) => {
                let typed_expr = expr
                    .as_ref()
                    .map(|e| self.visit_expr(e, context))
                    .transpose()?;

                if let Some(typed_expr) = typed_expr {
                    let Some(handler_ctx) = self.handler_contexts.last() else {
                        self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                            id: stmt.id,
                            severity: Severity::Error,
                            kind: TypeError::ContinueOutsideHandler,
                        }));
                        return Ok(TypedStmt {
                            id: stmt.id,
                            ty: Ty::Never,
                            kind: TypedStmtKind::Continue(Some(typed_expr)),
                        });
                    };

                    self.constraints.wants_equals_at_with_cause(
                        stmt.id,
                        handler_ctx.ret.clone(),
                        typed_expr.ty.clone(),
                        &context.group_info(),
                        Some(ConstraintCause::Internal),
                    );

                    TypedStmt {
                        id: stmt.id,
                        ty: Ty::Never,
                        kind: TypedStmtKind::Continue(Some(typed_expr)),
                    }
                } else {
                    TypedStmt {
                        id: stmt.id,
                        ty: Ty::Void,
                        kind: TypedStmtKind::Continue(None),
                    }
                }
            }
            StmtKind::Loop(cond, block) => {
                let cond_ty = if let Some(cond) = cond {
                    let cond_ty = self.visit_expr(cond, context)?;
                    self.constraints.wants_equals_at_with_cause(
                        cond.id,
                        cond_ty.ty.clone(),
                        Ty::Bool,
                        &context.group_info(),
                        Some(ConstraintCause::Condition(cond.id)),
                    );
                    cond_ty
                } else {
                    TypedExpr {
                        id: stmt.id,
                        ty: Ty::Bool,
                        kind: TypedExprKind::LiteralTrue,
                    }
                };

                let block = self.infer_block(block, context)?;

                TypedStmt {
                    id: stmt.id,
                    ty: Ty::Void,
                    kind: TypedStmtKind::Loop(cond_ty, block),
                }
            }
            StmtKind::Handling {
                effect_name, body, ..
            } => self.visit_handler_stmt(stmt, effect_name, body, context)?,
            StmtKind::For { .. } => {
                // For loops should be desugared before type inference
                unreachable!("for loops should be desugared before type inference")
            }
        };

        Ok(ty)
    }
}
