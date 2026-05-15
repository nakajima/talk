use itertools::Itertools;
use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    formatter,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        stmt::{Stmt, StmtKind},
    },
    types::{
        constraints::constraint::ConstraintCause,
        infer_ty::{Level, Ty},
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::curry,
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
            #[allow(clippy::todo)]
            ExprKind::RowVariable(..) => todo!(),
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
