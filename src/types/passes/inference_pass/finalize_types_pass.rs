use derive_visitor::{DriveMut, VisitorMut};
use itertools::Itertools;

use super::InferencePass;
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    name_resolution::symbol::Symbol,
    types::{
        callee::{Callee, Callees},
        constraints::{constraint::Constraint, projection::Projection, type_member::TypeMember},
        infer_ty::Ty,
        type_error::TypeError,
        typed_ast::{TypedBlock, TypedExpr, TypedExprKind, TypedStmt, TypedStmtKind},
    },
};

#[derive(Debug, VisitorMut)]
#[visitor(TypedExpr(enter))]
struct CanonicalizeCalls<'a> {
    callees: &'a Callees,
}

impl CanonicalizeCalls<'_> {
    fn enter_typed_expr(&mut self, expr: &mut TypedExpr) {
        let Some(callee_info) = self.callees.get(&expr.id).cloned() else {
            return;
        };

        let TypedExprKind::Call {
            callee,
            callee_ty,
            args,
            resolved_callee,
            callee_sym,
            ..
        } = &mut expr.kind
        else {
            return;
        };

        *resolved_callee = Some(callee_info.clone());
        let Callee::Method { symbol, .. } = callee_info else {
            return;
        };

        let TypedExprKind::Member { receiver, .. } = &callee.kind else {
            *callee_sym = Some(symbol);
            return;
        };

        let receiver_is_argument = matches!(
            receiver.kind,
            TypedExprKind::Constructor(Symbol::Protocol(_), ..)
                | TypedExprKind::Constructor(..)
                | TypedExprKind::Hole
        );

        let mut direct_args = Vec::with_capacity(args.len() + usize::from(!receiver_is_argument));
        if !receiver_is_argument {
            direct_args.push(receiver.as_ref().clone());
        }
        direct_args.append(args);

        let callee_id = callee.id;
        let callee_type = callee.ty.clone();
        *callee = Box::new(TypedExpr {
            id: callee_id,
            ty: callee_type,
            kind: TypedExprKind::Variable(symbol),
        });
        *callee_ty = callee.ty.clone();
        *args = direct_args;
        *callee_sym = Some(symbol);
    }
}

// Transitional phase wrapper: names post-inference finalization before
// finalization state is ready to move out of InferencePass entirely.
pub(super) struct FinalizeTypesPass<'pass, 'ast> {
    pass: &'pass mut InferencePass<'ast>,
}

impl<'pass, 'ast> FinalizeTypesPass<'pass, 'ast> {
    pub(super) fn new(pass: &'pass mut InferencePass<'ast>) -> Self {
        Self { pass }
    }

    pub(super) fn run(&mut self) {
        self.export_child_types();
        self.report_unsolved();
        self.canonicalize_calls();
    }

    fn export_child_types(&mut self) {
        let child_types = self
            .pass
            .session
            .resolved_names
            .child_types
            .iter()
            .map(|(sym, entries)| (*sym, entries.clone()))
            .collect_vec();

        for (sym, entries) in child_types {
            self.pass
                .session
                .type_catalog
                .child_types
                .entry(sym)
                .or_default()
                .extend(entries);
        }
    }

    fn report_unsolved(&mut self) {
        let unresolved = self
            .pass
            .constraints
            .unsolved()
            .into_iter()
            .cloned()
            .collect_vec();

        for constraint in unresolved {
            let constraint = constraint.apply(&mut self.pass.substitutions, self.pass.session);
            match constraint {
                Constraint::Call(..) => (),
                Constraint::DefaultTy(..) => (),
                Constraint::Equals(..) => (),
                Constraint::HasField(..) => (),
                Constraint::Member(member) => {
                    let ambiguous = self.member_is_ambiguous(&member.receiver, &member.label);
                    if ambiguous || self.is_top_level_expr(member.node_id) {
                        let kind = if ambiguous {
                            TypeError::AmbiguousMember(member.receiver, member.label)
                        } else {
                            TypeError::MemberNotFound(member.receiver, member.label.to_string())
                        };
                        self.pass
                            .diagnostics
                            .insert(AnyDiagnostic::Typing(Diagnostic {
                                id: member.node_id,
                                severity: Severity::Error,
                                kind,
                            }));
                    }
                }
                Constraint::MemberCall(member_call) => {
                    let ambiguous =
                        self.member_is_ambiguous(&member_call.receiver, &member_call.label);
                    if ambiguous || self.is_top_level_expr(member_call.member_node_id) {
                        let kind = if ambiguous {
                            TypeError::AmbiguousMember(member_call.receiver, member_call.label)
                        } else {
                            TypeError::MemberNotFound(
                                member_call.receiver,
                                member_call.label.to_string(),
                            )
                        };
                        self.pass
                            .diagnostics
                            .insert(AnyDiagnostic::Typing(Diagnostic {
                                id: member_call.member_node_id,
                                severity: Severity::Error,
                                kind,
                            }));
                    }
                }
                Constraint::RowSubset(..) => (),
                Constraint::Conforms(conforms) => match &conforms.ty {
                    Ty::Nominal { symbol, .. } | Ty::Primitive(symbol) => {
                        self.pass
                            .diagnostics
                            .insert(AnyDiagnostic::Typing(Diagnostic {
                                id: conforms.conformance_node_id,
                                severity: Severity::Error,
                                kind: TypeError::TypeDoesNotConform {
                                    symbol: *symbol,
                                    protocol_id: conforms.protocol_id,
                                },
                            }));
                    }
                    Ty::Constructor { name, .. } => {
                        self.pass
                            .diagnostics
                            .insert(AnyDiagnostic::Typing(Diagnostic {
                                id: conforms.conformance_node_id,
                                severity: Severity::Error,
                                kind: TypeError::TypeDoesNotConform {
                                    symbol: name
                                        .symbol()
                                        .unwrap_or_else(|_| unreachable!("did not resolve name")),
                                    protocol_id: conforms.protocol_id,
                                },
                            }));
                    }
                    Ty::Var { id, .. }
                        if matches!(
                            self.pass.session.lookup_type_param_origin(*id),
                            Some(Ty::Param(_, bounds)) if bounds.contains(&conforms.protocol_id)
                        ) => {}
                    ty => {
                        tracing::error!("did not solve {conforms:?}");
                        self.pass
                            .diagnostics
                            .insert(AnyDiagnostic::Typing(Diagnostic {
                                id: conforms.conformance_node_id,
                                severity: Severity::Error,
                                kind: TypeError::TypeCannotConform {
                                    ty: ty.clone(),
                                    protocol_id: conforms.protocol_id,
                                },
                            }));
                    }
                },
                Constraint::TypeMember(type_member) => self.report_type_member(type_member),
                Constraint::Projection(projection) => self.report_projection(projection),
            }
        }
    }

    fn canonicalize_calls(&mut self) {
        let callees = self.pass.session.callees_snapshot();
        let mut canonicalizer = CanonicalizeCalls { callees: &callees };
        for decl in &mut self.pass.root_decls {
            decl.drive_mut(&mut canonicalizer);
        }
        for stmt in &mut self.pass.root_stmts {
            stmt.drive_mut(&mut canonicalizer);
        }
    }

    fn member_is_ambiguous(&mut self, receiver: &Ty, label: &crate::label::Label) -> bool {
        let bounds = match receiver {
            Ty::Param(_, bounds) => bounds.clone(),
            Ty::Var { id, .. } => match self.pass.session.lookup_type_param_origin(*id) {
                Some(Ty::Param(_, bounds)) => bounds,
                _ => vec![],
            },
            _ => vec![],
        };

        let mut candidates = vec![];
        for protocol_id in bounds {
            if let Some((requirement, _source)) =
                self.pass.session.lookup_member(&protocol_id.into(), label)
                && !candidates.contains(&requirement)
            {
                candidates.push(requirement);
            }
        }

        candidates.len() > 1
    }

    fn is_top_level_expr(&self, id: crate::node_id::NodeID) -> bool {
        self.pass
            .root_stmts
            .iter()
            .any(|stmt| Self::stmt_contains_expr(stmt, id))
    }

    fn stmt_contains_expr(stmt: &TypedStmt, id: crate::node_id::NodeID) -> bool {
        match &stmt.kind {
            TypedStmtKind::Expr(expr) => Self::expr_contains(expr, id),
            TypedStmtKind::Assignment(lhs, rhs) => {
                Self::expr_contains(lhs, id) || Self::expr_contains(rhs, id)
            }
            TypedStmtKind::Return(expr) | TypedStmtKind::Continue(expr) => expr
                .as_ref()
                .is_some_and(|expr| Self::expr_contains(expr, id)),
            TypedStmtKind::Loop(cond, body) => {
                Self::expr_contains(cond, id) || Self::block_contains_expr(body, id)
            }
            TypedStmtKind::Handler { func, .. } => Self::block_contains_expr(&func.body, id),
            TypedStmtKind::Break => false,
        }
    }

    fn block_contains_expr(block: &TypedBlock, id: crate::node_id::NodeID) -> bool {
        block.body.iter().any(|node| match node {
            crate::types::typed_ast::TypedNode::Expr(expr) => Self::expr_contains(expr, id),
            crate::types::typed_ast::TypedNode::Stmt(stmt) => Self::stmt_contains_expr(stmt, id),
            crate::types::typed_ast::TypedNode::Decl(_) => false,
        })
    }

    fn expr_contains(expr: &TypedExpr, id: crate::node_id::NodeID) -> bool {
        if expr.id == id {
            return true;
        }

        match &expr.kind {
            TypedExprKind::LiteralArray(items) | TypedExprKind::Tuple(items) => {
                items.iter().any(|item| Self::expr_contains(item, id))
            }
            TypedExprKind::Block(block) => Self::block_contains_expr(block, id),
            TypedExprKind::Call { callee, args, .. } => {
                Self::expr_contains(callee, id)
                    || args.iter().any(|arg| Self::expr_contains(arg, id))
            }
            TypedExprKind::CallEffect { args, .. } => {
                args.iter().any(|arg| Self::expr_contains(arg, id))
            }
            TypedExprKind::Member { receiver, .. } => Self::expr_contains(receiver, id),
            TypedExprKind::Func(func) => Self::block_contains_expr(&func.body, id),
            TypedExprKind::If(cond, conseq, alt) => {
                Self::expr_contains(cond, id)
                    || Self::block_contains_expr(conseq, id)
                    || Self::block_contains_expr(alt, id)
            }
            TypedExprKind::Match(scrutinee, arms) => {
                Self::expr_contains(scrutinee, id)
                    || arms
                        .iter()
                        .any(|arm| Self::block_contains_expr(&arm.body, id))
            }
            TypedExprKind::RecordLiteral { fields } => fields
                .iter()
                .any(|field| Self::expr_contains(&field.value, id)),
            TypedExprKind::Hole
            | TypedExprKind::InlineIR(_)
            | TypedExprKind::LiteralInt(_)
            | TypedExprKind::LiteralFloat(_)
            | TypedExprKind::LiteralTrue
            | TypedExprKind::LiteralFalse
            | TypedExprKind::LiteralString(_)
            | TypedExprKind::Variable(_)
            | TypedExprKind::Constructor(_, _) => false,
        }
    }

    fn report_projection(&mut self, projection: Projection) {
        if self.pass.session.can_generalize_projection(
            projection.protocol_id,
            &projection.base,
            &projection.label,
            &mut self.pass.substitutions,
        ) {
            return;
        }

        self.pass
            .diagnostics
            .insert(AnyDiagnostic::Typing(Diagnostic {
                id: projection.node_id,
                severity: Severity::Error,
                kind: TypeError::UnknownAssociatedType {
                    base: projection.base,
                    label: projection.label,
                },
            }));
    }

    fn report_type_member(&mut self, type_member: TypeMember) {
        self.pass
            .diagnostics
            .insert(AnyDiagnostic::Typing(Diagnostic {
                id: type_member.node_id,
                severity: Severity::Error,
                kind: TypeError::UnknownTypeMember {
                    base: type_member.base,
                    member: type_member.name,
                },
            }));
    }
}
