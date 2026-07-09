use super::*;

impl<'s, 'a> BodyChecker<'s, 'a> {
    pub(super) fn infer_stmt(&mut self, stmt: &Stmt, ctx: &Ctx) -> StmtValue {
        match &stmt.kind {
            StmtKind::Expr(expr) => StmtValue::Value(self.infer_expr(expr, ctx)),

            StmtKind::Return(value) => {
                let expected = ctx.ret.clone();
                match value {
                    Some(expr) => self.check_expr(expr, &expected, CtReason::Return, ctx),
                    None => self.emit_eq(expected, Ty::unit(), stmt.id, CtReason::Return),
                }
                StmtValue::divergent()
            }

            StmtKind::If(condition, then_block, else_block) => {
                let cond_ty = self.infer_expr(condition, ctx);
                self.emit_eq(
                    Ty::Nominal(Symbol::Bool, vec![]),
                    cond_ty,
                    condition.id,
                    CtReason::Condition,
                );
                let then_ty = self.infer_block_value(then_block, ctx);
                if let Some(else_block) = else_block {
                    let else_ty = self.infer_block_value(else_block, ctx);
                    if then_ty.is_never() && else_ty.is_never() {
                        return StmtValue::divergent();
                    }
                }
                StmtValue::Unit
            }

            StmtKind::Assignment(lhs, rhs) => {
                let lhs_ty = self.infer_assignment_target(lhs, ctx);
                self.check_expr(rhs, &lhs_ty, CtReason::Assignment, ctx);
                StmtValue::Unit
            }

            StmtKind::Loop(condition, body) => {
                if let Some(condition) = condition {
                    let cond_ty = self.infer_expr(condition, ctx);
                    self.emit_eq(
                        Ty::Nominal(Symbol::Bool, vec![]),
                        cond_ty,
                        condition.id,
                        CtReason::Condition,
                    );
                }
                self.infer_block_value(body, ctx);
                if condition.is_none() && !Self::block_breaks_current_loop(body) {
                    StmtValue::divergent_loop()
                } else {
                    StmtValue::Unit
                }
            }

            StmtKind::Break => StmtValue::divergent(),
            StmtKind::Continue(payload) => {
                // A bare `continue` re-enters the enclosing loop; with a
                // payload it resumes the enclosing handler's perform.
                if let Some(expr) = payload {
                    match ctx.handler_ret.clone() {
                        Some(expected) => {
                            self.check_expr(expr, &expected, CtReason::Apply, ctx);
                        }
                        None => self.unsupported(
                            stmt.id,
                            "continue with a value outside an effect handler",
                        ),
                    }
                }
                StmtValue::divergent()
            }

            StmtKind::For {
                iterable,
                source_mode,
                pattern,
                body,
                hidden_source,
                hidden_iter,
                ..
            } => {
                // `for` is checked, not desugared: the implicit `iter()` and
                // `next()` calls resolve through the ordinary member/call
                // machinery on checker-minted ids, and the loop binder is
                // the payload of `next()`'s `.some` — exactly
                // `Iterator.Element`. The resolved facts are published as
                // this statement's ForPlan; the typed-tree build elaborates
                // the loop into ordinary nodes at those ids.
                use crate::node_kinds::call_arg::ArgMode;
                let file = stmt.id.0;
                let iter_callee_id = self.artifacts.synthetic_id(file);
                let iter_call_id = self.artifacts.synthetic_id(file);
                let next_callee_id = self.artifacts.synthetic_id(file);
                let next_call_id = self.artifacts.synthetic_id(file);
                let write_back_callee_id = self.artifacts.synthetic_id(file);
                let write_back_call_id = self.artifacts.synthetic_id(file);
                let write_back_arg_id = self.artifacts.synthetic_id(file);
                let finish_callee_id = self.artifacts.synthetic_id(file);
                let finish_call_id = self.artifacts.synthetic_id(file);
                let iter_label = match source_mode {
                    Some(ArgMode::Consume) => "into_iter",
                    Some(ArgMode::Mut) => "iter_mut",
                    Some(ArgMode::Copy | ArgMode::Borrow) => {
                        self.unsupported(stmt.id, "this marker on a `for` source");
                        "iter"
                    }
                    None => "iter",
                };
                // Mut iteration takes the source and restores it at loop
                // end: the source must be an assignable place, and the
                // binder a single name (the write-back reads it).
                if matches!(source_mode, Some(ArgMode::Mut)) {
                    if !matches!(
                        iterable.kind,
                        crate::node_kinds::expr::ExprKind::Variable(_)
                    ) {
                        self.unsupported(stmt.id, "`mut` iteration over a non-variable source");
                    }
                    if pattern.collect_binders().len() != 1 {
                        self.unsupported(stmt.id, "`mut` iteration with a destructuring binder");
                    }
                }
                let iterable_ty = self.infer_expr(iterable, ctx);
                if let Ok(symbol) = hidden_source.symbol() {
                    self.mono.insert(symbol, iterable_ty.clone());
                }

                let iter_member = Ty::Var(self.store.fresh_ty(self.level, iter_callee_id));
                self.artifacts
                    .node_types
                    .insert(iter_callee_id, iter_member.clone());
                let iterator_ty =
                    self.finish_call(iter_call_id, iter_member.clone(), &[], &None, ctx);
                self.artifacts
                    .node_types
                    .insert(iter_call_id, iterator_ty.clone());
                self.wanteds.push(Constraint::HasMember {
                    receiver: iterable_ty,
                    label: Label::Named(iter_label.into()),
                    member: iter_member,
                    origin: CtOrigin::new(iter_callee_id, CtReason::Apply),
                });
                if let Ok(symbol) = hidden_iter.symbol() {
                    self.mono.insert(symbol, iterator_ty.clone());
                }

                let next_member = Ty::Var(self.store.fresh_ty(self.level, next_callee_id));
                self.artifacts
                    .node_types
                    .insert(next_callee_id, next_member.clone());
                let next_result_ty =
                    self.finish_call(next_call_id, next_member.clone(), &[], &None, ctx);
                self.artifacts
                    .node_types
                    .insert(next_call_id, next_result_ty.clone());
                self.wanteds.push(Constraint::HasMember {
                    receiver: Ty::Borrow(Perm::Exclusive, Box::new(iterator_ty.clone())),
                    label: Label::Named("next".into()),
                    member: next_member,
                    origin: CtOrigin::new(next_callee_id, CtReason::Apply),
                });

                // The element is `.some`'s payload — the same deferred
                // variant machinery `if let .some(x) = it.next()` uses, so
                // no compiler-level knowledge of Optional is needed.
                let element_ty = Ty::Var(self.store.fresh_ty(self.level, pattern.id));
                self.wanteds.push(Constraint::HasVariant {
                    enum_ty: next_result_ty.clone(),
                    label: Label::Named("some".into()),
                    payload: vec![element_ty.clone()],
                    ctor: None,
                    origin: CtOrigin::new(pattern.id, CtReason::Pattern),
                });
                self.check_pattern(pattern, &element_ty);
                let body_ty = self.infer_block_value(body, ctx);

                if matches!(source_mode, Some(ArgMode::Mut)) {
                    // write_back(value): checked as a real call so its
                    // effects join the ambient row; the argument is a
                    // phantom read of the loop binder.
                    if let Some((_, binder)) = pattern.collect_binders().first().copied() {
                        let binder_name = crate::name::Name::Resolved(
                            binder,
                            self.resolved
                                .symbol_names
                                .get(&binder)
                                .cloned()
                                .unwrap_or_default(),
                        );
                        let phantom = crate::node_kinds::expr::Expr {
                            id: write_back_arg_id,
                            span: pattern.span,
                            kind: crate::node_kinds::expr::ExprKind::Variable(binder_name),
                        };
                        let arg = crate::node_kinds::call_arg::CallArg {
                            id: write_back_arg_id,
                            label: Label::Positional(0),
                            label_span: pattern.span,
                            value: phantom,
                            span: pattern.span,
                            mode: None,
                            mode_span: None,
                        };
                        let wb_member =
                            Ty::Var(self.store.fresh_ty(self.level, write_back_callee_id));
                        self.artifacts
                            .node_types
                            .insert(write_back_callee_id, wb_member.clone());
                        let wb_result = self.finish_call(
                            write_back_call_id,
                            wb_member.clone(),
                            std::slice::from_ref(&arg),
                            &None,
                            ctx,
                        );
                        self.artifacts
                            .node_types
                            .insert(write_back_call_id, wb_result);
                        self.wanteds.push(Constraint::HasMember {
                            receiver: Ty::Borrow(Perm::Exclusive, Box::new(iterator_ty.clone())),
                            label: Label::Named("write_back".into()),
                            member: wb_member,
                            origin: CtOrigin::new(write_back_callee_id, CtReason::Apply),
                        });
                    }

                    // finish(): the consuming restore; its result assigns
                    // back to the source place.
                    let finish_member = Ty::Var(self.store.fresh_ty(self.level, finish_callee_id));
                    self.artifacts
                        .node_types
                        .insert(finish_callee_id, finish_member.clone());
                    let finish_result =
                        self.finish_call(finish_call_id, finish_member.clone(), &[], &None, ctx);
                    self.artifacts
                        .node_types
                        .insert(finish_call_id, finish_result.clone());
                    self.wanteds.push(Constraint::HasMember {
                        receiver: iterator_ty.clone(),
                        label: Label::Named("finish".into()),
                        member: finish_member,
                        origin: CtOrigin::new(finish_callee_id, CtReason::Apply),
                    });
                    let source_ty = self.infer_assignment_target(iterable, ctx);
                    self.emit_eq(
                        source_ty,
                        finish_result,
                        finish_call_id,
                        CtReason::Assignment,
                    );
                }
                self.artifacts.for_plans.insert(
                    stmt.id,
                    ForPlan {
                        iter_callee_id: iter_callee_id,
                        iter_call_id: iter_call_id,
                        next_callee_id: next_callee_id,
                        next_call_id: next_call_id,
                        write_back_callee_id: write_back_callee_id,
                        write_back_call_id: write_back_call_id,
                        write_back_arg_id: write_back_arg_id,
                        finish_callee_id: finish_callee_id,
                        finish_call_id: finish_call_id,
                        iterator_ty,
                        element_ty,
                        next_result_ty,
                        body_ty,
                    },
                );
                StmtValue::Unit
            }

            StmtKind::Handling {
                effect_name, body, ..
            } => {
                // Handler block parameters take the effect's declared
                // parameter types; unannotated effect parameters are refined
                // by the perform sites that route to this handler.
                let sig = effect_name
                    .symbol()
                    .ok()
                    .and_then(|symbol| self.catalog.effects.get(&symbol))
                    .cloned();
                let params = sig
                    .as_ref()
                    .map(|sig| sig.params.clone())
                    .unwrap_or_default();
                // A handler block either ignores every payload (no
                // arguments) or names all of them.
                if !body.args.is_empty() && body.args.len() != params.len() {
                    self.diagnostics.errors.push((
                        TypeError::ArityMismatch {
                            expected: params.len(),
                            found: body.args.len(),
                        },
                        stmt.id,
                    ));
                }
                for (arg, param) in body.args.iter().zip(&params) {
                    if let Ok(symbol) = arg.name.symbol() {
                        self.mono.insert(symbol, param.clone());
                    }
                }
                // `continue v` inside this block resumes the perform: v
                // checks against the effect's return type.
                let resume_ty = sig.map(|sig| sig.ret).unwrap_or(Ty::Error);
                let body_ty = self.infer_block_value(body, &ctx.with_handler_ret(resume_ty));
                // A handler that completes without resuming ABORTS the
                // handled scope with its value, so that value must be what
                // the scope produces (`ctx.ret`: the enclosing return, or
                // the top-level scope's value). An always-resuming body is
                // Never and constrains nothing.
                if !body_ty.is_never() {
                    self.emit_eq(ctx.ret.clone(), body_ty, stmt.id, CtReason::Body);
                }
                StmtValue::Unit
            }
        }
    }

    /// Local lets: monomorphic, never generalized (OutsideIn(X) §4.2 /
    /// MonoLocalBinds).
    pub(super) fn check_local_decl(&mut self, decl: &Decl, ctx: &Ctx) {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                type_annotation,
                rhs,
            } => {
                // Unannotated lets take the rhs's inferred type directly —
                // value-directed, so a variant pattern (or a later match on
                // the binder) sees a concrete head instead of a constraint
                // variable the solver has not run on yet.
                let ty = match (type_annotation, rhs) {
                    (Some(annotation), _) => {
                        let ty = self.lower_annotation(annotation);
                        if let Some(rhs) = rhs {
                            self.check_expr(rhs, &ty, CtReason::Annotation, ctx);
                        }
                        ty
                    }
                    (None, Some(rhs)) => self.infer_expr(rhs, ctx),
                    (None, None) => Ty::Var(self.store.fresh_ty(self.level, decl.id)),
                };
                match &lhs.kind {
                    PatternKind::Bind(name) => {
                        if let Ok(symbol) = name.symbol() {
                            // A hoisted func binder already holds the
                            // placeholder this block's bodies unified
                            // against; tie it to the definition's type.
                            if let Some(existing) = self.mono.get(&symbol).cloned() {
                                self.emit_eq(existing, ty.clone(), decl.id, CtReason::Recursion);
                            }
                            self.mono.insert(symbol, ty);
                        }
                    }
                    // Destructuring let: the lhs is a pattern checked
                    // against the rhs type; its binders enter the
                    // monomorphic environment exactly like plain lets.
                    _ => {
                        self.check_pattern(lhs, &ty);
                    }
                }
            }
            DeclKind::Import(_) | DeclKind::TypeAlias(..) => {}
            other => self.unsupported(decl.id, decl_kind_name(other)),
        }
    }

    fn infer_assignment_target(&mut self, lhs: &Expr, ctx: &Ctx) -> Ty {
        match &lhs.kind {
            ExprKind::Variable(_) => self.infer_expr(lhs, ctx),
            ExprKind::Member(Some(_), ..) => self.infer_expr(lhs, ctx),
            _ => {
                let ty = self.infer_expr(lhs, ctx);
                self.diagnostics
                    .errors
                    .push((TypeError::InvalidAssignmentTarget, lhs.id));
                ty
            }
        }
    }

    fn block_breaks_current_loop(block: &Block) -> bool {
        block.body.iter().any(Self::node_breaks_current_loop)
    }

    fn node_breaks_current_loop(node: &Node) -> bool {
        match node {
            Node::Decl(decl) => Self::decl_breaks_current_loop(decl),
            Node::Stmt(stmt) => Self::stmt_breaks_current_loop(stmt),
            Node::Expr(expr) => Self::expr_breaks_current_loop(expr),
            Node::Block(block) => Self::block_breaks_current_loop(block),
            Node::MatchArm(arm) => Self::block_breaks_current_loop(&arm.body),
            Node::RecordField(field) => Self::expr_breaks_current_loop(&field.value),
            Node::CallArg(arg) => Self::expr_breaks_current_loop(&arg.value),
            Node::Func(_) => false,
            _ => false,
        }
    }

    fn decl_breaks_current_loop(decl: &Decl) -> bool {
        match &decl.kind {
            DeclKind::Let { rhs, .. } => rhs.as_ref().is_some_and(Self::expr_breaks_current_loop),
            _ => false,
        }
    }

    fn stmt_breaks_current_loop(stmt: &Stmt) -> bool {
        match &stmt.kind {
            StmtKind::Break => true,
            StmtKind::Expr(expr)
            | StmtKind::Return(Some(expr))
            | StmtKind::Continue(Some(expr)) => Self::expr_breaks_current_loop(expr),
            StmtKind::If(condition, then_block, else_block) => {
                Self::expr_breaks_current_loop(condition)
                    || Self::block_breaks_current_loop(then_block)
                    || else_block
                        .as_ref()
                        .is_some_and(Self::block_breaks_current_loop)
            }
            StmtKind::Assignment(lhs, rhs) => {
                Self::expr_breaks_current_loop(lhs) || Self::expr_breaks_current_loop(rhs)
            }
            StmtKind::Loop(..) | StmtKind::For { .. } => false,
            StmtKind::Handling { body, .. } => Self::block_breaks_current_loop(body),
            StmtKind::Return(None) | StmtKind::Continue(None) => false,
        }
    }

    fn expr_breaks_current_loop(expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::LiteralArray(items) | ExprKind::Tuple(items) => {
                items.iter().any(Self::expr_breaks_current_loop)
            }
            ExprKind::Unary(_, inner) | ExprKind::As(inner, _) => {
                Self::expr_breaks_current_loop(inner)
            }
            ExprKind::Binary(lhs, _, rhs) => {
                Self::expr_breaks_current_loop(lhs) || Self::expr_breaks_current_loop(rhs)
            }
            ExprKind::Block(block) => Self::block_breaks_current_loop(block),
            ExprKind::Call {
                callee,
                args,
                trailing_block: _,
                ..
            } => {
                Self::expr_breaks_current_loop(callee)
                    || args
                        .iter()
                        .any(|arg| Self::expr_breaks_current_loop(&arg.value))
            }
            ExprKind::Member(receiver, ..) => receiver
                .as_ref()
                .is_some_and(|receiver| Self::expr_breaks_current_loop(receiver)),
            ExprKind::Func(_) => false,
            ExprKind::If(..) => {
                unreachable!("if expressions are desugared to match before type checking")
            }
            ExprKind::Match(scrutinee, arms) => {
                Self::expr_breaks_current_loop(scrutinee)
                    || arms
                        .iter()
                        .any(|arm| Self::block_breaks_current_loop(&arm.body))
            }
            ExprKind::RecordLiteral { fields, spread } => {
                fields
                    .iter()
                    .any(|field| Self::expr_breaks_current_loop(&field.value))
                    || spread
                        .as_ref()
                        .is_some_and(|spread| Self::expr_breaks_current_loop(spread))
            }
            ExprKind::CallEffect { args, .. } => args
                .iter()
                .any(|arg| Self::expr_breaks_current_loop(&arg.value)),
            ExprKind::Incomplete(_)
            | ExprKind::InlineIR(_)
            | ExprKind::LiteralInt(_)
            | ExprKind::LiteralFloat(_)
            | ExprKind::LiteralTrue
            | ExprKind::LiteralFalse
            | ExprKind::LiteralString(_)
            | ExprKind::LiteralCharacter(_)
            | ExprKind::Variable(_)
            | ExprKind::Constructor(_) => false,
        }
    }
}
