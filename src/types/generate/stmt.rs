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
                StmtValue::Divergent
            }

            StmtKind::If(condition, then_block, else_block) => {
                let cond_ty = self.infer_expr(condition, ctx);
                self.emit_eq(
                    Ty::Nominal(Symbol::Bool, vec![]),
                    cond_ty,
                    condition.id,
                    CtReason::Condition,
                );
                self.infer_block_value(then_block, ctx);
                if let Some(else_block) = else_block {
                    self.infer_block_value(else_block, ctx);
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
                StmtValue::Unit
            }

            StmtKind::Break => StmtValue::Divergent,
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
                StmtValue::Divergent
            }

            StmtKind::For { .. } => {
                // for-loops are desugared by the name resolver; reaching one
                // is a transform bug.
                self.unsupported(stmt.id, "raw for loop");
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
                // The payload types this handler receives — zonked at
                // finalize, once the perform sites have taught the
                // unannotated parameters their types — for the lowerer's
                // capability closure.
                if let Some(&handler) = self.resolved.effect_handler_definitions.get(&stmt.id) {
                    self.artifacts
                        .handler_payload_tys
                        .insert(handler, params.clone());
                    if let Some(binder) = ctx.binder {
                        self.artifacts
                            .handlers_defined
                            .entry(binder)
                            .or_default()
                            .insert(handler);
                    }
                }
                // `continue v` inside this block resumes the perform: v
                // checks against the effect's return type.
                let resume_ty = sig.map(|sig| sig.ret).unwrap_or(Ty::Error);
                self.infer_block_value(body, &ctx.with_handler_ret(resume_ty));
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
            ExprKind::Member(Some(receiver), ..) => {
                let lhs_ty = self.infer_expr(lhs, ctx);
                self.check_assignment_receiver_writable(receiver);
                lhs_ty
            }
            _ => {
                let ty = self.infer_expr(lhs, ctx);
                self.diagnostics
                    .errors
                    .push((TypeError::InvalidAssignmentTarget, lhs.id));
                ty
            }
        }
    }

    fn check_assignment_receiver_writable(&mut self, receiver: &Expr) {
        if let ExprKind::Member(Some(parent), ..) = &receiver.kind {
            self.check_assignment_receiver_writable(parent);
        }

        let Some(receiver_ty) = self.artifacts.node_types.get(&receiver.id) else {
            return;
        };
        if let Ty::Borrow(BorrowKind::Shared, _) = self.store.shallow(receiver_ty) {
            self.diagnostics.errors.push((
                TypeError::AssignThroughSharedBorrow {
                    target: render_assignment_target(receiver),
                    ty: self.store.render(receiver_ty),
                },
                receiver.id,
            ));
        }
    }
}

fn render_assignment_target(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::Variable(name) => name.name_str(),
        ExprKind::Member(Some(receiver), label, _) => {
            format!("{}.{}", render_assignment_target(receiver), label)
        }
        _ => "value".to_string(),
    }
}
