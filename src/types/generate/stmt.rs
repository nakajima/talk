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
            | ExprKind::Variable(_)
            | ExprKind::Constructor(_) => false,
        }
    }
}
