use super::*;

impl<'a> Lowering<'a> {
    // ----- @_ir splices ------------------------------------------------------

    /// Map an inline-IR instruction to a PrimOp: `$n` → lowered bind
    /// expressions, `%n` → the enclosing function's parameters, literals
    /// pass through; the type argument is θ-resolved.
    pub(super) fn splice(
        &mut self,
        instruction: &InlineIRInstruction,
        ctx: &Ctx,
    ) -> Option<ExprId> {
        // `retain` lowers continuation-style (the walk may branch over
        // enum tags), so it can't be a single spliced expression; the
        // continuation path handles it via `splice_retain`.
        if matches!(instruction.kind, InlineIRInstructionKind::Retain { .. }) {
            return None;
        }
        let mut binds = Vec::with_capacity(instruction.binds.len());
        for bind in &instruction.binds {
            // Impure binds (auto-cloned generic values needing retains)
            // take the continuation path in `lower_expr`.
            binds.push(self.try_pure(bind, ctx)?);
        }
        self.splice_with_values(instruction, ctx, &binds)
    }

    /// The splice core over already-lowered bind values — shared by the
    /// pure path (`try_pure` binds) and the continuation path
    /// (`lower_args` binds, which applies per-bind auto-clone retains).
    pub(super) fn splice_with_values(
        &mut self,
        instruction: &InlineIRInstruction,
        ctx: &Ctx,
        binds: &[ExprId],
    ) -> Option<ExprId> {
        let operand = |this: &mut Self, v: &IrValue| -> Option<ExprId> {
            match v {
                IrValue::Bind(i) => binds.get(*i).copied(),
                IrValue::Reg(n) => ctx.params.get(*n as usize).copied(),
                IrValue::Int(i) => Some(this.p.int(*i)),
                IrValue::Float(f) => Some(this.p.float(*f)),
                IrValue::Bool(b) => Some(this.p.bool(*b)),
                IrValue::Void => Some(this.p.void()),
                _ => None,
            }
        };
        use InlineIRInstructionKind as K;
        let (op, operands): (Op, Vec<ExprId>) = match &instruction.kind {
            K::Add { a, b, .. } => (Op::Add, vec![operand(self, a)?, operand(self, b)?]),
            K::Sub { a, b, .. } => (Op::Sub, vec![operand(self, a)?, operand(self, b)?]),
            K::Mul { a, b, .. } => (Op::Mul, vec![operand(self, a)?, operand(self, b)?]),
            K::Div { a, b, .. } => (Op::Div, vec![operand(self, a)?, operand(self, b)?]),
            K::Cmp { lhs, rhs, op, .. } => {
                let cmp = match op {
                    TokenKind::EqualsEquals => CmpOp::Eq,
                    TokenKind::BangEquals => CmpOp::Ne,
                    TokenKind::Less => CmpOp::Lt,
                    TokenKind::LessEquals => CmpOp::Le,
                    TokenKind::Greater => CmpOp::Gt,
                    TokenKind::GreaterEquals => CmpOp::Ge,
                    _ => return None,
                };
                (Op::Cmp(cmp), vec![operand(self, lhs)?, operand(self, rhs)?])
            }
            K::Trunc { val, .. } => (Op::Trunc, vec![operand(self, val)?]),
            K::IsUnique { ptr, .. } => (Op::IsUnique, vec![operand(self, ptr)?]),
            K::IntToFloat { val, .. } => (Op::IToF, vec![operand(self, val)?]),
            K::ByteToInt { val, .. } => (Op::BToI, vec![operand(self, val)?]),
            K::Alloc { ty, count, .. } => {
                // `alloc T count`: count elements of T, sized by
                // TyKind::mem_size (Op::Alloc itself counts bytes). An
                // element the checker left unconstrained (`_alloc(n)`
                // with nothing loading or storing through it — the raw
                // buffers of ChatServer and friends) is a byte buffer:
                // map_ty would default the residual variable to Void,
                // which cannot live in memory.
                let unconstrained = matches!(&ty.kind, TypeAnnotationKind::Nominal { name, .. }
                    if name.symbol().is_ok_and(|s| matches!(ctx.theta.get(&s), Some(CheckTy::Var(_)))));
                let element = if unconstrained {
                    self.p.ty(TyKind::Byte)
                } else {
                    self.splice_ty(ty, ctx)?
                };
                let Some(size) = self.p.ty_kind(element).mem_size() else {
                    self.diagnostics
                        .push("lowering: alloc element type cannot live in memory".into());
                    return None;
                };
                let count = operand(self, count)?;
                let bytes = if size == 1 {
                    count
                } else {
                    let size = self.p.int(size as i64);
                    self.p.mul(count, size)
                };
                (Op::Alloc, vec![bytes])
            }
            K::Load { ty, addr, .. } => {
                let result = self.splice_ty(ty, ctx)?;
                let ptr = operand(self, addr)?;
                return Some(self.p.primop(Op::Load, &[ptr], result));
            }
            // `take T $value` transfers the value without changing its runtime
            // representation. Flow records the bind as consumed.
            K::Take { value, .. } => return operand(self, value),
            // `store T $value $addr`: one sized write; the width comes
            // from the value's λ_G type at the engines.
            K::Store { value, addr, .. } => {
                (Op::Store, vec![operand(self, addr)?, operand(self, value)?])
            }
            // `%? = gep T $addr $index`: pure pointer arithmetic —
            // addr + index · size(T) (no runtime op needed).
            K::Gep {
                ty,
                addr,
                offset_index,
                ..
            } => {
                let element = self.splice_ty(ty, ctx)?;
                let Some(size) = self.p.ty_kind(element).mem_size() else {
                    self.diagnostics
                        .push("lowering: gep element type cannot live in memory".into());
                    return None;
                };
                let addr = operand(self, addr)?;
                let index = operand(self, offset_index)?;
                let offset = if size == 1 {
                    index
                } else {
                    let size = self.p.int(size as i64);
                    self.p.mul(index, size)
                };
                return Some(self.p.add(addr, offset));
            }
            K::Free { ptr } => (Op::Free, vec![operand(self, ptr)?]),
            // Handled by `splice_retain` on the continuation path.
            K::Retain { .. } => return None,
            K::Copy {
                from, to, length, ..
            } => (
                Op::Copy,
                vec![
                    operand(self, from)?,
                    operand(self, to)?,
                    operand(self, length)?,
                ],
            ),
            K::Swap { ty, a, b } => {
                let element = self.splice_ty(ty, ctx)?;
                (
                    Op::Swap(element),
                    vec![operand(self, a)?, operand(self, b)?],
                )
            }
            K::IoWrite { fd, buf, count, .. } => (
                Op::IoWrite,
                vec![
                    operand(self, fd)?,
                    operand(self, buf)?,
                    operand(self, count)?,
                ],
            ),
        };
        let result_ty = match op {
            Op::Cmp(_) | Op::IsUnique => self.p.ty_bool(),
            Op::Trunc | Op::BToI => self.p.ty_i64(),
            Op::IToF => self.p.ty_f64(),
            Op::Alloc => self.p.ty_ptr(),
            Op::Copy | Op::Swap(_) | Op::Store | Op::Free => self.p.ty_void(),
            Op::IoWrite => self.p.ty_i64(),
            _ => self.p.expr_ty(operands[0]),
        };
        Some(self.p.primop(op, &operands, result_ty))
    }

    /// `retain T $value`: rc-bump every refcounted buffer the value owns —
    /// the runtime twin of the drop walk (`lower_retain_value_then`),
    /// θ-resolved per specialization. Continuation-shaped because the walk
    /// may branch (enum payloads switch on the tag), so it takes `k`
    /// directly instead of flowing through `splice_with_values`.
    pub(super) fn splice_retain(
        &mut self,
        annotation: &TypeAnnotation,
        value: &IrValue,
        ctx: &Ctx,
        binds: &[ExprId],
        k: ExprId,
    ) -> ExprId {
        let value = match value {
            IrValue::Bind(i) => binds.get(*i).copied(),
            IrValue::Reg(n) => ctx.params.get(*n as usize).copied(),
            _ => None,
        };
        let (Some(value), Some(ty)) = (value, self.splice_check_ty(annotation, ctx)) else {
            self.diagnostics
                .push("lowering: unsupported @_ir retain operand".into());
            return self.dead_end("unsupported_ir");
        };
        let void = self.p.void();
        let next = self.p.app(k, void);
        self.lower_retain_value_then(ctx, value, &Self::borrow_erased_ty(ty), next)
    }

    /// The checker type named by a splice's type argument, θ-resolved —
    /// the CheckTy sibling of [`Self::splice_ty`] for walks that dispatch
    /// on type structure rather than λ_G layout.
    fn splice_check_ty(&self, annotation: &TypeAnnotation, ctx: &Ctx) -> Option<CheckTy> {
        let TypeAnnotationKind::Nominal { name, .. } = &annotation.kind else {
            return None;
        };
        let symbol = name.symbol().ok()?;
        if let Some(bound) = ctx.theta.get(&symbol) {
            return Some(bound.clone());
        }
        Some(CheckTy::Nominal(symbol, vec![]))
    }

    /// The λ_G type named by a splice's type argument, θ-resolved (`load
    /// Element` inside a Byte specialization is a byte load).
    pub(super) fn splice_ty(&mut self, annotation: &TypeAnnotation, ctx: &Ctx) -> Option<TyId> {
        let TypeAnnotationKind::Nominal { name, .. } = &annotation.kind else {
            self.diagnostics
                .push("lowering: unsupported @_ir type argument".into());
            return None;
        };
        let symbol = name.symbol().ok()?;
        if let Some(bound) = ctx.theta.get(&symbol) {
            let bound = bound.clone();
            return Some(self.map_ty(&bound));
        }
        Some(self.map_ty(&CheckTy::Nominal(symbol, vec![])))
    }
}
