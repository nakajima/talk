use super::*;

impl<'a> Lowering<'a> {
    // ----- Types and θ -------------------------------------------------------

    /// The checker type of an expression node, θ-substituted.
    pub(super) fn checker_ty(&self, expr: &Expr, ctx: &Ctx) -> CheckTy {
        let raw = expr.ty.clone();
        let substituted = raw.substitute(&ctx.theta, &Default::default(), &Default::default());
        self.normalize_check_ty(substituted, ctx.unit)
    }

    pub(super) fn borrow_erased_ty(ty: CheckTy) -> CheckTy {
        match ty {
            CheckTy::Borrow(_, inner) | CheckTy::Unique(inner) => *inner,
            other => other,
        }
    }

    pub(super) fn normalize_check_ty(&self, ty: CheckTy, unit: usize) -> CheckTy {
        CheckNormalizer {
            catalog: &self.units[unit].types.catalog,
        }
        .fold_ty(&ty)
    }

    pub(super) fn expr_lambda_ty(&mut self, expr: &Expr, ctx: &Ctx) -> TyId {
        let ty = self.checker_ty(expr, ctx);
        self.map_ty(&ty)
    }

    /// θ contribution from a member's owner: a method/init of a generic
    /// struct (or an inherent extend member) ranges over its owner's rigid
    /// params, which the checker discharges by head substitution rather
    /// than scheme instantiation (`solve/member.rs::try_member`) — so no
    /// instantiation is recorded. Recover the same bindings by matching
    /// the declared self type against the concrete head. Existing θ
    /// entries win.
    pub(super) fn owner_theta(&self, member: Symbol, head: &CheckTy, theta: &mut Theta) {
        let CheckTy::Nominal(head_symbol, args) = head else {
            return;
        };
        for unit in &self.units {
            let catalog = &unit.types.catalog;
            if let Some(info) = catalog.structs.get(head_symbol) {
                let owns = info.methods.values().any(|s| *s == member)
                    || info.statics.values().any(|s| *s == member)
                    || info.inits.contains(&member);
                if owns {
                    for (param, arg) in info.params.iter().zip(args) {
                        theta.entry(*param).or_insert_with(|| arg.clone());
                    }
                    return;
                }
            }
            if let Some(info) = catalog.enums.get(head_symbol)
                && info.methods.values().any(|s| *s == member)
            {
                for (param, arg) in info.params.iter().zip(args) {
                    theta.entry(*param).or_insert_with(|| arg.clone());
                }
                return;
            }
            if let Some(members) = catalog.extend_members.get(head_symbol)
                && let Some(m) = members.values().find(|m| m.symbol == member)
            {
                for (pattern, actual) in m.self_args.iter().zip(args) {
                    crate::types::solve::bind_param_pattern(pattern, actual, theta);
                }
                return;
            }
        }
    }

    /// The full θ for a call to `symbol`: per-call-site instantiation
    /// composed with the enclosing θ; scheme params with no recorded
    /// instantiation (monomorphic recursion typed against the group's
    /// skeleton — THIH §11.6.3) inherit the enclosing specialization's
    /// binding.
    pub(super) fn call_theta(
        &self,
        symbol: Symbol,
        instantiation: Option<&Vec<(Symbol, CheckTy)>>,
        ctx: &Ctx,
    ) -> Theta {
        let mut theta = self.instantiation_at(instantiation, ctx);
        if let Some(scheme) = self.units.iter().find_map(|u| u.types.schemes.get(&symbol)) {
            for param in &scheme.params {
                if !theta.contains_key(&param.symbol)
                    && let Some(ty) = ctx.theta.get(&param.symbol)
                {
                    theta.insert(param.symbol, ty.clone());
                }
            }
        }
        theta
    }

    /// The per-call-site instantiation, composed with the enclosing θ
    /// (`instantiations ∘ θ` — the worklist's edge label).
    pub(super) fn instantiation_at(
        &self,
        instantiation: Option<&Vec<(Symbol, CheckTy)>>,
        ctx: &Ctx,
    ) -> Theta {
        let mut theta = Theta::default();
        if let Some(pairs) = instantiation {
            for (symbol, ty) in pairs {
                let ty = ty.substitute(&ctx.theta, &Default::default(), &Default::default());
                theta.insert(*symbol, ty);
            }
        }
        theta
    }

    /// Checker type → λ_G type. Function types become their CPS form:
    /// (T…) → R turns into Fn([T…, Fn(R, ⊥)], ⊥).
    pub(super) fn map_ty(&mut self, ty: &CheckTy) -> TyId {
        match ty {
            // Uniqueness is static: `*T` is represented as T.
            CheckTy::Unique(inner) => self.map_ty(inner),
            CheckTy::Nominal(symbol, _args) => {
                if *symbol == Symbol::Int {
                    self.p.ty_i64()
                } else if *symbol == Symbol::Float {
                    self.p.ty_f64()
                } else if *symbol == Symbol::Bool {
                    self.p.ty_bool()
                } else if *symbol == Symbol::Void {
                    self.p.ty_void()
                } else if *symbol == Symbol::Never {
                    self.p.ty_bot()
                } else if *symbol == Symbol::RawPtr {
                    self.p.ty_ptr()
                } else if *symbol == Symbol::Byte {
                    self.p.ty(TyKind::Byte)
                } else if self.is_enum(*symbol) {
                    // Enums are tagged variants; type arguments are erased
                    // (monomorphization already specialized every use).
                    self.p.ty(TyKind::Variant(*symbol))
                } else if self.symbol_is_heap(*symbol) {
                    self.p.ty(TyKind::Object(*symbol))
                } else {
                    self.p.ty(TyKind::Boxed(*symbol))
                }
            }
            CheckTy::Borrow(_, inner) => self.map_ty(inner),
            CheckTy::Func(params, ret, _eff) => {
                let mut dom_items: Vec<TyId> = params.iter().map(|t| self.map_ty(t)).collect();
                let ret_ty = self.map_ty(ret);
                let bot = self.p.ty_bot();
                let ret_k = self.p.ty_fn(ret_ty, bot);
                dom_items.push(ret_k);
                let dom = self.p.ty_tuple(&dom_items);
                self.p.ty_fn(dom, bot)
            }
            CheckTy::Tuple(items) => {
                let mapped: Vec<TyId> = items.iter().map(|t| self.map_ty(t)).collect();
                self.p.ty_tuple(&mapped)
            }
            // A closed record row is a tuple in the row's field order
            // (`Row::closed` sorts by label, so the layout is canonical —
            // Leijen's scoped labels, Trends in FP 2005, fixed to closed
            // rows until row polymorphism reaches the backend).
            CheckTy::Record(row) if row.tail.is_none() => {
                let field_tys: Vec<CheckTy> = row.fields.iter().map(|(_, t)| t.clone()).collect();
                let mapped: Vec<TyId> = field_tys.iter().map(|t| self.map_ty(t)).collect();
                self.p.ty_tuple(&mapped)
            }
            CheckTy::Any { protocol, .. } => self.p.ty(TyKind::Existential(protocol.protocol)),
            CheckTy::Param(_) => self.p.ty(TyKind::Erased),
            // A residual solver variable on an error-free program is
            // unconstrained — its instantiation cannot matter, so default
            // it (the ambiguity-defaulting move; statement-position @_ir
            // results are the common case).
            CheckTy::Var(_) => self.p.ty_void(),
            other => {
                self.diagnostics
                    .push(format!("lowering: type not yet supported: {other:?}"));
                self.p.ty_void()
            }
        }
    }
}
