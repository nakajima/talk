use super::*;

impl<'a> Lowering<'a> {
    // ----- Indexing -------------------------------------------------------

    /// One pass over every unit's ASTs collecting all lowerable bodies:
    /// top-level funcs (lowered to lets by the resolver), struct methods,
    /// extend members (witnesses + inherents), protocol defaults.
    pub(super) fn index_sources(&mut self) {
        for unit_index in 0..self.units.len() {
            let unit_asts = self.units[unit_index].asts;
            for ast in unit_asts.values() {
                for root in &ast.roots {
                    let Node::Decl(decl) = root else { continue };
                    self.index_decl(unit_index, decl);
                }
            }
            // Requirement signatures for default-body specialization.
            for info in self.units[unit_index].types.catalog.protocols.values() {
                for requirement in info.requirements.values() {
                    self.requirement_sigs
                        .insert(requirement.symbol, requirement.sig.clone());
                }
            }
        }
    }

    pub(super) fn index_decl(&mut self, unit: usize, decl: &'a Decl) {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                rhs: Some(rhs),
                ..
            } => {
                if let PatternKind::Bind(name) = &lhs.kind
                    && let Ok(symbol) = name.symbol()
                {
                    match &rhs.kind {
                        ExprKind::Func(func) => {
                            self.index_callable(unit, symbol, &func.params, &func.body, false);
                        }
                        _ => {
                            self.globals.insert(symbol, (unit, rhs));
                        }
                    }
                }
            }
            DeclKind::Struct { body, .. }
            | DeclKind::Enum { body, .. }
            | DeclKind::Protocol { body, .. } => {
                for member in &body.decls {
                    self.index_decl(unit, member);
                }
            }
            DeclKind::Extend { body, .. } => {
                for member in &body.decls {
                    self.index_decl(unit, member);
                }
            }
            DeclKind::Method { func, .. } => {
                if let Ok(symbol) = func.name.symbol() {
                    self.index_callable(unit, symbol, &func.params, &func.body, false);
                }
            }
            DeclKind::Init { name, params, body } => {
                if let Ok(symbol) = name.symbol() {
                    self.index_callable(unit, symbol, params, body, true);
                }
            }
            _ => {}
        }
    }

    pub(super) fn index_callable(
        &mut self,
        unit: usize,
        symbol: Symbol,
        params: &'a [crate::hir::Parameter],
        body: &'a Block,
        is_init: bool,
    ) {
        // A `mut func` is internally `self: &mut Self`, which uses the
        // inout calling convention: ret carries [result, Self] and the
        // caller writes Self back. Initializers are excluded because their
        // self starts blank and is returned as the result instead.
        if !is_init && params.first().is_some_and(Self::is_mutable_self_param) {
            // A `'heap` receiver mutates in place through the handle — no
            // inout pair, no caller write-back.
            let heap_self = params.first().is_some_and(|param| {
                matches!(
                    self.units[unit].types.node_types.get(&param.id),
                    Some(crate::types::ty::Ty::Borrow(_, inner))
                        if matches!(**inner, crate::types::ty::Ty::Nominal(inner_symbol, _)
                            if self.units[unit].types.catalog.is_heap(inner_symbol))
                ) || matches!(
                    self.units[unit].types.node_types.get(&param.id),
                    Some(crate::types::ty::Ty::Nominal(self_symbol, _))
                        if self.units[unit].types.catalog.is_heap(*self_symbol)
                )
            });
            if !heap_self {
                self.mutating.insert(symbol);
            }
        }
        self.sources
            .insert(symbol, FuncSource { unit, params, body });
    }

    pub(super) fn is_mutable_self_param(param: &crate::hir::Parameter) -> bool {
        param.name.name_str() == "self"
            && matches!(
                param
                    .type_annotation
                    .as_ref()
                    .map(|annotation| &annotation.kind),
                Some(TypeAnnotationKind::Borrow { mutable: true, .. })
            )
    }

    // ----- Effect capabilities (dynamic-extent handlers) ------------------

    /// The capability parameters a symbol's specialization takes: one per
    /// user-effect OCCURRENCE in its latent row, θ-substituted, deduped,
    /// in a canonical (label, instantiation) order shared by `demand`,
    /// `lower_function`, and every call site. Core effects ('io, 'async,
    /// 'alloc) are the runtime's and route to primops, not capabilities.
    pub(super) fn cap_entries_of(
        &self,
        symbol: Symbol,
        theta: &Theta,
    ) -> Vec<(Symbol, Vec<CheckTy>)> {
        let row = self
            .units
            .iter()
            .find_map(|u| u.types.schemes.get(&symbol).map(|s| &s.ty))
            .and_then(|ty| match ty {
                CheckTy::Func(_, _, eff) => Some(eff),
                _ => None,
            });
        let Some(row) = row else {
            return vec![];
        };
        let mut entries: Vec<(Symbol, Vec<CheckTy>)> = row
            .effects
            .iter()
            .filter(|entry| {
                entry.effect.external_module_id() != Some(crate::compiling::module::ModuleId::Core)
            })
            .map(|entry| {
                let args = entry
                    .args
                    .iter()
                    .map(|ty| ty.substitute(theta, &Default::default(), &Default::default()))
                    .collect();
                (entry.effect, args)
            })
            .collect();
        entries.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
        entries.dedup();
        entries
    }

    /// The effect's declared signature with its generics bound at `args`.
    pub(super) fn effect_sig_at(
        &mut self,
        effect: Symbol,
        args: &[CheckTy],
    ) -> Option<crate::types::catalog::EffectSig> {
        let sig = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.effects.get(&effect).cloned())?;
        if sig.generics.len() != args.len() {
            self.diagnostics.push(format!(
                "lowering: '{effect} expects {} type arguments, got {}",
                sig.generics.len(),
                args.len()
            ));
            return None;
        }
        let theta: Theta = sig
            .generics
            .iter()
            .copied()
            .zip(args.iter().cloned())
            .collect();
        Some(crate::types::catalog::EffectSig {
            generics: vec![],
            predicates: vec![],
            params: sig
                .params
                .iter()
                .map(|ty| ty.substitute(&theta, &Default::default(), &Default::default()))
                .collect(),
            ret: sig
                .ret
                .substitute(&theta, &Default::default(), &Default::default()),
        })
    }

    /// The capability domain for an effect instantiation: its payload
    /// types plus the resumption continuation — `(payloads…, Fn(ret, ⊥))`.
    /// Built from the finalized catalog signature, so a materialized
    /// capability closure and every demanded cap parameter agree on the
    /// type.
    pub(super) fn cap_dom_items(&mut self, effect: Symbol, args: &[CheckTy]) -> Option<Vec<TyId>> {
        let sig = self.effect_sig_at(effect, args)?;
        let mut items = Vec::with_capacity(sig.params.len() + 1);
        for param in &sig.params {
            if matches!(param, CheckTy::Var(_)) {
                self.diagnostics.push(
                    "lowering: effect parameter type unknown (annotate the effect declaration)"
                        .into(),
                );
                return None;
            }
            items.push(self.map_ty(param));
        }
        let bot = self.p.ty_bot();
        let resume_value_ty = self.map_ty(&sig.ret);
        items.push(self.p.ty_fn(resume_value_ty, bot));
        Some(items)
    }

    /// The capability's λ_G type: `Fn((payloads…, resume), ⊥)`.
    pub(super) fn cap_ty(&mut self, effect: Symbol, args: &[CheckTy]) -> Option<TyId> {
        let items = self.cap_dom_items(effect, args)?;
        let dom = self.p.ty_tuple(&items);
        let bot = self.p.ty_bot();
        Some(self.p.ty_fn(dom, bot))
    }

    pub(super) fn diagnose_unsupported_handlers(&mut self) {
        for unit_index in 0..self.units.len() {
            let asts = self.units[unit_index].asts;
            for ast in asts.values() {
                for root in &ast.roots {
                    self.diagnose_unsupported_handlers_in_node(unit_index, root);
                }
            }
        }
    }

    pub(super) fn diagnose_unsupported_handlers_in_node(&mut self, unit: usize, node: &Node) {
        match node {
            Node::Stmt(stmt) => self.diagnose_unsupported_handlers_in_stmt(unit, stmt),
            Node::Decl(decl) => match &decl.kind {
                DeclKind::Let { rhs: Some(rhs), .. } => {
                    self.diagnose_unsupported_handlers_in_expr(unit, rhs);
                }
                DeclKind::Struct { body, .. }
                | DeclKind::Enum { body, .. }
                | DeclKind::Protocol { body, .. }
                | DeclKind::Extend { body, .. } => {
                    for decl in &body.decls {
                        self.diagnose_unsupported_handlers_in_node(unit, &Node::Decl(decl.clone()));
                    }
                }
                DeclKind::Method { func, .. } => {
                    self.diagnose_unsupported_handlers_in_block(unit, &func.body);
                }
                DeclKind::Init { body, .. } => {
                    self.diagnose_unsupported_handlers_in_block(unit, body);
                }
                _ => {}
            },
            Node::Expr(expr) => self.diagnose_unsupported_handlers_in_expr(unit, expr),
        }
    }

    pub(super) fn diagnose_unsupported_handlers_in_block(&mut self, unit: usize, block: &Block) {
        for node in &block.body {
            self.diagnose_unsupported_handlers_in_node(unit, node);
        }
    }

    pub(super) fn diagnose_unsupported_handlers_in_stmt(&mut self, unit: usize, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Handling { body, .. } => {
                self.diagnose_unsupported_handlers_in_block(unit, body);
            }
            StmtKind::Expr(expr)
            | StmtKind::Return(Some(expr))
            | StmtKind::Continue(Some(expr)) => {
                self.diagnose_unsupported_handlers_in_expr(unit, expr);
            }
            StmtKind::If(_, then_block, else_block) => {
                self.diagnose_unsupported_handlers_in_block(unit, then_block);
                if let Some(else_block) = else_block {
                    self.diagnose_unsupported_handlers_in_block(unit, else_block);
                }
            }
            StmtKind::Assignment(lhs, rhs) => {
                self.diagnose_unsupported_handlers_in_expr(unit, lhs);
                self.diagnose_unsupported_handlers_in_expr(unit, rhs);
            }
            StmtKind::Loop(condition, body) => {
                if let Some(condition) = condition {
                    self.diagnose_unsupported_handlers_in_expr(unit, condition);
                }
                self.diagnose_unsupported_handlers_in_block(unit, body);
            }
            StmtKind::Return(None) | StmtKind::Break | StmtKind::Continue(None) => {}
        }
    }

    pub(super) fn diagnose_unsupported_handlers_in_expr(&mut self, unit: usize, expr: &Expr) {
        match &expr.kind {
            ExprKind::Block(block) => self.diagnose_unsupported_handlers_in_block(unit, block),
            ExprKind::Match(scrutinee, arms) => {
                self.diagnose_unsupported_handlers_in_expr(unit, scrutinee);
                for arm in arms {
                    self.diagnose_unsupported_handlers_in_block(unit, &arm.body);
                }
            }
            ExprKind::Tuple(items)
            | ExprKind::LiteralArray(items)
            | ExprKind::Con { args: items, .. } => {
                for item in items {
                    self.diagnose_unsupported_handlers_in_expr(unit, item);
                }
            }
            ExprKind::Call {
                callee,
                args,
                trailing_block,
                ..
            } => {
                self.diagnose_unsupported_handlers_in_expr(unit, callee);
                for arg in args {
                    self.diagnose_unsupported_handlers_in_expr(unit, &arg.value);
                }
                if let Some(block) = trailing_block {
                    self.diagnose_unsupported_handlers_in_block(unit, block);
                }
            }
            ExprKind::CallEffect { args, .. } => {
                for arg in args {
                    self.diagnose_unsupported_handlers_in_expr(unit, &arg.value);
                }
            }
            ExprKind::Member(Some(receiver), ..) | ExprKind::Proj(receiver, ..) => {
                self.diagnose_unsupported_handlers_in_expr(unit, receiver);
            }
            ExprKind::Func(func) => self.diagnose_unsupported_handlers_in_block(unit, &func.body),
            ExprKind::RecordLiteral { fields, spread } => {
                if let Some(spread) = spread {
                    self.diagnose_unsupported_handlers_in_expr(unit, spread);
                }
                for field in fields {
                    self.diagnose_unsupported_handlers_in_expr(unit, &field.value);
                }
            }
            _ => {}
        }
    }

    // ----- Worklist (lazy monomorphization) -------------------------------

    /// Demand the specialization of `symbol` at θ; returns its λ_G label.
    pub(super) fn demand(&mut self, symbol: Symbol, theta: Theta) -> Label {
        let key = (symbol, theta_key(&theta));
        if let Some(&label) = self.done.get(&key) {
            return label;
        }
        let sig = self.signature_of(symbol, &theta);
        let Some(CheckTy::Func(params, mut ret, _)) = sig else {
            self.diagnostics.push(format!(
                "lowering: no callable signature for {symbol} (not yet supported)"
            ));
            let void = self.p.ty_void();
            let bot = self.p.ty_bot();
            let dead = self.p.func("unsupported", void, bot);
            self.done.insert(key, dead);
            return dead;
        };

        // An init returns self whatever its body's final value is
        // (construction semantics — the checker types `Person(...)` as the
        // struct; the inferred body value may be Void).
        if self.is_init(symbol)
            && let Some(self_ty) = params.first()
        {
            *ret = self_ty.clone();
        }
        let param_tys: Vec<TyId> = params.iter().map(|t| self.map_ty(t)).collect();
        let ret_ty = self.map_ty(&ret);
        // Inout self: the ret continuation of a mutating method carries
        // [result, Self]; the caller writes Self back.
        let ret_payload = if self.mutating.contains(&symbol) {
            match param_tys.first() {
                Some(&self_ty) => self.p.ty_tuple(&[ret_ty, self_ty]),
                None => ret_ty,
            }
        } else {
            ret_ty
        };
        let bot = self.p.ty_bot();
        let mut dom_items = param_tys;
        // One capability parameter per user-effect instantiation in the
        // latent row (capability-passing style — Schuster, Brachthäuser &
        // Ostermann, ICFP 2020; the sorted row is a monomorphized evidence
        // vector — Xie & Leijen, ICFP 2021), then the return continuation.
        for (effect, args) in self.cap_entries_of(symbol, &theta) {
            if let Some(cap_ty) = self.cap_ty(effect, &args) {
                dom_items.push(cap_ty);
            }
        }
        dom_items.push(self.p.ty_fn(ret_payload, bot));
        let dom = self.p.ty_tuple(&dom_items);

        let name = self.spec_name(symbol, &theta);
        let label = self.p.func(&name, dom, bot);
        self.done.insert(key, label);
        self.queue.push((symbol, theta, label));
        label
    }

    pub(super) fn drain_queue(&mut self) {
        while let Some((symbol, theta, label)) = self.queue.pop() {
            self.lower_function(symbol, theta, label);
        }
    }

    /// The callable signature of a symbol: its scheme's type (top-level
    /// funcs, methods, witnesses) or its protocol requirement signature
    /// (default bodies), θ-substituted.
    pub(super) fn signature_of(&mut self, symbol: Symbol, theta: &Theta) -> Option<CheckTy> {
        let raw = self
            .units
            .iter()
            .find_map(|u| u.types.schemes.get(&symbol).map(|s| s.ty.clone()))
            .or_else(|| self.requirement_sigs.get(&symbol).cloned())?;
        Some(raw.substitute(theta, &Default::default(), &Default::default()))
    }

    /// A specialization's display name: the source name plus the concrete
    /// types it was specialized at (`id<Int>`), in a stable order.
    pub(super) fn spec_name(&mut self, symbol: Symbol, theta: &Theta) -> String {
        let base = self
            .units
            .iter()
            .find_map(|u| u.resolved.symbol_names.get(&symbol).cloned())
            .unwrap_or_else(|| format!("{symbol}"));
        if theta.is_empty() {
            return base;
        }
        let mut args: Vec<(String, String)> = theta
            .iter()
            .map(|(param, ty)| (format!("{param:?}"), ty.render_mono()))
            .collect();
        args.sort();
        let rendered: Vec<String> = args.into_iter().map(|(_, ty)| ty).collect();
        format!("{base}<{}>", rendered.join(", "))
    }
}
