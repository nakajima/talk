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

    // ----- Abort-capable functions (lexical effect handlers) --------------

    /// The transitive closure of the checker's capability tables: a
    /// binder is abort-capable if its body performs into a lexical
    /// handler (`performs_into`) or references an abort-capable binder
    /// (`binder_refs`) — its callers must thread the abort linkage (see
    /// `Ctx::raw_ret_k`). The reference edges are a conservative
    /// superset of calls; a spurious mark only costs a function the
    /// abort-capable calling convention, never correctness.
    pub(super) fn collect_abortable(&mut self) {
        // A handler defined inside the binder itself contains its aborts:
        // they never escape the function, so neither the binder nor its
        // callers need the abort-capable convention for them.
        let mut contained: FxHashMap<Symbol, FxHashSet<Symbol>> = FxHashMap::default();
        for unit in &self.units {
            for (&binder, handlers) in &unit.types.handlers_defined {
                contained.entry(binder).or_default().extend(handlers);
            }
        }
        let escapes =
            |binder: Symbol, handler: Symbol, contained: &FxHashMap<Symbol, FxHashSet<Symbol>>| {
                !contained
                    .get(&binder)
                    .is_some_and(|defined| defined.contains(&handler))
            };

        let mut reached: FxHashMap<Symbol, Vec<Symbol>> = FxHashMap::default();
        for unit in &self.units {
            for (&binder, handlers) in &unit.types.performs_into {
                let owned = reached.entry(binder).or_default();
                for &handler in handlers {
                    if escapes(binder, handler, &contained) && !owned.contains(&handler) {
                        owned.push(handler);
                    }
                }
            }
        }
        loop {
            let mut changed = false;
            for unit in &self.units {
                for (&binder, refs) in &unit.types.binder_refs {
                    for target in refs {
                        let Some(handlers) = reached.get(target).cloned() else {
                            continue;
                        };
                        let owned = reached.entry(binder).or_default();
                        for handler in handlers {
                            if escapes(binder, handler, &contained) && !owned.contains(&handler) {
                                owned.push(handler);
                                changed = true;
                            }
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        reached.retain(|_, handlers| !handlers.is_empty());
        // Deterministic handler order (abort_scope_ty takes the first).
        for handlers in reached.values_mut() {
            handlers.sort();
        }
        self.abortable = reached;
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
            StmtKind::Handling {
                effect_name, body, ..
            } => {
                if let Some(symbol) = effect_name.symbol().ok()
                    && self.units[unit]
                        .types
                        .catalog
                        .effects
                        .get(&symbol)
                        .is_some_and(|sig| !sig.generics.is_empty())
                {
                    self.diagnostics
                        .push("lowering: handlers for generic effects (not yet supported)".into());
                }
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

    /// Does this symbol's specialization take the abort-capable shape
    /// (normal-return continuation parameter + return slot reserved for
    /// aborts)? Inits and inout methods are excluded for now — their ret
    /// wrappers and the abort linkage have not been reconciled.
    pub(super) fn abort_shape(&self, symbol: Symbol) -> bool {
        self.abortable.contains_key(&symbol)
            && !self.is_init(symbol)
            && !self.mutating.contains(&symbol)
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
        if self.abort_shape(symbol) {
            // The abort-capable shape: …params, normal-return continuation
            // (taking [result, return slot]), then the return slot itself,
            // reserved for abort propagation (capability-passing CPS —
            // Schuster et al., PLDI 2022).
            let scope_ty = self.abort_scope_ty(symbol, ret_payload);
            let slot_ty = self.p.ty_fn(scope_ty, bot);
            let pair_ty = self.p.ty_tuple(&[ret_payload, slot_ty]);
            dom_items.push(self.p.ty_fn(pair_ty, bot));
            dom_items.push(slot_ty);
        } else {
            if self.abortable.contains_key(&symbol) {
                self.diagnostics.push(format!(
                    "lowering: {symbol} is an init or inout method that can abort (not yet supported)"
                ));
            }
            dom_items.push(self.p.ty_fn(ret_payload, bot));
        }
        let dom = self.p.ty_tuple(&dom_items);

        let name = self.spec_name(symbol, &theta);
        let label = self.p.func(&name, dom, bot);
        self.done.insert(key, label);
        self.queue.push((symbol, theta, label));
        label
    }

    /// The value type an abort-capable function's Ret chain carries: the
    /// result type of the scope owning the handler its performs route to.
    /// Falls back to the function's own result type (with a diagnostic)
    /// when the handler is unknown — the program is already rejected.
    pub(super) fn abort_scope_ty(&mut self, symbol: Symbol, fallback: TyId) -> TyId {
        let handlers = self.abortable.get(&symbol).cloned().unwrap_or_default();
        if handlers.len() > 1 {
            self.diagnostics.push(format!(
                "lowering: {symbol} performs into more than one handler (not yet supported)"
            ));
        }
        let Some(cap) = handlers.first().and_then(|h| self.handler_caps.get(h)) else {
            self.diagnostics.push(format!(
                "lowering: {symbol} can abort but is demanded before its handler is installed (not yet supported)"
            ));
            return fallback;
        };
        cap.scope_result_ty
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
