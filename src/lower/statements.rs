use super::*;
use crate::lower::mir;

/// Where an assignment ultimately writes: a root cell (value semantics,
/// functional rebuild + write-back) or a `'heap` object handle (in-place).
pub(super) enum AssignBase {
    Cell(ExprId),
    Object(ExprId),
}

/// The leaf operation a structural teardown walk applies to owned
/// buffers: release them (drop) or rc-bump them (the CoW clone's retain).
#[derive(Clone, Copy)]
enum PayloadAction {
    Drop,
    Retain,
}

impl<'a> Lowering<'a> {
    // ----- Blocks and statements -------------------------------------------

    /// Lower a block whose VALUE flows to continuation `k` (a Fn(R, ⊥)
    /// expression). A block's value is its final expression; divergent
    /// statements (return) ignore `k`. `params` are the block's own
    /// parameters when it is a function/closure body (owned by-value
    /// parameters drop at its scope exit); empty otherwise.
    pub(super) fn lower_block(
        &mut self,
        block: &Block,
        params: &[hir::Parameter],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let body = self.annotated_body(block, ctx, |types, owner, block| {
            mir::build_function(types, owner, params, block)
        });
        self.lower_mir_body(&body, ctx, k)
    }

    /// Lower a match arm's body: like `lower_block`, but the arm pattern's
    /// binders are the body's root-frame locals.
    pub(super) fn lower_arm_block(
        &mut self,
        pattern: &hir::Pattern,
        block: &Block,
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let body = self.annotated_body(block, ctx, |types, _, block| {
            mir::build_arm_body(types, pattern, block)
        });
        self.lower_mir_body(&body, ctx, k)
    }

    /// One MIR body per HIR block — every θ-specialization re-lowers the
    /// shared body instead of rebuilding it. Function-like bodies come from
    /// the module's store (built pre-flow, annotated by the flow checker);
    /// the rest (nested value blocks, match arms) build on miss and are
    /// annotated from the flow results the checker left on this subtree.
    pub(super) fn annotated_body(
        &mut self,
        block: &Block,
        ctx: &Ctx,
        build: impl FnOnce(&TypeOutput, Option<Symbol>, &Block) -> mir::Body,
    ) -> std::sync::Arc<mir::Body> {
        let key = (ctx.unit, block.id);
        if let Some(body) = self.mir_bodies.get(&key) {
            return std::sync::Arc::clone(body);
        }
        let unit = &self.units[ctx.unit];
        let body = match unit.bodies.get(block.id) {
            Some(body) => body,
            None => {
                let mut body = build(unit.types, ctx.owner, block);
                let collected = crate::flow::mir_annotate::CollectedSchedules::of_block(block);
                crate::flow::mir_annotate::annotate_body_from_hir(&mut body, &collected);
                std::sync::Arc::new(body)
            }
        };
        self.mir_bodies.insert(key, std::sync::Arc::clone(&body));
        body
    }

    /// Resolve an assignment lhs to its root cell and the field path down
    /// to the assigned location: `a.b.c = …` walks Member receivers to
    /// the cell-bound variable, collecting per level the field index and
    /// the record's λ_G type (structs by declared order; anonymous
    /// records by the row's canonical label-sorted order, matching
    /// map_ty's layout).
    pub(super) fn assignment_target(
        &mut self,
        lhs: &Expr,
        ctx: &Ctx,
    ) -> Option<(AssignBase, Vec<(u32, TyId)>)> {
        match &lhs.kind {
            ExprKind::Variable(name) => {
                let symbol = name.symbol().ok();
                if let Some(Binding::Cell(cell)) = symbol.and_then(|s| ctx.env.get(&s).copied()) {
                    return Some((AssignBase::Cell(cell), vec![]));
                }
                // A mutable top-level binding assigned from inside a
                // function: its registered cell (captured like any value).
                if let Some(cell) = symbol.and_then(|s| self.top_level_cells.get(&s).copied()) {
                    return Some((AssignBase::Cell(cell), vec![]));
                }
                self.diagnostics
                    .push("lowering: assignment to a non-cell binding".into());
                None
            }
            ExprKind::Member(Some(receiver), label) | ExprKind::Proj(receiver, label, _) => {
                let head = Self::borrow_erased_ty(self.checker_ty(receiver, ctx));
                // Nearest-to-leaf `'heap` receiver: the write is an in-place
                // ObjectSet on the handle — nothing above it is rebuilt or
                // written back (mutation is visible through the reference).
                let (base, mut path) = if matches!(&head, CheckTy::Nominal(symbol, _)
                    if self.symbol_is_heap(*symbol))
                {
                    let Some(handle) = self.try_pure(receiver, ctx) else {
                        self.diagnostics.push(
                            "lowering: assignment through an impure heap receiver (not yet supported)"
                                .into(),
                        );
                        return None;
                    };
                    (AssignBase::Object(handle), vec![])
                } else {
                    self.assignment_target(receiver, ctx)?
                };
                let index = match &head {
                    CheckTy::Record(row) if row.tail.is_none() => row
                        .fields
                        .iter()
                        .position(|(name, _)| name.to_string() == label.to_string())
                        .map(|i| i as u32),
                    _ => {
                        let resolution = lhs.member_resolution.clone();
                        match resolution {
                            Some(crate::types::output::MemberResolution::Direct(property)) => {
                                self.field_index(&head, property)
                            }
                            _ => None,
                        }
                    }
                };
                let Some(index) = index else {
                    self.diagnostics.push(format!(
                        "lowering: '{label}' is not a stored field of {head:?}"
                    ));
                    return None;
                };
                let record_ty = self.map_ty(&head);
                path.push((index, record_ty));
                Some((base, path))
            }
            _ => {
                self.diagnostics
                    .push("lowering: assignment target not yet supported".into());
                None
            }
        }
    }

    /// The write side of `object_assignment`: functional rebuild below the
    /// handle, one in-place ObjectSet at it.
    pub(super) fn object_assignment_write(
        &mut self,
        base: ExprId,
        path: &[(u32, TyId)],
        value: ExprId,
    ) -> ExprId {
        let void_ty = self.p.ty_void();
        let (first_index, _) = path[0];
        if path.len() == 1 {
            return self
                .p
                .primop(Op::ObjectSet(first_index), &[base, value], void_ty);
        }
        // Read down below the object, rebuild functionally back up to the
        // object's field, then one ObjectSet.
        let mut levels = Vec::with_capacity(path.len());
        levels.push(base);
        for step in 1..path.len() {
            let (index, _) = path[step - 1];
            let (_, level_ty) = path[step];
            let prev = levels[step - 1];
            levels.push(self.field_get(prev, index, level_ty));
        }
        let mut stored = value;
        for step in (1..path.len()).rev() {
            let (index, _) = path[step];
            let level_ty = path[step].1;
            stored = self.field_set(levels[step], index, stored, level_ty);
        }
        self.p
            .primop(Op::ObjectSet(first_index), &[base, stored], void_ty)
    }

    pub(super) fn object_assignment_old_value(
        &mut self,
        base: ExprId,
        path: &[(u32, TyId)],
        leaf_ty: TyId,
    ) -> ExprId {
        let mut parent = base;
        for step in 1..path.len() {
            let (index, _) = path[step - 1];
            let (_, level_ty) = path[step];
            parent = self.field_get(parent, index, level_ty);
        }
        let (index, _) = path[path.len() - 1];
        self.field_get(parent, index, leaf_ty)
    }

    pub(super) fn rebuilt_assignment_value(
        &mut self,
        cell: ExprId,
        path: &[(u32, TyId)],
        value: ExprId,
    ) -> ExprId {
        if path.is_empty() {
            return value;
        }
        // Read down the path, then rebuild back up from the leaf:
        // levels[k] is the record indexed at step k.
        let TyKind::Cell(root_ty) = *self.p.ty_kind(self.p.expr_ty(cell)) else {
            unreachable!("assignment target is not a cell");
        };
        let mut levels = Vec::with_capacity(path.len());
        levels.push(self.p.primop(Op::CellGet, &[cell], root_ty));
        for step in 1..path.len() {
            let (index, _) = path[step - 1];
            let (_, level_ty) = path[step];
            let prev = levels[step - 1];
            levels.push(self.field_get(prev, index, level_ty));
        }
        let mut stored = value;
        for step in (0..path.len()).rev() {
            let (index, _) = path[step];
            let level_ty = if step == 0 { root_ty } else { path[step].1 };
            stored = self.field_set(levels[step], index, stored, level_ty);
        }
        stored
    }

    pub(super) fn assignment_old_value(
        &mut self,
        cell: ExprId,
        path: &[(u32, TyId)],
        leaf_ty: TyId,
    ) -> ExprId {
        let TyKind::Cell(root_ty) = *self.p.ty_kind(self.p.expr_ty(cell)) else {
            unreachable!("assignment target is not a cell");
        };
        if path.is_empty() {
            return self.p.primop(Op::CellGet, &[cell], root_ty);
        }
        let mut parent = self.p.primop(Op::CellGet, &[cell], root_ty);
        for step in 1..path.len() {
            let (index, _) = path[step - 1];
            let (_, level_ty) = path[step];
            parent = self.field_get(parent, index, level_ty);
        }
        let (index, _) = path[path.len() - 1];
        self.field_get(parent, index, leaf_ty)
    }

    /// One field read for the assignment path: structs (boxed records)
    /// use GetField; anonymous records are tuples, so extract.
    pub(super) fn field_get(&mut self, record: ExprId, index: u32, field_ty: TyId) -> ExprId {
        match self.p.ty_kind(self.p.expr_ty(record)) {
            TyKind::Tuple(_) => self.p.extract(record, index),
            TyKind::Object(_) => self.p.primop(Op::ObjectGet(index), &[record], field_ty),
            _ => self.p.primop(Op::GetField(index), &[record], field_ty),
        }
    }

    /// One functional field replacement for the assignment path: structs
    /// use SetField (CoW); anonymous records rebuild the tuple with the
    /// slot replaced.
    pub(super) fn field_set(
        &mut self,
        record: ExprId,
        index: u32,
        value: ExprId,
        record_ty: TyId,
    ) -> ExprId {
        let items = match self.p.ty_kind(record_ty) {
            TyKind::Tuple(items) => Some(items.clone()),
            _ => None,
        };
        match items {
            Some(items) => {
                let rebuilt: Vec<ExprId> = (0..items.len() as u32)
                    .map(|slot| {
                        if slot == index {
                            value
                        } else {
                            self.p.extract(record, slot)
                        }
                    })
                    .collect();
                self.p.tuple(&rebuilt)
            }
            None => self
                .p
                .primop(Op::SetField(index), &[record, value], record_ty),
        }
    }

    pub(super) fn symbol_has_move_fact(&self, body: &mir::Body, symbol: Symbol) -> bool {
        body.blocks
            .iter()
            .flat_map(|block| &block.statements)
            .any(|statement| {
                statement
                    .ownership
                    .moves
                    .iter()
                    .any(|source| source.root == symbol)
            })
    }

    pub(super) fn symbol_check_ty(&self, symbol: Symbol, theta: &Theta) -> Option<CheckTy> {
        self.units.iter().enumerate().find_map(|(unit, unit_data)| {
            let raw = unit_data.types.schemes.get(&symbol)?.ty.clone();
            let substituted = raw.substitute(theta, &Default::default(), &Default::default());
            Some(self.normalize_check_ty(substituted, unit))
        })
    }

    pub(super) fn lower_drop_bindings_then(
        &mut self,
        ctx: &Ctx,
        drops: &[DropBinding],
        next: ExprId,
    ) -> ExprId {
        let mut body = next;
        for drop in drops.iter().rev() {
            let Some(value) = self.binding_value(ctx, drop.symbol) else {
                continue;
            };
            body = if drop.dynamic_flags.is_empty() {
                self.lower_drop_value_then(ctx, value, &drop.ty, body)
            } else {
                self.lower_dynamic_drop_binding_then(ctx, drop, value, body)
            };
        }
        body
    }

    pub(super) fn binding_value(&mut self, ctx: &Ctx, symbol: Symbol) -> Option<ExprId> {
        if let Some(binding) = ctx.env.get(&symbol).copied() {
            return match binding {
                Binding::Value(value) => Some(value),
                Binding::Cell(cell) => {
                    let TyKind::Cell(inner) = *self.p.ty_kind(self.p.expr_ty(cell)) else {
                        return None;
                    };
                    Some(self.p.primop(Op::CellGet, &[cell], inner))
                }
            };
        }
        if let Some(&cell) = self.top_level_cells.get(&symbol) {
            let TyKind::Cell(inner) = *self.p.ty_kind(self.p.expr_ty(cell)) else {
                return None;
            };
            return Some(self.p.primop(Op::CellGet, &[cell], inner));
        }
        None
    }

    pub(super) fn lower_drop_value_then(
        &mut self,
        ctx: &Ctx,
        value: ExprId,
        ty: &CheckTy,
        next: ExprId,
    ) -> ExprId {
        // Ledger: values carrying `'heap` handles release their regions
        // (one runtime scan covers any shape); owned parts still drop
        // structurally below, with object interiors left to the finalizer
        // walk.
        let mut next = next;
        if self.contains_object_type(ty) {
            let void_ty = self.p.ty_void();
            let release = self.p.primop(Op::RegionRelease, &[value], void_ty);
            next = self.sequence_void_effect(release, next);
            if matches!(Self::borrow_erased_ty(ty.clone()), CheckTy::Nominal(symbol, _)
                if self.symbol_is_heap(symbol))
            {
                return next;
            }
        }
        if !self.needs_drop_type(ty) {
            return next;
        }
        match Self::borrow_erased_ty(ty.clone()) {
            CheckTy::Nominal(symbol, args) => {
                if self.symbol_is_borrowed(symbol) {
                    return next;
                }
                // An enum's owned payloads drop under a tag dispatch: one
                // switch arm per variant, each dropping that variant's
                // owned payloads, joining back to `next`.
                if self.is_enum(symbol) {
                    return self.lower_enum_payloads_then(
                        ctx,
                        value,
                        symbol,
                        &args,
                        next,
                        PayloadAction::Drop,
                    );
                }
                // A `Deinit` conformance is the user's destructor hook
                // (Rust's Drop::drop model): the body runs first, then the
                // GLUE tears the fields down structurally — the body never
                // owns field teardown. The self-recursion guard is θ-aware:
                // inside `deinit<Array<String>>`, dropping an ELEMENT that
                // is itself an array (a different instantiation) must
                // still dispatch — only the body's own value skips. The
                // witness ranges over the CONFORMANCE row's rigid params,
                // so θ binds the row's self_args against this application.
                let value_theta = self.deinit_theta(symbol, &args);
                if let Some(witness) = self.deinit_witness(symbol)
                    && (ctx.owner != Some(witness) || value_theta != ctx.theta)
                {
                    let theta = value_theta;
                    let label = self.demand(witness, theta);
                    let fn_ref = self.p.func_ref(label);
                    let void_ty = self.p.ty_void();
                    let bot = self.p.ty_bot();
                    let teardown =
                        self.lower_structural_teardown_then(ctx, value, symbol, &args, next);
                    let cont = self.p.func("after_deinit", void_ty, bot);
                    self.p.set_body(cont, teardown);
                    let cont_ref = self.p.func_ref(cont);
                    let args_tuple = self.p.tuple(&[value, cont_ref]);
                    return self.p.app(fn_ref, args_tuple);
                }
                self.lower_structural_teardown_then(ctx, value, symbol, &args, next)
            }
            CheckTy::Tuple(items) => {
                let mut body = next;
                for (index, item_ty) in items.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(&item_ty) {
                        continue;
                    }
                    let field_value = self.p.extract(value, index as u32);
                    body = self.lower_drop_value_then(ctx, field_value, &item_ty, body);
                }
                body
            }
            CheckTy::Record(row) if row.tail.is_none() => {
                let mut body = next;
                for (index, (_, field_ty)) in row.fields.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(&field_ty) {
                        continue;
                    }
                    let field_value = self.p.extract(value, index as u32);
                    body = self.lower_drop_value_then(ctx, field_value, &field_ty, body);
                }
                body
            }
            CheckTy::Any { protocol, .. } => {
                // Every existential carries a drop witness in its last
                // table slot: `λ(payload, k)` (deinit dispatch included).
                // The slot index comes from the ENTRY unit's merged
                // catalog — the drop may lower inside core (Array's
                // deinit) for a protocol core has never heard of.
                let index = self.units[self.entry]
                    .types
                    .catalog
                    .requirements_for_conformance(protocol)
                    .len() as u32;
                let void_ty = self.p.ty_void();
                let bot = self.p.ty_bot();
                let erased = self.p.ty(TyKind::Erased);
                let k_ty = self.p.ty_fn(void_ty, bot);
                let dom = self.p.ty_tuple(&[erased, k_ty]);
                let witness_ty = self.p.ty_fn(dom, bot);
                let witness = self
                    .p
                    .primop(Op::ExistentialWitness(index), &[value], witness_ty);
                let payload = self.p.primop(Op::ExistentialPayload, &[value], erased);
                let cont = self.p.func("after_existential_drop", void_ty, bot);
                self.p.set_body(cont, next);
                let cont_ref = self.p.func_ref(cont);
                let args_tuple = self.p.tuple(&[payload, cont_ref]);
                self.p.app(witness, args_tuple)
            }
            _ => next,
        }
    }

    /// Retain a value's refcounted buffers (the CoW clone: an rc bump at
    /// every raw-pointer allocation the value owns), then continue. Mirrors
    /// [`Self::lower_drop_value_then`]'s teardown structure — retain exactly
    /// where a drop would free — minus `Deinit` dispatch: auto-clone applies
    /// only to CheapClone types, which have no destructor to run.
    pub(super) fn lower_retain_value_then(
        &mut self,
        ctx: &Ctx,
        value: ExprId,
        ty: &CheckTy,
        next: ExprId,
    ) -> ExprId {
        if !self.needs_drop_type(ty) {
            return next;
        }
        match Self::borrow_erased_ty(ty.clone()) {
            CheckTy::Nominal(symbol, args) => {
                if self.symbol_is_borrowed(symbol) {
                    return next;
                }
                // An enum retains under the same tag dispatch its drop
                // uses: each variant's owned payloads rc-bump exactly
                // where they would free.
                if self.is_enum(symbol) {
                    return self.lower_enum_payloads_then(
                        ctx,
                        value,
                        symbol,
                        &args,
                        next,
                        PayloadAction::Retain,
                    );
                }
                if let Some(index) = self.rawptr_field_index(symbol) {
                    let ptr_ty = self.p.ty_ptr();
                    let ptr = self.p.primop(Op::GetField(index), &[value], ptr_ty);
                    let void_ty = self.p.ty_void();
                    let retain = self.p.primop(Op::Retain, &[ptr], void_ty);
                    return self.sequence_void_effect(retain, next);
                }
                let fields = self.field_types_for(symbol, &args);
                let mut body = next;
                for (index, (_, field_ty)) in fields.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(&field_ty) {
                        continue;
                    }
                    let field_lambda_ty = self.map_ty(&field_ty);
                    let field_value =
                        self.p
                            .primop(Op::GetField(index as u32), &[value], field_lambda_ty);
                    body = self.lower_retain_value_then(ctx, field_value, &field_ty, body);
                }
                body
            }
            CheckTy::Tuple(items) => {
                let mut body = next;
                for (index, item_ty) in items.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(&item_ty) {
                        continue;
                    }
                    let field_value = self.p.extract(value, index as u32);
                    body = self.lower_retain_value_then(ctx, field_value, &item_ty, body);
                }
                body
            }
            CheckTy::Record(row) if row.tail.is_none() => {
                let mut body = next;
                for (index, (_, field_ty)) in row.fields.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(&field_ty) {
                        continue;
                    }
                    let field_value = self.p.extract(value, index as u32);
                    body = self.lower_retain_value_then(ctx, field_value, &field_ty, body);
                }
                body
            }
            _ => next,
        }
    }

    /// Walk an enum value's owned payloads: `GetTag` + `Switch`, one arm
    /// per variant in declaration order (the tag numbering), applying
    /// `action` to each variant's owned payloads in reverse, all joining
    /// back to `next`. Shared by the drop and retain walkers so a variant
    /// retains exactly where it would free.
    fn lower_enum_payloads_then(
        &mut self,
        ctx: &Ctx,
        value: ExprId,
        symbol: Symbol,
        args: &[CheckTy],
        next: ExprId,
        action: PayloadAction,
    ) -> ExprId {
        let theta = self.nominal_theta(symbol, args);
        let Some(info) = self
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.enums.get(&symbol).cloned())
        else {
            return next;
        };
        let variant_payloads: Vec<Vec<CheckTy>> = info
            .variants
            .values()
            .map(|variant| match &variant.constructor_scheme.ty {
                CheckTy::Func(payloads, ..) => payloads
                    .iter()
                    .map(|ty| ty.substitute(&theta, &Default::default(), &Default::default()))
                    .collect(),
                _ => vec![],
            })
            .collect();
        if !variant_payloads
            .iter()
            .flatten()
            .any(|payload| self.needs_drop_type(payload))
        {
            return next;
        }
        let (join_name, arm_name) = match action {
            PayloadAction::Drop => ("after_enum_drop", "drop_variant"),
            PayloadAction::Retain => ("after_enum_retain", "retain_variant"),
        };
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let join = self.p.func(join_name, void_ty, bot);
        self.p.set_body(join, next);
        let join_ref = self.p.func_ref(join);
        let mut arm_refs = Vec::with_capacity(variant_payloads.len());
        for payloads in &variant_payloads {
            let unit_value = self.p.void();
            let mut body = self.p.app(join_ref, unit_value);
            for (index, payload_ty) in payloads.iter().enumerate().rev() {
                if !self.needs_drop_type(payload_ty) {
                    continue;
                }
                let payload_lambda_ty = self.map_ty(payload_ty);
                let payload =
                    self.p
                        .primop(Op::GetPayload(index as u32), &[value], payload_lambda_ty);
                body = match action {
                    PayloadAction::Drop => {
                        self.lower_drop_value_then(ctx, payload, payload_ty, body)
                    }
                    PayloadAction::Retain => {
                        self.lower_retain_value_then(ctx, payload, payload_ty, body)
                    }
                };
            }
            let arm = self.p.func(arm_name, void_ty, bot);
            self.p.set_body(arm, body);
            arm_refs.push(self.p.func_ref(arm));
        }
        let i64_ty = self.p.ty_i64();
        let tag = self.p.primop(Op::GetTag, &[value], i64_ty);
        self.p.switch(tag, &arm_refs, join_ref, bot)
    }

    /// The `deinit` witness for a nominal's `Deinit` conformance, if any.
    pub(super) fn deinit_witness(&self, symbol: Symbol) -> Option<Symbol> {
        self.units.iter().find_map(|unit| {
            unit.types
                .catalog
                .conformances
                .get(&(symbol, Symbol::Deinit))
                .and_then(|conformance| conformance.witnesses.get("deinit"))
                .copied()
        })
    }

    /// Structural teardown of a nominal's owned parts: the raw-pointer
    /// field frees, other droppable fields drop recursively. Runs after a
    /// Deinit hook returns (the glue owns teardown, never the hook body)
    /// and directly for nominals without one.
    fn lower_structural_teardown_then(
        &mut self,
        ctx: &Ctx,
        value: ExprId,
        symbol: Symbol,
        args: &[CheckTy],
        next: ExprId,
    ) -> ExprId {
        if let Some(index) = self.rawptr_field_index(symbol) {
            let ptr_ty = self.p.ty_ptr();
            let ptr = self.p.primop(Op::GetField(index), &[value], ptr_ty);
            let void_ty = self.p.ty_void();
            let free = self.p.primop(Op::Free, &[ptr], void_ty);
            return self.sequence_void_effect(free, next);
        }
        let fields = self.field_types_for(symbol, args);
        let mut body = next;
        for (index, (_, field_ty)) in fields.into_iter().enumerate().rev() {
            if !self.needs_drop_type(&field_ty) {
                continue;
            }
            let field_lambda_ty = self.map_ty(&field_ty);
            let field_value = self
                .p
                .primop(Op::GetField(index as u32), &[value], field_lambda_ty);
            body = self.lower_drop_value_then(ctx, field_value, &field_ty, body);
        }
        body
    }

    /// θ for a Deinit witness at this application: the conformance row's
    /// rigid params bound against the head args.
    pub(super) fn deinit_theta(&self, symbol: Symbol, args: &[CheckTy]) -> Theta {
        let mut theta = Theta::default();
        if let Some(conformance) = self.units.iter().find_map(|unit| {
            unit.types
                .catalog
                .conformances
                .get(&(symbol, Symbol::Deinit))
        }) {
            for (pattern, actual) in conformance.self_args.iter().zip(args) {
                crate::types::solve::bind_param_pattern(pattern, actual, &mut theta);
            }
        }
        theta
    }

    /// θ binding a nominal's declared params to this application's args.
    pub(super) fn nominal_theta(&self, symbol: Symbol, args: &[CheckTy]) -> Theta {
        let params = self
            .units
            .iter()
            .find_map(|unit| {
                unit.types
                    .catalog
                    .structs
                    .get(&symbol)
                    .map(|info| info.params.clone())
                    .or_else(|| {
                        unit.types
                            .catalog
                            .enums
                            .get(&symbol)
                            .map(|info| info.params.clone())
                    })
            })
            .unwrap_or_default();
        params.into_iter().zip(args.iter().cloned()).collect()
    }

    pub(super) fn sequence_void_effect(&mut self, effect: ExprId, next: ExprId) -> ExprId {
        let bot = self.p.ty_bot();
        let void_ty = self.p.ty_void();
        let cont = self.p.func("after_drop", void_ty, bot);
        self.p.set_body(cont, next);
        let cont_ref = self.p.func_ref(cont);
        self.p.app(cont_ref, effect)
    }

    pub(super) fn with_drop_flags(
        &mut self,
        drops: &[DropBinding],
        ctx: &mut Ctx,
        finish: impl FnOnce(&mut Self, &mut Ctx) -> ExprId,
    ) -> ExprId {
        let mut keys = Vec::new();
        for drop in drops {
            for key in &drop.dynamic_flags {
                if !ctx.drop_flags.contains_key(key) && !keys.iter().any(|seen| seen == key) {
                    keys.push(key.clone());
                }
            }
        }
        self.with_drop_flag_keys(&keys, ctx, finish)
    }

    fn with_drop_flag_keys(
        &mut self,
        keys: &[Place],
        ctx: &mut Ctx,
        finish: impl FnOnce(&mut Self, &mut Ctx) -> ExprId,
    ) -> ExprId {
        let Some((key, rest)) = keys.split_first() else {
            return finish(self, ctx);
        };
        let bool_ty = self.p.ty_bool();
        let cell_ty = self.p.ty_cell(bool_ty);
        let bot = self.p.ty_bot();
        let bind = self.p.func("drop_flag", cell_ty, bot);
        let cell = self.p.var(bind);
        ctx.drop_flags.insert(key.clone(), cell);
        let body = self.with_drop_flag_keys(rest, ctx, finish);
        self.p.set_body(bind, body);
        let bind_ref = self.p.func_ref(bind);
        let initial = self.p.bool(true);
        let flag_cell = self.p.primop(Op::CellNew, &[initial], cell_ty);
        self.p.app(bind_ref, flag_cell)
    }

    pub(super) fn set_drop_flags_under_then(
        &mut self,
        ctx: &Ctx,
        key_path: &Place,
        live: bool,
        next: ExprId,
    ) -> ExprId {
        let mut keys: Vec<Place> = ctx
            .drop_flags
            .keys()
            .filter(|key| key_path.contains(key))
            .cloned()
            .collect();
        keys.sort_by_key(|key| format!("{key:?}"));
        let mut body = next;
        for key in keys.iter().rev() {
            body = self.set_drop_flag_then(ctx, key, live, body);
        }
        body
    }

    fn set_drop_flag_then(
        &mut self,
        ctx: &Ctx,
        key_path: &Place,
        live: bool,
        next: ExprId,
    ) -> ExprId {
        let Some(&flag) = ctx.drop_flags.get(key_path) else {
            return next;
        };
        let value = self.p.bool(live);
        let void_ty = self.p.ty_void();
        let set = self.p.primop(Op::CellSet, &[flag, value], void_ty);
        self.sequence_void_effect(set, next)
    }

    pub(super) fn lower_dynamic_assignment_drop_then(
        &mut self,
        ctx: &Ctx,
        key_path: &Place,
        value: ExprId,
        ty: &CheckTy,
        next: ExprId,
    ) -> ExprId {
        self.lower_drop_key_path_if_live_then(ctx, key_path, value, ty, next)
    }

    fn lower_dynamic_drop_binding_then(
        &mut self,
        ctx: &Ctx,
        drop: &DropBinding,
        value: ExprId,
        next: ExprId,
    ) -> ExprId {
        self.lower_drop_key_path_if_live_then(ctx, &drop.key_path, value, &drop.ty, next)
    }

    fn lower_drop_key_path_if_live_then(
        &mut self,
        ctx: &Ctx,
        key_path: &Place,
        value: ExprId,
        ty: &CheckTy,
        next: ExprId,
    ) -> ExprId {
        let Some(&flag) = ctx.drop_flags.get(key_path) else {
            return self.lower_drop_value_with_dynamic_fields_then(ctx, key_path, value, ty, next);
        };
        let after_drop = self.set_drop_flag_then(ctx, key_path, false, next);
        let drop_body =
            self.lower_drop_value_with_dynamic_fields_then(ctx, key_path, value, ty, after_drop);
        let bool_ty = self.p.ty_bool();
        let live = self.p.primop(Op::CellGet, &[flag], bool_ty);
        self.branch_value(live, drop_body, next)
    }

    fn lower_drop_value_with_dynamic_fields_then(
        &mut self,
        ctx: &Ctx,
        key_path: &Place,
        value: ExprId,
        ty: &CheckTy,
        next: ExprId,
    ) -> ExprId {
        if !self.needs_drop_type(ty) {
            return next;
        }
        match Self::borrow_erased_ty(ty.clone()) {
            CheckTy::Nominal(symbol, args) => {
                if self.symbol_is_borrowed(symbol) {
                    return next;
                }
                // An enum's owned payloads drop under a tag dispatch: one
                // switch arm per variant, each dropping that variant's
                // owned payloads, joining back to `next`.
                if self.is_enum(symbol) {
                    return self.lower_enum_payloads_then(
                        ctx,
                        value,
                        symbol,
                        &args,
                        next,
                        PayloadAction::Drop,
                    );
                }
                // A `Deinit` conformance runs the user's destructor, which
                // consumes the value; its own body then drops the fields
                // (its scope-exit drops), so no structural teardown follows
                // here. Inside the deinit body itself, dropping self skips
                // the dispatch (fields only) — no recursion.
                if let Some(witness) = self.deinit_witness(symbol)
                    && ctx.owner != Some(witness)
                {
                    let theta = self.nominal_theta(symbol, &args);
                    let label = self.demand(witness, theta);
                    let fn_ref = self.p.func_ref(label);
                    let void_ty = self.p.ty_void();
                    let bot = self.p.ty_bot();
                    let cont = self.p.func("after_deinit", void_ty, bot);
                    self.p.set_body(cont, next);
                    let cont_ref = self.p.func_ref(cont);
                    let args_tuple = self.p.tuple(&[value, cont_ref]);
                    return self.p.app(fn_ref, args_tuple);
                }
                if let Some(index) = self.rawptr_field_index(symbol) {
                    let ptr_ty = self.p.ty_ptr();
                    let ptr = self.p.primop(Op::GetField(index), &[value], ptr_ty);
                    let void_ty = self.p.ty_void();
                    let free = self.p.primop(Op::Free, &[ptr], void_ty);
                    return self.sequence_void_effect(free, next);
                }
                let fields = self.field_types_for(symbol, &args);
                let mut body = next;
                for (index, (field_symbol, field_ty)) in fields.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(&field_ty) {
                        continue;
                    }
                    let field_key_path = key_path.child(field_symbol);
                    let field_lambda_ty = self.map_ty(&field_ty);
                    let field_value =
                        self.p
                            .primop(Op::GetField(index as u32), &[value], field_lambda_ty);
                    body = if ctx.drop_flags.contains_key(&field_key_path) {
                        self.lower_drop_key_path_if_live_then(
                            ctx,
                            &field_key_path,
                            field_value,
                            &field_ty,
                            body,
                        )
                    } else {
                        self.lower_drop_value_with_dynamic_fields_then(
                            ctx,
                            &field_key_path,
                            field_value,
                            &field_ty,
                            body,
                        )
                    };
                }
                body
            }
            CheckTy::Tuple(items) => {
                let mut body = next;
                for (index, item_ty) in items.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(&item_ty) {
                        continue;
                    }
                    let field_value = self.p.extract(value, index as u32);
                    body = self.lower_drop_value_then(ctx, field_value, &item_ty, body);
                }
                body
            }
            CheckTy::Record(row) if row.tail.is_none() => {
                let mut body = next;
                for (index, (_, field_ty)) in row.fields.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(&field_ty) {
                        continue;
                    }
                    let field_value = self.p.extract(value, index as u32);
                    body = self.lower_drop_value_then(ctx, field_value, &field_ty, body);
                }
                body
            }
            CheckTy::Any { .. } => next,
            _ => next,
        }
    }

    /// One `GradeView` per unit: each unit's catalog is import-closed
    /// (check_types merges every visible module's catalog), so a type is
    /// classified by whichever unit can see all its symbols. The flow
    /// checker's `GradeView` is the single definition of owned / object /
    /// borrowed — lowering must agree with it for scheduled drops to
    /// match emitted ones.
    fn grade_views(&self) -> impl Iterator<Item = crate::flow::grades::GradeView<'_>> {
        self.units
            .iter()
            .map(|unit| crate::flow::grades::GradeView::new(unit.types))
    }

    pub(super) fn needs_drop_type(&self, ty: &CheckTy) -> bool {
        self.grade_views().any(|grades| grades.needs_drop(ty))
    }

    /// Owned parts to drop OR `'heap` handles to release: the binding gets
    /// scope-exit processing either way.
    pub(super) fn needs_release_type(&self, ty: &CheckTy) -> bool {
        self.needs_drop_type(ty) || self.contains_object_type(ty)
    }

    /// Whether a value of this type may carry a `'heap` handle anywhere.
    pub(super) fn contains_object_type(&self, ty: &CheckTy) -> bool {
        self.grade_views().any(|grades| grades.contains_object(ty))
    }

    /// A pure place read (variable or stored-field chain): carries no
    /// unclaimed region count. Anything else is an rvalue.
    pub(super) fn rhs_is_rvalue(&self, rhs: &Expr, _ctx: &Ctx) -> bool {
        fn is_place(expr: &Expr) -> bool {
            match &expr.kind {
                ExprKind::Variable(_) => true,
                ExprKind::Member(Some(receiver), _) | ExprKind::Proj(receiver, ..) => {
                    is_place(receiver)
                }
                _ => false,
            }
        }
        !is_place(rhs)
    }

    pub(super) fn field_types_for(
        &self,
        symbol: Symbol,
        args: &[CheckTy],
    ) -> Vec<(Symbol, CheckTy)> {
        let Some(info) = self
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(&symbol))
        else {
            return vec![];
        };
        let substitution: Theta = info
            .params
            .iter()
            .copied()
            .zip(args.iter().cloned())
            .collect();
        info.fields
            .values()
            .map(|(field_symbol, field_ty)| {
                (
                    *field_symbol,
                    field_ty.substitute(&substitution, &Default::default(), &Default::default()),
                )
            })
            .collect()
    }

    pub(super) fn rawptr_field_index(&self, symbol: Symbol) -> Option<u32> {
        self.units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(&symbol))
            .and_then(|info| {
                info.fields
                    .values()
                    .position(|(_, ty)| {
                        matches!(ty, CheckTy::Nominal(head, _) if *head == Symbol::RawPtr)
                    })
                    .map(|index| index as u32)
            })
    }

    pub(super) fn symbol_is_borrowed(&self, symbol: Symbol) -> bool {
        // The `Borrowed` marker conformance, read structurally from the
        // catalog (the legacy fact set is empty under the flow checker).
        self.units.iter().any(|unit| {
            unit.types
                .catalog
                .conformances
                .contains_key(&(symbol, Symbol::Borrowed))
        })
    }

    /// A continuation that discards its value and jumps to `target` with ().
    pub(super) fn discarding_cont(&mut self, value_ty: TyId, target: ExprId) -> ExprId {
        let bot = self.p.ty_bot();
        let cont = self.p.func("discard", value_ty, bot);
        let void = self.p.void();
        let body = self.p.app(target, void);
        self.p.set_body(cont, body);
        self.p.func_ref(cont)
    }
}
