use super::*;
use crate::lower::mir;

impl<'a> Lowering<'a> {
    // ----- Blocks and statements -------------------------------------------

    /// Lower a block whose VALUE flows to continuation `k` (a Fn(R, ⊥)
    /// expression). A block's value is its final expression; divergent
    /// statements (return) ignore `k`.
    pub(super) fn lower_block(&mut self, block: &Block, ctx: &Ctx, k: ExprId) -> ExprId {
        // The single MIR build: from annotated HIR, drops already elaborated
        // by the flow checker's schedules on the block itself.
        let unit = &self.units[ctx.unit];
        let body = mir::build_function(unit.types, ctx.owner, block);
        self.lower_mir_body(&body, ctx, k)
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
    ) -> Option<(ExprId, Vec<(u32, TyId)>)> {
        match &lhs.kind {
            ExprKind::Variable(name) => {
                let symbol = name.symbol().ok();
                if let Some(Binding::Cell(cell)) = symbol.and_then(|s| ctx.env.get(&s).copied()) {
                    return Some((cell, vec![]));
                }
                // A mutable top-level binding assigned from inside a
                // function: its registered cell (captured like any value).
                if let Some(cell) = symbol.and_then(|s| self.top_level_cells.get(&s).copied()) {
                    return Some((cell, vec![]));
                }
                self.diagnostics
                    .push("lowering: assignment to a non-cell binding".into());
                None
            }
            ExprKind::Member(Some(receiver), label) => {
                let (cell, mut path) = self.assignment_target(receiver, ctx)?;
                let head = Self::borrow_erased_ty(self.checker_ty(receiver, ctx));
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
                Some((cell, path))
            }
            _ => {
                self.diagnostics
                    .push("lowering: assignment target not yet supported".into());
                None
            }
        }
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
        if !self.needs_drop_type(ctx.unit, ty) {
            return next;
        }
        match Self::borrow_erased_ty(ty.clone()) {
            CheckTy::Nominal(symbol, args) => {
                if self.symbol_is_borrowed(symbol) {
                    return next;
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
                for (index, (_, field_ty)) in fields.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(ctx.unit, &field_ty) {
                        continue;
                    }
                    let field_lambda_ty = self.map_ty(&field_ty);
                    let field_value =
                        self.p
                            .primop(Op::GetField(index as u32), &[value], field_lambda_ty);
                    body = self.lower_drop_value_then(ctx, field_value, &field_ty, body);
                }
                body
            }
            CheckTy::Tuple(items) => {
                let mut body = next;
                for (index, item_ty) in items.into_iter().enumerate().rev() {
                    if !self.needs_drop_type(ctx.unit, &item_ty) {
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
                    if !self.needs_drop_type(ctx.unit, &field_ty) {
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
        keys: &[OwnershipKeyPath],
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
        key_path: &OwnershipKeyPath,
        live: bool,
        next: ExprId,
    ) -> ExprId {
        let mut keys: Vec<OwnershipKeyPath> = ctx
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
        key_path: &OwnershipKeyPath,
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
        key_path: &OwnershipKeyPath,
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
        key_path: &OwnershipKeyPath,
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
        key_path: &OwnershipKeyPath,
        value: ExprId,
        ty: &CheckTy,
        next: ExprId,
    ) -> ExprId {
        if !self.needs_drop_type(ctx.unit, ty) {
            return next;
        }
        match Self::borrow_erased_ty(ty.clone()) {
            CheckTy::Nominal(symbol, args) => {
                if self.symbol_is_borrowed(symbol) {
                    return next;
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
                    if !self.needs_drop_type(ctx.unit, &field_ty) {
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
                    if !self.needs_drop_type(ctx.unit, &item_ty) {
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
                    if !self.needs_drop_type(ctx.unit, &field_ty) {
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

    pub(super) fn needs_drop_type(&self, unit: usize, ty: &CheckTy) -> bool {
        self.type_needs_drop(unit, ty, &mut FxHashSet::default())
    }

    pub(super) fn type_needs_drop(
        &self,
        unit: usize,
        ty: &CheckTy,
        visiting: &mut FxHashSet<Symbol>,
    ) -> bool {
        match ty {
            CheckTy::Borrow(_, _) => false,
            CheckTy::Nominal(symbol, args) => {
                if self.symbol_is_borrowed(*symbol) {
                    return false;
                }
                self.symbol_has_ability(*symbol, "Owner")
                    || self.nominal_needs_drop(unit, *symbol, args, visiting)
            }
            CheckTy::Tuple(items) => items
                .iter()
                .any(|item| self.type_needs_drop(unit, item, visiting)),
            CheckTy::Record(row) => row
                .fields
                .iter()
                .any(|(_, field_ty)| self.type_needs_drop(unit, field_ty, visiting)),
            CheckTy::Any { .. } => true,
            CheckTy::Func(..)
            | CheckTy::Proj(..)
            | CheckTy::Param(_)
            | CheckTy::Var(_)
            | CheckTy::Error => false,
        }
    }

    pub(super) fn nominal_needs_drop(
        &self,
        unit: usize,
        symbol: Symbol,
        args: &[CheckTy],
        visiting: &mut FxHashSet<Symbol>,
    ) -> bool {
        if !visiting.insert(symbol) {
            return false;
        }
        let result = self
            .field_types_for(symbol, args)
            .into_iter()
            .any(|(_, field_ty)| self.type_needs_drop(unit, &field_ty, visiting));
        visiting.remove(&symbol);
        result
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

    pub(super) fn symbol_has_ability(&self, symbol: Symbol, ability: &str) -> bool {
        let Some(protocol) = self.protocol_named(ability) else {
            return false;
        };
        self.units.iter().any(|unit| {
            unit.types
                .catalog
                .conformances_by_head
                .get(&symbol)
                .is_some_and(|protocols| {
                    protocols.iter().any(|candidate| {
                        unit.types
                            .catalog
                            .protocol_and_supers(*candidate)
                            .contains(&protocol)
                    })
                })
        })
    }

    pub(super) fn protocol_named(&self, name: &str) -> Option<Symbol> {
        self.units.iter().find_map(|unit| {
            unit.types
                .catalog
                .protocols
                .keys()
                .find(|symbol| {
                    unit.types
                        .display_names
                        .get(symbol)
                        .or_else(|| unit.resolved.symbol_names.get(symbol))
                        .is_some_and(|display| display == name)
                })
                .copied()
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
