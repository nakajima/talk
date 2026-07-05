use super::*;

impl<'a> Lowering<'a> {
    // ----- Records -----------------------------------------------------------

    /// Array literals allocate raw bytes internally, but the public Array
    /// storage field may now be a managed storage wrapper. If the core
    /// Array still has the old RawPtr layout, leave the pointer untouched.
    pub(super) fn array_storage_value(
        &mut self,
        array_symbol: Symbol,
        ptr: ExprId,
    ) -> Option<ExprId> {
        let Some(field_ty) = self
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(&array_symbol))
            .and_then(|info| info.fields.get("storage").map(|(_, ty)| ty.clone()))
        else {
            return Some(ptr);
        };
        self.storage_wrapper_value(&field_ty, ptr, "Array")
    }

    /// String literals also start from a raw pointer into static bytes, while
    /// the source-level String may store a managed byte storage wrapper.
    pub(super) fn string_storage_value(
        &mut self,
        string_symbol: Symbol,
        ptr: ExprId,
    ) -> Option<ExprId> {
        let Some(field_ty) = self
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(&string_symbol))
            .and_then(|info| {
                info.fields
                    .get("storage")
                    .or_else(|| info.fields.get("base"))
                    .map(|(_, ty)| ty.clone())
            })
        else {
            return Some(ptr);
        };
        self.storage_wrapper_value(&field_ty, ptr, "String")
    }

    pub(super) fn storage_wrapper_value(
        &mut self,
        field_ty: &CheckTy,
        ptr: ExprId,
        owner: &str,
    ) -> Option<ExprId> {
        let CheckTy::Nominal(storage_symbol, _) = field_ty else {
            self.diagnostics.push(format!(
                "lowering: {owner} storage field is not RawPtr or a RawPtr wrapper"
            ));
            return None;
        };
        if *storage_symbol == Symbol::RawPtr {
            return Some(ptr);
        }
        let Some(storage_info) = self
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(storage_symbol))
        else {
            self.diagnostics.push(format!(
                "lowering: {owner} storage wrapper does not resolve to a struct"
            ));
            return None;
        };
        if storage_info.fields.len() != 1 {
            self.diagnostics.push(format!(
                "lowering: {owner} storage wrapper does not expose a RawPtr field"
            ));
            return None;
        }
        let Some((_, CheckTy::Nominal(head, _))) =
            storage_info.fields.values().next().map(|(_, ty)| ((), ty))
        else {
            self.diagnostics.push(format!(
                "lowering: {owner} storage wrapper does not expose a RawPtr field"
            ));
            return None;
        };
        if *head != Symbol::RawPtr {
            self.diagnostics.push(format!(
                "lowering: {owner} storage wrapper does not expose a RawPtr field"
            ));
            return None;
        }
        let storage_ty = self.map_ty(field_ty);
        Some(
            self.p
                .primop(Op::RecordNew(*storage_symbol), &[ptr], storage_ty),
        )
    }

    /// GetField for a member read: through member_resolutions when the
    /// checker saw the node, else by name against the receiver's record
    /// type (@_ir binds are trusted, not inferred, so they carry no
    /// resolutions).
    pub(super) fn field_read(
        &mut self,
        expr: &Expr,
        receiver: &Expr,
        receiver_value: ExprId,
        ctx: &Ctx,
    ) -> Option<ExprId> {
        // Anonymous records are label-sorted tuples (map_ty), so a field
        // read is an extract at the label's canonical position.
        let head = Self::borrow_erased_ty(self.checker_ty(receiver, ctx));
        if let CheckTy::Record(row) = &head
            && row.tail.is_none()
            && let ExprKind::Member(_, label) | ExprKind::Proj(_, label, _) = &expr.kind
            && let Some(index) = row
                .fields
                .iter()
                .position(|(name, _)| name.to_string() == label.to_string())
        {
            return Some(self.p.extract(receiver_value, index as u32));
        }
        let resolution = expr.member_resolution.clone();
        if let Some(crate::types::output::MemberResolution::Direct(property)) = resolution {
            let index = self.field_index(&head, property)?;
            let field_check_ty = self.checker_ty(expr, ctx);
            let field_ty = self.map_ty(&field_check_ty);
            let op = match self.p.ty_kind(self.p.expr_ty(receiver_value)) {
                TyKind::Object(_) => Op::ObjectGet(index),
                _ => Op::GetField(index),
            };
            return Some(self.p.primop(op, &[receiver_value], field_ty));
        }

        let ExprKind::Member(_, label) = &expr.kind else {
            return None;
        };
        let TyKind::Boxed(record_symbol) = *self.p.ty_kind(self.p.expr_ty(receiver_value)) else {
            return None;
        };
        let info = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.structs.get(&record_symbol))?;
        let (index, field_ty) = info
            .fields
            .iter()
            .enumerate()
            .find(|(_, (name, _))| *name == &label.to_string())
            .map(|(i, (_, (_, ty)))| (i as u32, ty.clone()))?;
        let field_ty = self.map_ty(&field_ty);
        Some(
            self.p
                .primop(Op::GetField(index), &[receiver_value], field_ty),
        )
    }

    /// Is this callee a stored field holding a function value — a call
    /// through a record field (`self.route_handler0.invoke()`), as
    /// opposed to a method call? Field callees dispatch indirectly.
    pub(super) fn is_field_value_callee(&mut self, callee: &Expr, ctx: &Ctx) -> bool {
        let (ExprKind::Member(Some(receiver), label) | ExprKind::Proj(receiver, label, _)) =
            &callee.kind
        else {
            return false;
        };
        let head = Self::borrow_erased_ty(self.checker_ty(receiver, ctx));
        match callee.member_resolution.clone() {
            Some(crate::types::output::MemberResolution::Direct(property)) => {
                self.field_index(&head, property).is_some()
            }
            Some(_) => false,
            None => {
                let CheckTy::Nominal(head_symbol, _) = head else {
                    return false;
                };
                self.units
                    .iter()
                    .find_map(|u| u.types.catalog.structs.get(&head_symbol))
                    .is_some_and(|info| info.fields.contains_key(&label.to_string()))
            }
        }
    }

    /// The position of `property` in the head struct's declared field
    /// order (the record layout).
    pub(super) fn field_index(&mut self, head: &CheckTy, property: Symbol) -> Option<u32> {
        let CheckTy::Nominal(head_symbol, _) = head else {
            return None;
        };
        let info = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.structs.get(head_symbol))?;
        info.fields
            .values()
            .position(|(symbol, _)| *symbol == property)
            .map(|i| i as u32)
    }

    // ----- Enums ---------------------------------------------------------

    /// The catalog row for an enum symbol (cloned: callers keep building
    /// the program while reading it).
    pub(super) fn enum_info(&self, symbol: Symbol) -> Option<crate::types::catalog::Enum> {
        self.units
            .iter()
            .find_map(|u| u.types.catalog.enums.get(&symbol).cloned())
    }

    pub(super) fn is_enum(&self, symbol: Symbol) -> bool {
        self.units
            .iter()
            .any(|u| u.types.catalog.enums.contains_key(&symbol))
    }

    pub(super) fn is_init(&self, symbol: Symbol) -> bool {
        self.units.iter().any(|u| {
            u.types
                .catalog
                .structs
                .values()
                .any(|info| info.inits.contains(&symbol))
        })
    }

    /// Construct a variant value: source payloads followed by hidden runtime
    /// evidence for GADT-local constructor bounds.
    pub(super) fn variant_new_for_expr(
        &mut self,
        site: VariantSite,
        enum_symbol: Symbol,
        tag: u16,
        variant_symbol: Symbol,
        payloads: &[ExprId],
        ctx: &Ctx,
    ) -> ExprId {
        let mut runtime_payloads = payloads.to_vec();
        runtime_payloads.extend(self.variant_evidence_tables(site, variant_symbol, ctx));
        self.variant_new(enum_symbol, tag, &runtime_payloads)
    }

    pub(super) fn variant_evidence_tables(
        &mut self,
        site: VariantSite,
        variant_symbol: Symbol,
        ctx: &Ctx,
    ) -> Vec<ExprId> {
        let Some(variant) = self.variant_by_symbol(variant_symbol) else {
            return vec![];
        };
        let theta = self.instantiation_at(site.instantiation.as_ref(), ctx);
        let mut tables = vec![];
        for predicate in &variant.constructor_scheme.predicates {
            let crate::types::ty::Predicate::Conforms { ty, protocol } = predicate else {
                continue;
            };
            let CheckTy::Param(param) = ty else {
                continue;
            };
            let concrete = theta.get(param).cloned().unwrap_or(CheckTy::Param(*param));
            match self.evidence_table_for_ty(*protocol, &concrete, ctx, site.node) {
                Some(table) => tables.push(table),
                None => {
                    self.diagnostics.push(format!(
                        "lowering: cannot store runtime evidence for constructor bound {param}: {protocol}"
                    ));
                    tables.push(self.p.tuple(&[]));
                }
            }
        }
        tables
    }

    pub(super) fn variant_pattern_evidence(
        &mut self,
        variant: &crate::types::catalog::Variant,
        instantiation: &crate::types::variant::VariantInstantiation,
        value: ExprId,
        source_payload_count: usize,
        unit: usize,
    ) -> Vec<((Symbol, Symbol), EvidenceBinding)> {
        let mut evidence = vec![];
        let mut runtime_index = source_payload_count as u32;
        let subst: Theta = instantiation.instantiations.iter().cloned().collect();
        for source in &variant.constructor_scheme.predicates {
            let crate::types::ty::Predicate::Conforms {
                ty: CheckTy::Param(source_param),
                protocol,
            } = source
            else {
                continue;
            };
            let instantiated = source.substitute(&subst, &Default::default(), &Default::default());
            if let crate::types::ty::Predicate::Conforms {
                ty: CheckTy::Param(param),
                ..
            } = instantiated
            {
                let table_ty = self.evidence_table_ty(*protocol, &[], unit);
                let table = self
                    .p
                    .primop(Op::GetPayload(runtime_index), &[value], table_ty);
                evidence.push((
                    (param, *protocol),
                    EvidenceBinding {
                        protocol: *protocol,
                        table,
                    },
                ));
            }
            let _ = source_param;
            runtime_index += 1;
        }
        evidence
    }

    pub(super) fn variant_by_symbol(
        &self,
        variant_symbol: Symbol,
    ) -> Option<crate::types::catalog::Variant> {
        for unit in &self.units {
            for info in unit.types.catalog.enums.values() {
                if let Some(variant) = info
                    .variants
                    .values()
                    .find(|variant| variant.symbol == variant_symbol)
                {
                    return Some(variant.clone());
                }
            }
        }
        None
    }

    /// Construct a raw variant value: pure, exactly like `RecordNew`.
    pub(super) fn variant_new(
        &mut self,
        enum_symbol: Symbol,
        tag: u16,
        payloads: &[ExprId],
    ) -> ExprId {
        let ty = self.p.ty(TyKind::Variant(enum_symbol));
        self.p
            .primop(Op::VariantNew(enum_symbol, tag), payloads, ty)
    }

    /// For a record literal: row position → source field index, from the
    /// checker's (label-sorted) row. Fields still *evaluate* in source
    /// order; this permutation only places the values.
    pub(super) fn record_field_order(
        &mut self,
        expr: &Expr,
        fields: &[hir::RecordField],
        ctx: &Ctx,
    ) -> Option<Vec<usize>> {
        let CheckTy::Record(row) = self.checker_ty(expr, ctx) else {
            return None;
        };
        if row.tail.is_some() || row.fields.len() != fields.len() {
            return None;
        }
        row.fields
            .iter()
            .map(|(label, _)| {
                let name = label.to_string();
                fields.iter().position(|f| f.label.name_str() == name)
            })
            .collect()
    }

    /// Intern string-literal bytes into static memory (deduplicated).
    pub(super) fn intern_static(&mut self, bytes: &[u8]) -> u32 {
        if let Some(&offset) = self.statics.get(bytes) {
            return offset;
        }
        let offset = self.p.static_mem.len() as u32;
        self.p.static_mem.extend_from_slice(bytes);
        if bytes.is_empty() {
            // A zero-length static still needs an address strictly inside
            // the region: at the region's end its offset would equal
            // static_len and alias the first heap allocation, whose free
            // would then release the wrong buffer.
            self.p.static_mem.push(0);
        }
        self.statics.insert(bytes.to_vec(), offset);
        offset
    }
}
