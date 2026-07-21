use super::*;

impl<'s, 'a> BodyChecker<'s, 'a> {
    // ----- Names, annotations, helpers ----------------------------------

    pub(super) fn lookup(&mut self, name: &Name, node: NodeID) -> Ty {
        let Ok(symbol) = name.symbol() else {
            // The name resolver already diagnosed this; poison quietly.
            return Ty::Error;
        };
        self.lookup_symbol_ty(symbol, node)
    }

    pub(super) fn lookup_symbol_ty(&mut self, symbol: Symbol, node: NodeID) -> Ty {
        // ADR 0035 §6: a static parameter used as an ordinary value HAS
        // its declared value type. The frontend owns this typing; the
        // backend only substitutes the instance's concrete value.
        if let Some(value_ty) = self.catalog.static_params.get(&symbol) {
            return value_ty.clone();
        }
        if let Some(ty) = self.mono.get(&symbol) {
            return ty.clone();
        }
        if let Some(scheme) = self.schemes.get(&symbol).cloned() {
            return self.instantiate(&scheme, node);
        }
        // Referenced before its (later) group runs: park a conservative
        // outer-level variable; that group will reuse and solve it, and will
        // skip generalization for whatever it touched.
        let ty = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, node));
        self.mono.insert(symbol, ty.clone());
        ty
    }

    /// Instantiate a scheme with fresh variables (Damas-Milner) and record
    /// the substitution for the lowerer (the "call sites and substitutions"
    /// surface).
    pub(super) fn instantiate(&mut self, scheme: &Scheme, node: NodeID) -> Ty {
        if scheme.params.is_empty()
            && scheme.eff_params.is_empty()
            && scheme.row_params.is_empty()
            && scheme.perm_params.is_empty()
        {
            return scheme.ty.clone();
        }

        let mut tys = FxHashMap::default();
        let mut recorded = vec![];
        for param in &scheme.params {
            let fresh = self.store.fresh_ty(self.level, node);
            if let crate::types::ty::ParamKind::Static(value_ty) = &param.kind {
                // ADR 0035 §5: a hole standing for a static argument left
                // unresolved at finalization gets a targeted diagnostic.
                self.store.mark_static_hole(fresh);
                // ADR 0035 §2: instantiating forms an application, and
                // every integer static argument owes nonnegativity,
                // however the hole gets solved (inference, explicit
                // argument, or a materialized default).
                if matches!(value_ty, Ty::Nominal(symbol, _) if *symbol == Symbol::Int) {
                    self.wanteds.push(Constraint::StaticCmp {
                        op: crate::types::ty::StaticCmpOp::Le,
                        lhs: Ty::Static(StaticValue::Int(StaticInt::constant(0))),
                        rhs: Ty::Var(fresh),
                        origin: CtOrigin::new(node, CtReason::Apply),
                    });
                }
            }
            let var = Ty::Var(fresh);
            recorded.push((param.symbol, var.clone()));
            tys.insert(param.symbol, var);
        }
        let mut effs = FxHashMap::default();
        for param in &scheme.eff_params {
            effs.insert(
                *param,
                crate::types::ty::EffTail::Var(self.store.fresh_eff(self.level, node)),
            );
        }
        let mut rows = FxHashMap::default();
        for param in &scheme.row_params {
            let var = self.store.fresh_row(self.level, node);
            // Recorded as an empty open record over the fresh variable:
            // zonking at finalize resolves it to the call's concrete row
            // (what monomorphization splices into the signature).
            recorded.push((
                *param,
                Ty::Record(crate::types::ty::Row {
                    fields: vec![],
                    tail: Some(crate::types::ty::RowTail::Var(var)),
                }),
            ));
            rows.insert(*param, crate::types::ty::RowTail::Var(var));
        }

        let mut perms = FxHashMap::default();
        for param in &scheme.perm_params {
            perms.insert(
                *param,
                crate::types::ty::Perm::Var(self.store.fresh_perm(self.level, node)),
            );
        }

        // Declared defaults are inference fallbacks at call sites: if
        // nothing else pins the fresh variable by quiescence, it takes
        // the default (PreferEq semantics); an inferred or explicit
        // argument always wins.
        for param in &scheme.params {
            if let Some(default) = &param.default
                && !matches!(default, Ty::Error)
            {
                let default = default.substitute(&tys, &effs, &rows);
                self.wanteds.push(Constraint::PreferEq(
                    tys[&param.symbol].clone(),
                    default,
                    CtOrigin::new(node, CtReason::Apply),
                ));
            }
        }

        // The scheme's qualified context becomes fresh wanteds under the
        // instantiation substitution (Jones's qualified-type instantiation).
        // This subsumes inline bounds and scheme-carried HasMember facts.
        // Perms substitute here too: a predicate mentioning a quantified
        // `Perm::Param` must see the same fresh var the scheme type gets.
        for predicate in &scheme.predicates {
            self.wanteds.push(
                predicate
                    .substitute(&tys, &effs, &rows)
                    .substitute_perms(&perms)
                    .into_constraint(CtOrigin::new(node, CtReason::Apply)),
            );
        }
        self.artifacts
            .instantiations
            .entry(node)
            .or_default()
            .extend(recorded);
        scheme
            .ty
            .substitute(&tys, &effs, &rows)
            .substitute_perms(&perms)
    }

    /// Fresh effect- and row-tail variables for a variant's quantified effect
    /// and row parameters. The type parameters are freshened by the caller
    /// (as inference vars for expressions, rigid params for patterns).
    pub(super) fn fresh_variant_eff_rows(
        &mut self,
        variant: &Variant,
        node: NodeID,
    ) -> (FxHashMap<Symbol, EffTail>, FxHashMap<Symbol, RowTail>) {
        let mut effs = FxHashMap::default();
        for param in &variant.constructor_scheme.eff_params {
            effs.insert(*param, EffTail::Var(self.store.fresh_eff(self.level, node)));
        }
        let mut rows = FxHashMap::default();
        for param in &variant.constructor_scheme.row_params {
            rows.insert(*param, RowTail::Var(self.store.fresh_row(self.level, node)));
        }
        (effs, rows)
    }

    pub(super) fn instantiate_variant(
        &mut self,
        variant: &Variant,
        mut tys: FxHashMap<Symbol, Ty>,
        node: NodeID,
    ) -> VariantInstantiation {
        for param in &variant.constructor_scheme.params {
            tys.entry(param.symbol)
                .or_insert_with(|| Ty::Var(self.store.fresh_ty(self.level, node)));
        }
        let (effs, rows) = self.fresh_variant_eff_rows(variant, node);
        variant.instantiate(&tys, &effs, &rows)
    }

    pub(super) fn instantiate_variant_pattern(
        &mut self,
        variant: &Variant,
        mut tys: FxHashMap<Symbol, Ty>,
        node: NodeID,
    ) -> (VariantInstantiation, Vec<Symbol>) {
        let mut local_params = vec![];
        for param in &variant.constructor_scheme.params {
            tys.entry(param.symbol).or_insert_with(|| {
                let local = Symbol::TypeParameter(self.symbols.next_type_parameter(self.module_id));
                local_params.push(local);
                Ty::Param(local)
            });
        }
        let (effs, rows) = self.fresh_variant_eff_rows(variant, node);
        (variant.instantiate(&tys, &effs, &rows), local_params)
    }

    pub(super) fn emit_variant_predicates(
        &mut self,
        instantiation: &VariantInstantiation,
        node: NodeID,
    ) {
        for predicate in &instantiation.givens {
            self.wanteds.push(
                predicate
                    .clone()
                    .into_constraint(CtOrigin::new(node, CtReason::Apply)),
            );
        }
    }

    pub(super) fn record_variant_instantiation(
        &mut self,
        node: NodeID,
        instantiation: &VariantInstantiation,
    ) {
        if !instantiation.instantiations.is_empty() {
            self.artifacts
                .instantiations
                .entry(node)
                .or_default()
                .extend(instantiation.instantiations.iter().cloned());
        }
    }

    pub(super) fn record_instantiation(
        &mut self,
        node: NodeID,
        params: &[SchemeParam],
        theta: &[Ty],
    ) {
        self.artifacts
            .instantiations
            .entry(node)
            .or_default()
            .extend(
                params
                    .iter()
                    .map(|param| param.symbol)
                    .zip(theta.iter().cloned()),
            );
    }

    /// Explicit call-site type arguments (`_alloc<Element>(capacity)`)
    /// equate positionally with the instantiation recorded at the callee
    /// (scheme params list declared generics first, in order).
    pub(super) fn apply_type_args(&mut self, callee_node: NodeID, type_args: &[GenericArg]) {
        let recorded: Vec<(Symbol, Ty)> = self
            .artifacts
            .instantiations
            .get(&callee_node)
            .cloned()
            .unwrap_or_default();
        // More explicit type arguments than the callee declares is an
        // error — but only when an instantiation was recorded (builtins
        // and trusted splices manage their own type arguments).
        if !recorded.is_empty() && type_args.len() > recorded.len() {
            self.diagnostics.errors.push((
                TypeError::ArityMismatch {
                    expected: recorded.len(),
                    found: type_args.len(),
                },
                callee_node,
            ));
        }
        for (type_arg, (param, target)) in type_args.iter().zip(recorded) {
            let ty = self.lower_generic_arg_for_param(param, type_arg);
            // The explicit argument owns its formation obligation (its
            // lowering emits nonnegativity at the argument's own node);
            // retract the instantiation hole's universal wanted so a
            // negative argument reports once, not twice.
            self.retract_hole_nonneg(&target);
            self.emit_eq(target, ty, type_arg.id(), CtReason::Annotation);
        }
    }

    /// Remove the pending `0 <= hole` formation wanted minted for a
    /// static-Int instantiation hole that an explicit argument has just
    /// filled. No-op for type-kind params (no such wanted exists).
    pub(super) fn retract_hole_nonneg(&mut self, target: &Ty) {
        let zero = Ty::Static(StaticValue::Int(StaticInt::constant(0)));
        self.wanteds.retain(|constraint| {
            !matches!(constraint, Constraint::StaticCmp {
                op: crate::types::ty::StaticCmpOp::Le,
                lhs,
                rhs,
                ..
            } if lhs == &zero && rhs == target)
        });
    }
}
