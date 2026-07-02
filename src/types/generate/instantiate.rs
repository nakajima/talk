use super::*;

impl<'s, 'a> BodyChecker<'s, 'a> {
    // ----- Names, annotations, helpers ----------------------------------

    pub(super) fn lookup(&mut self, name: &Name, node: NodeID, ctx: &Ctx) -> Ty {
        let Ok(symbol) = name.symbol() else {
            // The name resolver already diagnosed this; poison quietly.
            return Ty::Error;
        };
        self.lookup_symbol_ty(symbol, node, ctx)
    }

    pub(super) fn lookup_symbol_ty(&mut self, symbol: Symbol, node: NodeID, ctx: &Ctx) -> Ty {
        // A reference edge for the capability tables. Locals land here
        // too; they are harmless noise (the consumer only chases
        // abort-capable targets, and symbols are never reused).
        if let Some(binder) = ctx.binder
            && binder != symbol
        {
            self.artifacts
                .binder_refs
                .entry(binder)
                .or_default()
                .insert(symbol);
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
            let var = Ty::Var(self.store.fresh_ty(self.level, node));
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

        // The scheme's qualified context becomes fresh wanteds under the
        // instantiation substitution (Jones's qualified-type instantiation).
        // This subsumes inline bounds and scheme-carried HasMember facts.
        for predicate in &scheme.predicates {
            self.wanteds.push(
                predicate
                    .substitute(&tys, &effs, &rows)
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

    pub(super) fn record_instantiation(&mut self, node: NodeID, params: &[Symbol], theta: &[Ty]) {
        self.artifacts
            .instantiations
            .entry(node)
            .or_default()
            .extend(params.iter().copied().zip(theta.iter().cloned()));
    }

    /// Explicit call-site type arguments (`_alloc<Element>(capacity)`)
    /// equate positionally with the instantiation recorded at the callee
    /// (scheme params list declared generics first, in order).
    pub(super) fn apply_type_args(&mut self, callee_node: NodeID, type_args: &[TypeAnnotation]) {
        let recorded: Vec<Ty> = self
            .artifacts
            .instantiations
            .get(&callee_node)
            .map(|subst| subst.iter().map(|(_, ty)| ty.clone()).collect())
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
        for (annotation, target) in type_args.iter().zip(recorded) {
            let ty = self.lower_annotation(annotation);
            self.emit_eq(target, ty, annotation.id, CtReason::Annotation);
        }
    }

    pub(super) fn callable_arity(&mut self, symbol: Symbol) -> Option<usize> {
        if let Some(scheme) = self.schemes.get(&symbol)
            && let Ty::Func(params, ..) = &scheme.ty
        {
            return Some(params.len());
        }
        if let Some(ty) = self.mono.get(&symbol).cloned()
            && let Ty::Func(params, ..) = self.store.shallow(&ty)
        {
            return Some(params.len());
        }
        None
    }
}
