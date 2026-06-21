use super::*;

/// Generalize a binding group's types after its solve: quantify exactly the
/// unsolved variables deeper than `base_level` (Rémy levels), minting a rigid
/// `Param` for each and binding the variable to it in the store, so every
/// type that shared the variable (other binders in the group, node types for
/// hover) sees the same parameter — THIH §11.6.3's per-group quantification.
/// Residual variable-headed predicates attach to the minted parameters'
/// scheme context (THIH section 11.6's retained predicates for implicitly
/// typed binding groups).
pub struct Generalizer<'s> {
    pub store: &'s mut VarStore,
    pub symbols: &'s mut Symbols,
    pub module_id: crate::compiling::module::ModuleId,
    pub base_level: Level,
    /// Residual predicates keyed by the type-variable root that caused them
    /// to float out of solving. Generalization quantifies those variables and
    /// attaches the predicates to the scheme's qualified context.
    var_predicates: FxHashMap<u32, Vec<Predicate>>,
    /// Params minted by THIS group's generalization (plus declared generics
    /// seeded per binder). A scheme quantifies a rigid `Param` only if this
    /// group minted it — pre-existing rigids (e.g. the enclosing struct's
    /// generics in a method type) stay free and are substituted at member
    /// access instead.
    minted: rustc_hash::FxHashSet<Symbol>,
    params: Vec<SchemeParam>,
    eff_params: Vec<Symbol>,
    row_params: Vec<Symbol>,
    predicates: Vec<Predicate>,
}

impl<'s> Generalizer<'s> {
    pub fn new(
        store: &'s mut VarStore,
        symbols: &'s mut Symbols,
        module_id: crate::compiling::module::ModuleId,
        base_level: Level,
        var_predicates: FxHashMap<u32, Vec<Predicate>>,
    ) -> Self {
        Generalizer {
            store,
            symbols,
            module_id,
            base_level,
            var_predicates,
            minted: Default::default(),
            params: vec![],
            eff_params: vec![],
            row_params: vec![],
            predicates: vec![],
        }
    }

    /// Quantify the generalizable variables of `ty`, in order of appearance,
    /// seeding the scheme with the binder's declared generic parameters.
    /// Call once per binder; variables already generalized (bound to Params)
    /// are shared across the group's schemes automatically.
    pub fn generalize(&mut self, ty: &Ty, declared: &[SchemeParam]) -> Scheme {
        let zonked = self.store.zonk_ty(ty);
        self.params = declared.to_vec();
        for param in declared {
            self.minted.insert(param.symbol);
        }
        self.eff_params.clear();
        self.row_params.clear();
        self.predicates.clear();
        let ty = self.quantify_ty(&zonked);
        Scheme {
            params: std::mem::take(&mut self.params),
            eff_params: std::mem::take(&mut self.eff_params),
            row_params: std::mem::take(&mut self.row_params),
            predicates: std::mem::take(&mut self.predicates),
            ty,
        }
    }

    pub(super) fn mint_param(&mut self) -> Symbol {
        let param = Symbol::TypeParameter(self.symbols.next_type_parameter(self.module_id));
        self.minted.insert(param);
        param
    }

    pub(super) fn quantify_predicate(&mut self, predicate: &Predicate) -> Predicate {
        match predicate {
            Predicate::TypeEq(a, b) => Predicate::TypeEq(self.quantify_ty(a), self.quantify_ty(b)),
            Predicate::EffectEq(a, b) => {
                Predicate::EffectEq(self.quantify_eff(a), self.quantify_eff(b))
            }
            Predicate::RowEq(a, b) => Predicate::RowEq(self.quantify_row(a), self.quantify_row(b)),
            Predicate::Conforms { ty, protocol } => Predicate::Conforms {
                ty: self.quantify_ty(ty),
                protocol: *protocol,
            },
            Predicate::HasMember {
                receiver,
                label,
                member,
            } => Predicate::HasMember {
                receiver: self.quantify_ty(receiver),
                label: label.clone(),
                member: self.quantify_ty(member),
            },
        }
    }

    pub(super) fn quantify_row(&mut self, row: &Row) -> Row {
        match self.quantify_ty(&Ty::Record(row.clone())) {
            Ty::Record(row) => row,
            _ => row.clone(),
        }
    }

    /// Quantify the binding group's leftover variables. The structural
    /// recursion is `TyFold`; the store-aware, param-minting leaves are in the
    /// impl below.
    pub(super) fn quantify_ty(&mut self, ty: &Ty) -> Ty {
        self.fold_ty(ty)
    }

    pub(super) fn quantify_eff(&mut self, eff: &EffectRow) -> EffectRow {
        let zonked = self.store.zonk_eff(eff);
        let tail = match zonked.tail {
            Some(EffTail::Var(v)) if self.store.level(v.0) > self.base_level => {
                let param = self.mint_param();
                self.store.bind(
                    v.0,
                    VarValue::Eff(EffectRow {
                        effects: BTreeSet::new(),
                        tail: Some(EffTail::Param(param)),
                    }),
                );
                self.eff_params.push(param);
                Some(EffTail::Param(param))
            }
            Some(EffTail::Param(sym)) => {
                if !self.eff_params.contains(&sym) {
                    self.eff_params.push(sym);
                }
                Some(EffTail::Param(sym))
            }
            other => other,
        };
        EffectRow {
            effects: zonked.effects,
            tail,
        }
    }
}

/// Generalization is the param-minting `TyFold`: a variable deeper than the
/// group's base level becomes a fresh rigid `Param` (bound in the store so all
/// sharers see it); shallower variables stay free. Effect/row var tails mint
/// row/effect params the same way.
impl TyFold for Generalizer<'_> {
    fn fold_var(&mut self, var: TyVar) -> Ty {
        match self.store.shallow(&Ty::Var(var)) {
            Ty::Var(root_var) => {
                let root = root_var.0;
                if self.store.level(root) > self.base_level {
                    let param = self.mint_param();
                    self.store.bind(root, VarValue::Ty(Ty::Param(param)));
                    self.params.push(SchemeParam { symbol: param });
                    if let Some(predicates) = self.var_predicates.remove(&root) {
                        for predicate in predicates {
                            let predicate = self.quantify_predicate(&predicate);
                            if !self.predicates.contains(&predicate) {
                                self.predicates.push(predicate);
                            }
                        }
                    }
                    Ty::Param(param)
                } else {
                    Ty::Var(TyVar(root))
                }
            }
            resolved => self.fold_ty(&resolved),
        }
    }

    fn fold_param(&mut self, symbol: Symbol) -> Ty {
        // Quantified earlier by this same group: include it in this scheme's
        // parameter list too (params are per-scheme). Rigid params from
        // elsewhere (a nominal's generics) stay free.
        if self.minted.contains(&symbol) && !self.params.iter().any(|p| p.symbol == symbol) {
            self.params.push(SchemeParam { symbol });
        }
        Ty::Param(symbol)
    }

    fn fold_eff(&mut self, eff: &EffectRow) -> EffectRow {
        self.quantify_eff(eff)
    }

    fn fold_row(&mut self, row: &Row) -> Row {
        let zonked = self.store.zonk_row(row);
        let fields = zonked
            .fields
            .iter()
            .map(|(l, t)| (l.clone(), self.fold_ty(t)))
            .collect();
        let tail = match zonked.tail {
            Some(RowTail::Var(v)) if self.store.level(v.0) > self.base_level => {
                let param = self.mint_param();
                self.store.bind(
                    v.0,
                    VarValue::Row(Row {
                        fields: vec![],
                        tail: Some(RowTail::Param(param)),
                    }),
                );
                self.row_params.push(param);
                Some(RowTail::Param(param))
            }
            other => other,
        };
        Row { fields, tail }
    }
}
