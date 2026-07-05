use super::*;

#[derive(Clone, Debug)]
pub(super) enum VarValue {
    Ty(Ty),
    Eff(EffectRow),
    Row(Row),
    Perm(Perm),
}

#[derive(Clone, Debug)]
pub(super) struct VarInfo {
    pub(super) parent: u32,
    pub(super) value: Option<VarValue>,
    pub(super) level: Level,
    /// Where the variable was introduced. Read by finalization diagnostics
    /// ("cannot infer, add an annotation") so errors blame the variable's
    /// origin.
    #[allow(dead_code)]
    origin: NodeID,
}

/// Union-find over all three variable kinds (type, effect-row, record-row).
#[derive(Default, Debug)]
pub struct VarStore {
    pub(super) vars: Vec<VarInfo>,
    /// Bumped on every bind/union; the solver's progress detector.
    generation: u64,
}

impl VarStore {
    pub(super) fn fresh(&mut self, level: Level, origin: NodeID) -> u32 {
        let id = self.vars.len() as u32;
        self.vars.push(VarInfo {
            parent: id,
            value: None,
            level,
            origin,
        });
        id
    }

    pub fn fresh_ty(&mut self, level: Level, origin: NodeID) -> TyVar {
        TyVar(self.fresh(level, origin))
    }

    pub fn fresh_eff(&mut self, level: Level, origin: NodeID) -> EffVar {
        EffVar(self.fresh(level, origin))
    }

    pub fn fresh_row(&mut self, level: Level, origin: NodeID) -> RowVar {
        RowVar(self.fresh(level, origin))
    }

    pub fn fresh_perm(&mut self, level: Level, origin: NodeID) -> PermVar {
        PermVar(self.fresh(level, origin))
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    /// Find with path compression (Tarjan's union-find).
    pub fn find(&mut self, var: u32) -> u32 {
        let parent = self.vars[var as usize].parent;
        if parent == var {
            return var;
        }
        let root = self.find(parent);
        self.vars[var as usize].parent = root;
        root
    }

    pub fn level(&mut self, var: u32) -> Level {
        let root = self.find(var);
        self.vars[root as usize].level
    }

    pub(super) fn set_level(&mut self, var: u32, level: Level) {
        let root = self.find(var);
        self.vars[root as usize].level = level;
    }

    pub(super) fn value(&mut self, var: u32) -> Option<VarValue> {
        let root = self.find(var);
        self.vars[root as usize].value.clone()
    }

    pub(crate) fn origin(&mut self, var: u32) -> NodeID {
        let root = self.find(var);
        self.vars[root as usize].origin
    }

    pub(super) fn bind(&mut self, var: u32, value: VarValue) {
        let root = self.find(var);
        debug_assert!(self.vars[root as usize].value.is_none());
        self.vars[root as usize].value = Some(value);
        self.generation += 1;
    }

    /// Union two unsolved roots, keeping the outermost (smallest) level.
    pub(super) fn union(&mut self, a: u32, b: u32) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        let level = self.vars[ra as usize]
            .level
            .min(self.vars[rb as usize].level);
        self.vars[rb as usize].parent = ra;
        self.vars[ra as usize].level = level;
        self.generation += 1;
    }

    /// Resolve the head of a type: follow solved variables until we reach a
    /// non-variable constructor or an unsolved root.
    pub fn shallow(&mut self, ty: &Ty) -> Ty {
        let mut current = ty.clone();
        loop {
            match current {
                Ty::Var(v) => match self.value(v.0) {
                    Some(VarValue::Ty(inner)) => current = inner,
                    Some(_) => unreachable!("type var bound to non-type value"),
                    None => return Ty::Var(TyVar(self.find(v.0))),
                },
                other => return other,
            }
        }
    }

    /// Resolve a borrow permission: follow solved perm variables until a
    /// concrete permission, a rigid param, or an unsolved root.
    pub fn shallow_perm(&mut self, perm: Perm) -> Perm {
        let mut current = perm;
        loop {
            match current {
                Perm::Var(v) => match self.value(v.0) {
                    Some(VarValue::Perm(inner)) => current = inner,
                    Some(_) => unreachable!("perm var bound to non-perm value"),
                    None => return Perm::Var(PermVar(self.find(v.0))),
                },
                other => return other,
            }
        }
    }

    /// Fully substitute solved variables, flattening row tails. The structural
    /// recursion is `TyFold`; only the leaves are store-aware (see the impl
    /// below).
    pub fn zonk_ty(&mut self, ty: &Ty) -> Ty {
        self.fold_ty(ty)
    }

    /// Bind every unsolved permission variable in `ty` to `Shared` and return
    /// the resolved type. The defaulting rule: a borrow whose permission was
    /// never forced exclusive is a read-only borrow. Runs at finalization,
    /// after all solving, so the binding is safe and every sharer of the
    /// variable sees the same default.
    pub fn default_unsolved_perms(&mut self, ty: &Ty) -> Ty {
        PermDefaulter { store: self }.fold_ty(ty)
    }

    pub fn zonk_eff(&mut self, eff: &EffectRow) -> EffectRow {
        let (effects, tail) = self.flatten_eff(eff);
        let effects = effects
            .into_iter()
            .map(|entry| EffectEntry {
                effect: entry.effect,
                args: entry.args.iter().map(|ty| self.zonk_ty(ty)).collect(),
            })
            .collect();
        let tail = match tail {
            FlatTail::None => None,
            FlatTail::Var(v) => Some(EffTail::Var(EffVar(v))),
            FlatTail::Param(sym) => Some(EffTail::Param(sym)),
        };
        EffectRow::new(effects, tail)
    }

    pub fn zonk_row(&mut self, row: &Row) -> Row {
        let (fields, tail) = self.flatten_row(row);
        let fields = fields
            .into_iter()
            .map(|(l, t)| (l, self.zonk_ty(&t)))
            .collect();
        let tail = match tail {
            FlatTail::None => None,
            FlatTail::Var(v) => Some(RowTail::Var(RowVar(v))),
            FlatTail::Param(sym) => Some(RowTail::Param(sym)),
        };
        Row { fields, tail }
    }

    /// Collapse an effect row to (label set, final tail), following solved
    /// tail variables.
    pub(super) fn flatten_eff(&mut self, eff: &EffectRow) -> (Vec<EffectEntry>, FlatTail) {
        let mut effects = eff.effects.clone();
        let mut tail = eff.tail.clone();
        loop {
            match tail {
                None => return (effects, FlatTail::None),
                Some(EffTail::Param(sym)) => return (effects, FlatTail::Param(sym)),
                Some(EffTail::Var(v)) => match self.value(v.0) {
                    Some(VarValue::Eff(inner)) => {
                        effects.extend(inner.effects.iter().cloned());
                        tail = inner.tail;
                    }
                    Some(_) => unreachable!("effect var bound to non-effect value"),
                    None => return (effects, FlatTail::Var(self.find(v.0))),
                },
            }
        }
    }

    /// Collapse a record row to (fields, final tail), following solved tails.
    pub(super) fn flatten_row(&mut self, row: &Row) -> (Vec<(Label, Ty)>, FlatTail) {
        let mut fields = row.fields.clone();
        let mut tail = row.tail.clone();
        loop {
            match tail {
                None => break (sorted(fields), FlatTail::None),
                Some(RowTail::Param(sym)) => break (sorted(fields), FlatTail::Param(sym)),
                Some(RowTail::Var(v)) => match self.value(v.0) {
                    Some(VarValue::Row(inner)) => {
                        fields.extend(inner.fields.iter().cloned());
                        tail = inner.tail;
                    }
                    Some(_) => unreachable!("row var bound to non-row value"),
                    None => break (sorted(fields), FlatTail::Var(self.find(v.0))),
                },
            }
        }
    }

    /// Store-aware preorder query (the read-only dual of zonk's `TyFold`):
    /// resolve each node through `shallow` so solved variables are followed,
    /// and — unlike `Ty::try_visit` — also surface row/effect *tails* (both
    /// `Var` and `Param`), since the escape/resolution walks differ on which
    /// tails count. Tail *variables* are surfaced but not followed. `f` returns
    /// `Break` to short-circuit.
    pub(crate) fn query_resolved<B>(
        &mut self,
        ty: &Ty,
        f: &mut impl FnMut(&mut Self, TyNode<'_>) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        let resolved = self.shallow(ty);
        f(self, TyNode::Ty(&resolved))?;
        match &resolved {
            Ty::Nominal(_, args) | Ty::Tuple(args) => {
                for arg in args {
                    self.query_resolved(arg, f)?;
                }
            }
            Ty::Borrow(_, inner) => self.query_resolved(inner, f)?,
            Ty::Unique(inner) => self.query_resolved(inner, f)?,
            Ty::Func(params, ret, eff) => {
                for param in params {
                    self.query_resolved(param, f)?;
                }
                self.query_resolved(ret, f)?;
                if let Some(tail) = &eff.tail {
                    f(self, TyNode::EffTail(tail))?;
                }
            }
            Ty::Record(row) => {
                for (_, field) in &row.fields {
                    self.query_resolved(field, f)?;
                }
                if let Some(tail) = &row.tail {
                    f(self, TyNode::RowTail(tail))?;
                }
            }
            Ty::Any { assoc, .. } => {
                for (_, ty) in assoc {
                    self.query_resolved(ty, f)?;
                }
            }
            Ty::Proj(base, ..) => self.query_resolved(base, f)?,
            Ty::Var(_) | Ty::Param(_) | Ty::Error => {}
        }
        ControlFlow::Continue(())
    }

    /// Render a type for diagnostics, zonking first.
    pub fn render(&mut self, ty: &Ty) -> String {
        self.zonk_ty(ty).render_mono()
    }

    pub fn render_eff(&mut self, eff: &EffectRow) -> String {
        let (effects, tail) = self.flatten_eff(eff);
        let mut labels: Vec<String> = effects
            .iter()
            .map(|entry| {
                let zonked = EffectEntry {
                    effect: entry.effect,
                    args: entry.args.iter().map(|ty| self.zonk_ty(ty)).collect(),
                };
                crate::types::ty::render_entry(&zonked, &Default::default())
            })
            .collect();
        if !matches!(tail, FlatTail::None) {
            labels.push("..".into());
        }
        format!("<{}>", labels.join(", "))
    }
}

/// Zonking is the store-aware `TyFold`: a variable resolves through the union-
/// find (`shallow`) and its binding is folded in turn; effect/row tails flatten
/// through solved tail variables. The structural arms come from the trait.
impl TyFold for VarStore {
    fn fold_var(&mut self, var: TyVar) -> Ty {
        match self.shallow(&Ty::Var(var)) {
            Ty::Var(root) => Ty::Var(root),
            resolved => self.fold_ty(&resolved),
        }
    }

    fn fold_perm(&mut self, perm: Perm) -> Perm {
        self.shallow_perm(perm)
    }

    fn fold_eff(&mut self, eff: &EffectRow) -> EffectRow {
        self.zonk_eff(eff)
    }

    fn fold_row(&mut self, row: &Row) -> Row {
        self.zonk_row(row)
    }
}

/// Zonk that additionally binds unsolved permission variables to `Shared`
/// (see [`VarStore::default_unsolved_perms`]).
struct PermDefaulter<'s> {
    store: &'s mut VarStore,
}

impl TyFold for PermDefaulter<'_> {
    fn fold_var(&mut self, var: TyVar) -> Ty {
        match self.store.shallow(&Ty::Var(var)) {
            Ty::Var(root) => Ty::Var(root),
            resolved => self.fold_ty(&resolved),
        }
    }

    fn fold_perm(&mut self, perm: Perm) -> Perm {
        match self.store.shallow_perm(perm) {
            Perm::Var(v) => {
                self.store.bind(v.0, VarValue::Perm(Perm::Shared));
                Perm::Shared
            }
            other => other,
        }
    }

    fn fold_eff(&mut self, eff: &EffectRow) -> EffectRow {
        let zonked = self.store.zonk_eff(eff);
        EffectRow::new(
            zonked
                .effects
                .iter()
                .map(|entry| EffectEntry {
                    effect: entry.effect,
                    args: entry.args.iter().map(|ty| self.fold_ty(ty)).collect(),
                })
                .collect(),
            zonked.tail,
        )
    }

    fn fold_row(&mut self, row: &Row) -> Row {
        let zonked = self.store.zonk_row(row);
        Row {
            fields: zonked
                .fields
                .iter()
                .map(|(label, ty)| (label.clone(), self.fold_ty(ty)))
                .collect(),
            tail: zonked.tail,
        }
    }
}

pub(super) fn sorted(mut fields: Vec<(Label, Ty)>) -> Vec<(Label, Ty)> {
    fields.sort_by(|(a, _), (b, _)| a.cmp(b));
    fields
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum FlatTail {
    None,
    Var(u32),
    Param(Symbol),
}

/// A node yielded by [`VarStore::query_resolved`]: a resolved type, or a row /
/// effect tail (surfaced raw so each query applies its own tail policy).
pub(crate) enum TyNode<'a> {
    Ty(&'a Ty),
    RowTail(&'a RowTail),
    EffTail(&'a EffTail),
}
