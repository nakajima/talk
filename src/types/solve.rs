//! The constraint solver: one entry point, called once per binding group
//! (OutsideIn(X), Vytiniotis, Peyton Jones, Schrijvers & Sulzmann, JFP 2011 —
//! the simplifier of §7, instantiated for Talk's theory X = equalities over
//! types-with-rows, protocol conformance, and HasMember predicates).
//!
//! - Equalities solve by Robinson unification (JACM 1965) over a union-find
//!   `VarStore` with path compression.
//! - Variable levels follow Rémy (INRIA RR-1766, 1992): generalization
//!   quantifies exactly the variables deeper than the binding group's level,
//!   and binding a variable adjusts inner levels outward. The same levels
//!   will enforce implication untouchability in milestone 8 (OutsideIn §5,
//!   as in GHC's TcLevel).
//! - Record rows unify by decomposition in the scoped-labels style (Leijen,
//!   *Extensible Records with Scoped Labels*, TFP 2005). Effect rows are the
//!   same algorithm over a label set (Leijen, *Koka: Programming with
//!   Row-Polymorphic Effect Types*, MSR-TR-2013-79).
//!   There is no published OutsideIn(X)-with-rows; the composition is ours,
//!   but row equalities canonicalize into smaller constraints exactly like
//!   constructor decomposition, which is the property the framework needs.
//! - `Conforms` is a class constraint (Wadler & Blott, POPL 1989) solved by
//!   conformance-table lookup. Associated-type bindings are not carried on
//!   `Conforms`; they are ordinary projections that reduce through the
//!   conformance row (Chakravarty, Keller & Peyton Jones, ICFP 2005).
//! - `HasMember` is a Has predicate (Gaster & Jones, TR NOTTCS-TR-96-3,
//!   1996). A stuck predicate set is retried while unification makes
//!   progress; at quiescence the unique-owner *improvement* rule applies
//!   (Jones, *Simplifying and Improving Qualified Types*, FPCA 1995):
//!   improvement is a substitution justified by uniqueness — multiple owners
//!   mean an error, never a guess.
//! - `Never` is NOT special here: bottom applies only at joins, which the
//!   generator handles (Pierce & Turner, TOPLAS 2000 joins).
//!
//! Constraints live for one binding group: `solve` consumes them and returns
//! residual variable-headed predicates, which generalization turns into a
//! scheme's qualified context (THIH section 11.6's split between deferred and
//! retained predicates). Nothing is stored.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::label::Label;
use crate::name_resolution::scc_graph::Level;
use crate::name_resolution::symbol::{Symbol, Symbols};
use crate::node_id::NodeID;
use crate::types::catalog::{MemberOwner, Requirement, TypeCatalog};
use crate::types::constraint::{Constraint, CtOrigin, CtReason};
use crate::types::error::TypeError;
use crate::types::output::MemberResolution;
use crate::types::ty::{
    EffTail, EffVar, EffectRow, Predicate, Row, RowTail, RowVar, Scheme, SchemeParam, Ty, TyVar,
};

#[derive(Clone, Debug)]
enum VarValue {
    Ty(Ty),
    Eff(EffectRow),
    Row(Row),
}

#[derive(Clone, Debug)]
struct VarInfo {
    parent: u32,
    value: Option<VarValue>,
    level: Level,
    /// Where the variable was introduced. Read by milestone 4's
    /// finalization pass ("cannot infer, add an annotation" diagnostics
    /// blame the variable's origin, per the approved plan's Phase 3).
    #[allow(dead_code)]
    origin: NodeID,
}

/// Union-find over all three variable kinds (type, effect-row, record-row).
#[derive(Default, Debug)]
pub struct VarStore {
    vars: Vec<VarInfo>,
    /// Bumped on every bind/union; the solver's progress detector.
    generation: u64,
}

impl VarStore {
    fn fresh(&mut self, level: Level, origin: NodeID) -> u32 {
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

    fn set_level(&mut self, var: u32, level: Level) {
        let root = self.find(var);
        self.vars[root as usize].level = level;
    }

    fn value(&mut self, var: u32) -> Option<VarValue> {
        let root = self.find(var);
        self.vars[root as usize].value.clone()
    }

    fn bind(&mut self, var: u32, value: VarValue) {
        let root = self.find(var);
        debug_assert!(self.vars[root as usize].value.is_none());
        self.vars[root as usize].value = Some(value);
        self.generation += 1;
    }

    /// Union two unsolved roots, keeping the outermost (smallest) level.
    fn union(&mut self, a: u32, b: u32) {
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

    /// Fully substitute solved variables, flattening row tails.
    pub fn zonk_ty(&mut self, ty: &Ty) -> Ty {
        match self.shallow(ty) {
            Ty::Var(v) => Ty::Var(v),
            Ty::Param(sym) => Ty::Param(sym),
            Ty::Nominal(sym, args) => {
                Ty::Nominal(sym, args.iter().map(|a| self.zonk_ty(a)).collect())
            }
            Ty::Func(params, ret, eff) => Ty::Func(
                params.iter().map(|p| self.zonk_ty(p)).collect(),
                Box::new(self.zonk_ty(&ret)),
                self.zonk_eff(&eff),
            ),
            Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| self.zonk_ty(i)).collect()),
            Ty::Record(row) => Ty::Record(self.zonk_row(&row)),
            Ty::Proj(base, protocol, assoc) => {
                Ty::Proj(Box::new(self.zonk_ty(&base)), protocol, assoc)
            }
            Ty::Error => Ty::Error,
        }
    }

    pub fn zonk_eff(&mut self, eff: &EffectRow) -> EffectRow {
        let (effects, tail) = self.flatten_eff(eff);
        let tail = match tail {
            FlatTail::None => None,
            FlatTail::Var(v) => Some(EffTail::Var(EffVar(v))),
            FlatTail::Param(sym) => Some(EffTail::Param(sym)),
        };
        EffectRow { effects, tail }
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
    fn flatten_eff(&mut self, eff: &EffectRow) -> (BTreeSet<Symbol>, FlatTail) {
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
    fn flatten_row(&mut self, row: &Row) -> (Vec<(Label, Ty)>, FlatTail) {
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

    /// Render a type for diagnostics, zonking first.
    pub fn render(&mut self, ty: &Ty) -> String {
        self.zonk_ty(ty).render_mono()
    }

    pub fn render_eff(&mut self, eff: &EffectRow) -> String {
        let (effects, tail) = self.flatten_eff(eff);
        let mut labels: Vec<String> = effects.iter().map(|sym| format!("'{sym}")).collect();
        if !matches!(tail, FlatTail::None) {
            labels.push("..".into());
        }
        format!("<{}>", labels.join(", "))
    }
}

fn sorted(mut fields: Vec<(Label, Ty)>) -> Vec<(Label, Ty)> {
    fields.sort_by(|(a, _), (b, _)| a.cmp(b));
    fields
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum FlatTail {
    None,
    Var(u32),
    Param(Symbol),
}

/// Normalize the head of a type: reduce an associated-type projection
/// through the conformance table when its base's head is concrete
/// (type-family top-level reaction, OutsideIn(X) JFP 2011 §7; instance
/// reduction per Chakravarty et al., ICFP 2005). Irreducible projections
/// (rigid base, or no binding) come back as `Proj`.
pub fn normalize_ty(store: &mut VarStore, catalog: &TypeCatalog, ty: &Ty) -> Ty {
    match store.shallow(ty) {
        Ty::Proj(base, protocol, assoc) => {
            let base = normalize_ty(store, catalog, &base);
            if let Ty::Nominal(symbol, args) = &base
                && let Some(conformance) = catalog.conformances.get(&(*symbol, protocol))
                && let Some(binding) = conformance.assoc.get(&assoc)
            {
                let binding = binding.clone();
                let self_args = conformance.self_args.clone();
                let mut substitution = FxHashMap::default();
                for (pattern, actual) in self_args.iter().zip(args) {
                    bind_param_pattern(pattern, actual, &mut substitution);
                }
                let reduced =
                    binding.substitute(&substitution, &Default::default(), &Default::default());
                return normalize_ty(store, catalog, &reduced);
            }
            Ty::Proj(Box::new(base), protocol, assoc)
        }
        other => other,
    }
}

/// A projection whose base is still a unification variable cannot react yet
/// (the FLATTEN-style wait in OutsideIn's canonicalization): defer it.
fn stuck_projection(store: &mut VarStore, ty: &Ty) -> bool {
    match ty {
        Ty::Proj(base, _, _) => {
            let base = store.shallow(base);
            matches!(base, Ty::Var(_)) || stuck_projection(store, &base)
        }
        _ => false,
    }
}

/// The per-binding-group solver. Borrows the checker's tables; owns nothing.
/// Dropped (with any leftover state) when the group is done.
pub struct Solver<'s> {
    pub store: &'s mut VarStore,
    pub errors: &'s mut Vec<(TypeError, NodeID)>,
    pub catalog: &'s TypeCatalog,
    pub schemes: &'s FxHashMap<Symbol, Scheme>,
    pub mono: &'s FxHashMap<Symbol, Ty>,
    pub instantiations: &'s mut FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    pub member_resolutions: &'s mut FxHashMap<NodeID, MemberResolution>,
    pub level: Level,
    /// True only in the final solve: committing a member constraint to its
    /// single nominal owner is defaulting, sound only once no later group
    /// can constrain the receiver further. Group solves hold such
    /// constraints instead, so they ride the binder's scheme (qualified
    /// types — Jones, *Qualified Types*, 1994).
    pub defaulting: bool,
    /// Local assumptions from declaration `where` clauses and future GADT
    /// match refinements. They are erased evidence: used only to discharge
    /// wanteds while solving this implication.
    pub givens: Vec<Predicate>,
    /// In-flight auto-derived conformances, so recursive nominals resolve
    /// coinductively instead of looping.
    pub derived_seen: rustc_hash::FxHashSet<(Symbol, Symbol)>,
}

impl<'s> Solver<'s> {
    /// Solve to quiescence: run the worklist, retry stuck predicates while
    /// unification makes progress, then improve (unique-owner), then stop.
    /// Returns the residual variable-headed `Conforms` constraints for
    /// generalization; everything else unresolved becomes an error.
    pub fn solve(&mut self, wanteds: Vec<Constraint>) -> Vec<Constraint> {
        let mut queue = wanteds;
        let mut stuck: Vec<Constraint> = vec![];
        loop {
            let generation = self.store.generation();
            while let Some(constraint) = queue.pop() {
                match constraint {
                    Constraint::Eq(a, b, origin) => {
                        let a = normalize_ty(self.store, self.catalog, &a);
                        let b = normalize_ty(self.store, self.catalog, &b);
                        let a = self.rewrite_ty_from_givens(a);
                        let b = self.rewrite_ty_from_givens(b);
                        if a == b {
                            continue;
                        }
                        if stuck_projection(self.store, &a) || stuck_projection(self.store, &b) {
                            stuck.push(Constraint::Eq(a, b, origin));
                        } else {
                            self.unify(&a, &b, origin, &mut queue);
                        }
                    }
                    Constraint::EffEq(a, b, origin) => self.unify_eff(&a, &b, origin),
                    Constraint::Conforms {
                        ty,
                        protocol,
                        origin,
                    } => {
                        if let Some(unsolved) =
                            self.try_conforms(ty, protocol, origin, &mut queue)
                        {
                            stuck.push(unsolved);
                        }
                    }
                    Constraint::HasMember {
                        receiver,
                        label,
                        member,
                        origin,
                    } => {
                        if let Some(unsolved) =
                            self.try_member(receiver, label, member, origin, &mut queue)
                        {
                            stuck.push(unsolved);
                        }
                    }
                    Constraint::Implic(implication) => {
                        if implication.givens.is_empty() {
                            queue.extend(implication.wanteds);
                        } else {
                            let original_given_len = self.givens.len();
                            self.givens.extend(implication.givens);
                            let residual = self.solve(implication.wanteds);
                            self.givens.truncate(original_given_len);
                            stuck.extend(residual);
                        }
                    }
                }
            }
            if stuck.is_empty() {
                return vec![];
            }
            if self.store.generation() != generation {
                queue = std::mem::take(&mut stuck);
                continue;
            }
            if self.improve(&mut stuck, &mut queue) {
                queue.extend(std::mem::take(&mut stuck));
                continue;
            }
            break;
        }

        let mut residual = vec![];
        for constraint in stuck {
            match constraint {
                Constraint::Conforms {
                    ty,
                    protocol,
                    origin,
                } => {
                    if matches!(self.store.shallow(&ty), Ty::Var(_)) {
                        residual.push(Constraint::Conforms {
                            ty,
                            protocol,
                            origin,
                        });
                    } else {
                        let rendered = self.store.render(&ty);
                        self.errors.push((
                            TypeError::NotConforming {
                                ty: rendered,
                                protocol: protocol.to_string(),
                            },
                            origin.node,
                        ));
                    }
                }
                Constraint::Eq(a, b, origin) => {
                    // A projection whose base never resolved in this group
                    // may still resolve once a later group solves the base
                    // (the same floating as Conforms residuals).
                    residual.push(Constraint::Eq(a, b, origin));
                }
                Constraint::HasMember {
                    receiver,
                    label,
                    member,
                    origin,
                } => {
                    // Stuck member constraints float to the final solve: a
                    // variable head may be solved by a later group, and a
                    // concrete head only ends up here when the member's own
                    // signature is still a variable (its group has not run
                    // yet) — a genuinely unknown member errors inside
                    // try_member directly.
                    residual.push(Constraint::HasMember {
                        receiver,
                        label,
                        member,
                        origin,
                    });
                }
                _ => {}
            }
        }
        residual
    }

    fn rewrite_ty_from_givens(&mut self, ty: Ty) -> Ty {
        let mut seen = FxHashSet::default();
        self.rewrite_ty_from_givens_inner(ty, &mut seen)
    }

    fn rewrite_ty_from_givens_inner(&mut self, ty: Ty, seen: &mut FxHashSet<Ty>) -> Ty {
        let ty = normalize_ty(self.store, self.catalog, &ty);
        if !seen.insert(ty.clone()) {
            return ty;
        }
        let rebuilt = match ty {
            Ty::Nominal(symbol, args) => Ty::Nominal(
                symbol,
                args.into_iter()
                    .map(|arg| {
                        let mut seen = seen.clone();
                        self.rewrite_ty_from_givens_inner(arg, &mut seen)
                    })
                    .collect(),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .into_iter()
                    .map(|item| {
                        let mut seen = seen.clone();
                        self.rewrite_ty_from_givens_inner(item, &mut seen)
                    })
                    .collect(),
            ),
            Ty::Func(params, ret, eff) => Ty::Func(
                params
                    .into_iter()
                    .map(|param| {
                        let mut seen = seen.clone();
                        self.rewrite_ty_from_givens_inner(param, &mut seen)
                    })
                    .collect(),
                Box::new({
                    let mut seen = seen.clone();
                    self.rewrite_ty_from_givens_inner(*ret, &mut seen)
                }),
                eff,
            ),
            Ty::Record(row) => Ty::Record(Row {
                fields: row
                    .fields
                    .into_iter()
                    .map(|(label, field)| {
                        let mut seen = seen.clone();
                        (label, self.rewrite_ty_from_givens_inner(field, &mut seen))
                    })
                    .collect(),
                tail: row.tail,
            }),
            Ty::Proj(base, protocol, assoc) => {
                let base = self.rewrite_ty_from_givens_inner(*base, seen);
                normalize_ty(
                    self.store,
                    self.catalog,
                    &Ty::Proj(Box::new(base), protocol, assoc),
                )
            }
            other => other,
        };

        for given in self.givens.clone() {
            let Predicate::TypeEq(lhs, rhs) = given else {
                continue;
            };
            let lhs = normalize_ty(self.store, self.catalog, &lhs);
            let rhs = normalize_ty(self.store, self.catalog, &rhs);
            let (from, to) = Self::oriented_given_rewrite(lhs, rhs);
            if rebuilt == from {
                return self.rewrite_ty_from_givens_inner(to, seen);
            }
        }
        rebuilt
    }

    fn oriented_given_rewrite(lhs: Ty, rhs: Ty) -> (Ty, Ty) {
        if Self::rewrite_specificity(&lhs) <= Self::rewrite_specificity(&rhs) {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        }
    }

    fn rewrite_specificity(ty: &Ty) -> u8 {
        match ty {
            Ty::Var(_) | Ty::Param(_) => 0,
            Ty::Proj(..) => 1,
            Ty::Func(..) | Ty::Record(_) | Ty::Tuple(_) => 2,
            Ty::Nominal(..) => 3,
            Ty::Error => 4,
        }
    }

    fn given_conformance_satisfies(&mut self, ty: &Ty, protocol: Symbol) -> bool {
        for given in self.givens.clone() {
            let Predicate::Conforms {
                ty: given_ty,
                protocol: given_protocol,
            } = given
            else {
                continue;
            };
            let given_ty = normalize_ty(self.store, self.catalog, &given_ty);
            let given_ty = self.rewrite_ty_from_givens(given_ty);
            if &given_ty == ty && self.catalog.bounds_satisfy(&[given_protocol], protocol) {
                return true;
            }
        }
        false
    }

    /// One step on a Conforms constraint: discharge against the conformance
    /// table (OutsideIn's class-constraint reaction; instance contexts will
    /// emit further wanteds when conditional conformance lands).
    fn try_conforms(
        &mut self,
        ty: Ty,
        protocol: Symbol,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> Option<Constraint> {
        let normalized = normalize_ty(self.store, self.catalog, &ty);
        let normalized = self.rewrite_ty_from_givens(normalized);
        if self.given_conformance_satisfies(&normalized, protocol) {
            return None;
        }
        match normalized.clone() {
            Ty::Var(_) => Some(Constraint::Conforms {
                ty,
                protocol,
                origin,
            }),
            Ty::Error => None,
            Ty::Param(param) => {
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&param)
                    .cloned()
                    .unwrap_or_default();
                if self.catalog.bounds_satisfy(&bounds, protocol) {
                    None
                } else {
                    let rendered = self.store.render(&ty);
                    self.errors.push((
                        TypeError::NotConforming {
                            ty: rendered,
                            protocol: protocol.to_string(),
                        },
                        origin.node,
                    ));
                    None
                }
            }
            // An irreducible projection conforms through the bounds declared
            // on the associated type (`associated T: Iterator`).
            Ty::Proj(base, _, assoc_symbol) => {
                if matches!(self.store.shallow(&base), Ty::Var(_)) {
                    return Some(Constraint::Conforms {
                        ty,
                        protocol,
                        origin,
                    });
                }
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&assoc_symbol)
                    .cloned()
                    .unwrap_or_default();
                if self.catalog.bounds_satisfy(&bounds, protocol) {
                    None
                } else {
                    let rendered = self.store.render(&ty);
                    self.errors.push((
                        TypeError::NotConforming {
                            ty: rendered,
                            protocol: protocol.to_string(),
                        },
                        origin.node,
                    ));
                    None
                }
            }
            Ty::Nominal(symbol, args) => {
                match self.catalog.conformances.get(&(symbol, protocol)) {
                    Some(conformance) => {
                        let conformance = conformance.clone();
                        // Bind the row's rigid params against the actual
                        // head arguments, then discharge the instance
                        // context as new wanteds (Hall/Hammond/Peyton
                        // Jones/Wadler, *Type Classes in Haskell*).
                        // Associated types are ordinary projections
                        // normalized by `normalize_ty` (Chakravarty/Keller/
                        // Peyton Jones, *Associated Type Synonyms*).
                        let mut substitution: FxHashMap<Symbol, Ty> = FxHashMap::default();
                        for (pattern, actual) in conformance.self_args.iter().zip(&args) {
                            bind_param_pattern(pattern, actual, &mut substitution);
                        }
                        for predicate in &conformance.context {
                            queue.push(
                                predicate
                                    .substitute(&substitution, &Default::default(), &Default::default())
                                    .into_constraint(origin),
                            );
                        }
                        None
                    }
                    None => {
                        if self.try_derive(symbol, &args, protocol, origin, queue) {
                            return None;
                        }
                        let rendered = self.store.render(&ty);
                        self.errors.push((
                            TypeError::NotConforming {
                                ty: rendered,
                                protocol: protocol.to_string(),
                            },
                            origin.node,
                        ));
                        None
                    }
                }
            }
            other => {
                let rendered = self.store.render(&other);
                self.errors.push((
                    TypeError::NotConforming {
                        ty: rendered,
                        protocol: protocol.to_string(),
                    },
                    origin.node,
                ));
                None
            }
        }
    }

    /// Auto-derived conformance (today: Showable) for structs and enums
    /// without an explicit row. The derived instance's context is
    /// structural — every field/payload conforms — checked coinductively so
    /// recursive nominals terminate.
    fn try_derive(
        &mut self,
        symbol: Symbol,
        args: &[Ty],
        protocol: Symbol,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        if !self.catalog.derivable.contains(&protocol) {
            return false;
        }
        if !self.derived_seen.insert((symbol, protocol)) {
            return true;
        }
        if let Some(info) = self.catalog.structs.get(&symbol) {
            let substitution: FxHashMap<Symbol, Ty> = info
                .params
                .iter()
                .copied()
                .zip(args.iter().cloned())
                .collect();
            for (_, (_, field_ty)) in &info.fields {
                let field_ty =
                    field_ty.substitute(&substitution, &Default::default(), &Default::default());
                queue.push(Constraint::Conforms {
                    ty: field_ty,
                    protocol,
                    origin,
                });
            }
            return true;
        }
        if let Some(info) = self.catalog.enums.get(&symbol) {
            let substitution: FxHashMap<Symbol, Ty> = info
                .params
                .iter()
                .copied()
                .zip(args.iter().cloned())
                .collect();
            for variant in info.variants.values() {
                for payload in &variant.payloads {
                    let payload =
                        payload.substitute(&substitution, &Default::default(), &Default::default());
                    queue.push(Constraint::Conforms {
                        ty: payload,
                        protocol,
                        origin,
                    });
                }
            }
            return true;
        }
        false
    }

    /// One step on a HasMember predicate against a known head.
    /// Dispatch a member use through the protocols that could provide it.
    /// Returns true when handled: exactly one distinct requirement binds
    /// (instances with contexts — Hall et al., TOPLAS 1996); several emit
    /// an ambiguity error naming the protocol-static forms (`P.m(x)`)
    /// that pick one, since committing to any would make meaning depend
    /// on table order (overlapping instances — Jones, *Qualified Types*,
    /// 1994, §2.4). Zero candidates fall through to the caller.
    #[allow(clippy::too_many_arguments)]
    fn dispatch_member_through(
        &mut self,
        protocols: &[Symbol],
        head: Option<Symbol>,
        receiver: &Ty,
        label: &str,
        member: &Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        let mut candidates: Vec<(Symbol, Symbol, Requirement)> = vec![];
        for &protocol in protocols {
            let Some((owner, requirement)) = self.catalog.requirement_in(protocol, label) else {
                continue;
            };
            // Two protocols inheriting one base share its requirement —
            // that is one candidate, not an ambiguity.
            if candidates
                .iter()
                .any(|(_, _, r)| r.symbol == requirement.symbol)
            {
                continue;
            }
            candidates.push((protocol, owner, requirement.clone()));
        }
        match candidates.as_slice() {
            [] => false,
            [(protocol, owner, requirement)] => {
                let witness = head
                    .and_then(|h| self.catalog.conformances.get(&(h, *protocol)))
                    .and_then(|c| c.witnesses.get(label))
                    .copied()
                    .unwrap_or(requirement.symbol);
                self.bind_requirement(
                    *owner,
                    requirement,
                    receiver,
                    member,
                    origin,
                    queue,
                    witness,
                );
                true
            }
            many => {
                let rendered = self.store.render(receiver);
                self.errors.push((
                    TypeError::AmbiguousMember {
                        receiver: rendered,
                        label: label.to_string(),
                        candidates: many.iter().map(|(p, ..)| p.to_string()).collect(),
                    },
                    origin.node,
                ));
                true
            }
        }
    }

    fn try_member(
        &mut self,
        receiver: Ty,
        label: Label,
        member: Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> Option<Constraint> {
        let label_str = label.to_string();
        let normalized = normalize_ty(self.store, self.catalog, &receiver);
        let normalized = self.rewrite_ty_from_givens(normalized);
        if stuck_projection(self.store, &normalized) {
            return Some(Constraint::HasMember {
                receiver,
                label,
                member,
                origin,
            });
        }
        match normalized {
            Ty::Var(_) => Some(Constraint::HasMember {
                receiver,
                label,
                member,
                origin,
            }),
            Ty::Error => None,
            // Members of an irreducible projection dispatch through the
            // bounds declared on the associated type.
            Ty::Proj(_, _, assoc_symbol) => {
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&assoc_symbol)
                    .cloned()
                    .unwrap_or_default();
                if self.dispatch_member_through(
                    &bounds, None, &receiver, &label_str, &member, origin, queue,
                ) {
                    return None;
                }
                let rendered = self.store.render(&receiver);
                self.errors.push((
                    TypeError::UnknownMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    origin.node,
                ));
                None
            }
            // Structural access via an open-row equality (Leijen 2005):
            // present fields hit; absent fields on a closed row are a row
            // mismatch.
            Ty::Record(_) => {
                let tail = self.store.fresh_row(self.level, origin.node);
                let probe = Ty::Record(Row {
                    fields: vec![(Label::Named(label_str), member)],
                    tail: Some(RowTail::Var(tail)),
                });
                queue.push(Constraint::Eq(receiver, probe, origin));
                None
            }
            Ty::Param(param) => {
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&param)
                    .cloned()
                    .unwrap_or_default();
                if self.dispatch_member_through(
                    &bounds, None, &receiver, &label_str, &member, origin, queue,
                ) {
                    return None;
                }
                let rendered = self.store.render(&receiver);
                self.errors.push((
                    TypeError::UnknownMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    origin.node,
                ));
                None
            }
            Ty::Nominal(symbol, args) => {
                if let Some(info) = self.catalog.structs.get(&symbol) {
                    let substitution: FxHashMap<Symbol, Ty> = info
                        .params
                        .iter()
                        .copied()
                        .zip(args.iter().cloned())
                        .collect();
                    if let Some((property, field_ty)) = info.fields.get(&label_str) {
                        let field_ty = field_ty.substitute(
                            &substitution,
                            &Default::default(),
                            &Default::default(),
                        );
                        queue.push(Constraint::Eq(member, field_ty, origin));
                        self.member_resolutions
                            .insert(origin.node, MemberResolution::Direct(*property));
                        return None;
                    }
                    if let Some(&method) = info.methods.get(&label_str) {
                        let signature = self.symbol_ty(method, origin.node, queue);
                        let signature = signature.substitute(
                            &substitution,
                            &Default::default(),
                            &Default::default(),
                        );
                        return match self.store.shallow(&signature) {
                            Ty::Func(params, ret, eff) if !params.is_empty() => {
                                queue.push(Constraint::Eq(
                                    params[0].clone(),
                                    receiver.clone(),
                                    origin,
                                ));
                                queue.push(Constraint::Eq(
                                    member,
                                    Ty::Func(params[1..].to_vec(), ret, eff),
                                    origin,
                                ));
                                self.member_resolutions
                                    .insert(origin.node, MemberResolution::Direct(method));
                                None
                            }
                            // Signature still being checked in this group:
                            // retry when it resolves.
                            Ty::Var(_) => Some(Constraint::HasMember {
                                receiver,
                                label,
                                member,
                                origin,
                            }),
                            _ => None,
                        };
                    }
                }
                // Methods on enums dispatch exactly like struct methods:
                // instantiate the (possibly generic) scheme, pin self,
                // and the member is the self-dropped signature.
                if let Some(info) = self.catalog.enums.get(&symbol)
                    && let Some(&method) = info.methods.get(&label_str)
                {
                    {
                        let substitution: FxHashMap<Symbol, Ty> = info
                            .params
                            .iter()
                            .copied()
                            .zip(args.iter().cloned())
                            .collect();
                        let signature = self.symbol_ty(method, origin.node, queue);
                        let signature = signature.substitute(
                            &substitution,
                            &Default::default(),
                            &Default::default(),
                        );
                        return match self.store.shallow(&signature) {
                            Ty::Func(params, ret, eff) if !params.is_empty() => {
                                queue.push(Constraint::Eq(
                                    params[0].clone(),
                                    receiver.clone(),
                                    origin,
                                ));
                                queue.push(Constraint::Eq(
                                    member,
                                    Ty::Func(params[1..].to_vec(), ret, eff),
                                    origin,
                                ));
                                self.member_resolutions
                                    .insert(origin.node, MemberResolution::Direct(method));
                                None
                            }
                            // Signature still being checked in this group:
                            // retry when it resolves.
                            Ty::Var(_) => Some(Constraint::HasMember {
                                receiver,
                                label,
                                member,
                                origin,
                            }),
                            _ => None,
                        };
                    }
                }
                // Members provided through conformances (extend witnesses):
                // type via the protocol requirement, which is always valid if
                // the conformance is (the witness is checked against the
                // requirement when the extend body is checked).
                if let Some(protocols) = self.catalog.conformances_by_head.get(&symbol) {
                    let protocols = protocols.clone();
                    if self.dispatch_member_through(
                        &protocols,
                        Some(symbol),
                        &receiver,
                        &label_str,
                        &member,
                        origin,
                        queue,
                    ) {
                        return None;
                    }
                }
                // Auto-derived protocol members (`optional.show()` without
                // an explicit conformance): dispatch through the requirement
                // when the head is a struct/enum and the protocol derives.
                let is_derivable_head = self.catalog.structs.contains_key(&symbol)
                    || self.catalog.enums.contains_key(&symbol);
                if is_derivable_head {
                    for protocol in self.catalog.derivable.clone() {
                        if let Some((owner, requirement)) =
                            self.catalog.requirement_in(protocol, &label_str)
                        {
                            let requirement = requirement.clone();
                            let witness = requirement.symbol;
                            self.bind_requirement(
                                owner,
                                &requirement,
                                &receiver,
                                &member,
                                origin,
                                queue,
                                witness,
                            );
                            return None;
                        }
                    }
                }
                // Inherent extend members (`extend Float { func _trunc() }`).
                if let Some(members) = self.catalog.extend_members.get(&symbol)
                    && let Some(inherent) = members.get(&label_str)
                {
                    let inherent = inherent.clone();
                    let mut substitution: FxHashMap<Symbol, Ty> = FxHashMap::default();
                    for (pattern, actual) in inherent.self_args.iter().zip(&args) {
                        bind_param_pattern(pattern, actual, &mut substitution);
                    }
                    let mut effs = FxHashMap::default();
                    effs.insert(
                        inherent.symbol,
                        EffTail::Var(self.store.fresh_eff(self.level, origin.node)),
                    );
                    let signature =
                        inherent
                            .sig
                            .substitute(&substitution, &effs, &Default::default());
                    if let Ty::Func(params, ret, eff) = signature
                        && !params.is_empty()
                    {
                        queue.push(Constraint::Eq(params[0].clone(), receiver.clone(), origin));
                        queue.push(Constraint::Eq(
                            member,
                            Ty::Func(params[1..].to_vec(), ret, eff),
                            origin,
                        ));
                        self.member_resolutions
                            .insert(origin.node, MemberResolution::Direct(inherent.symbol));
                    }
                    return None;
                }
                let rendered = self.store.render(&receiver);
                self.errors.push((
                    TypeError::UnknownMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    origin.node,
                ));
                None
            }
            other => {
                let rendered = self.store.render(&other);
                self.errors.push((
                    TypeError::UnknownMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    origin.node,
                ));
                None
            }
        }
    }

    /// Type a member through a protocol requirement: substitute Self and the
    /// associated types into the requirement's signature, bind self, and
    /// demand conformance. Associated types substitute as projections
    /// `recv.Assoc` and reduce through `normalize_ty` once the receiver is
    /// concrete. A protocol's own Self
    /// (default-body checking) gets the protocol's same-named associated param
    /// where one exists — a sub-protocol's redeclared `associated` refines its
    /// super's — and a Self-projection otherwise.
    #[allow(clippy::too_many_arguments)]
    fn bind_requirement(
        &mut self,
        protocol: Symbol,
        requirement: &Requirement,
        receiver: &Ty,
        member: &Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
        witness: Symbol,
    ) {
        let owner_assoc: Vec<(String, Symbol)> = self
            .catalog
            .protocols
            .get(&protocol)
            .map(|info| info.assoc.iter().map(|(n, s)| (n.clone(), *s)).collect())
            .unwrap_or_default();

        let receiver_head = self.store.shallow(receiver);
        let mut tys: FxHashMap<Symbol, Ty> = FxHashMap::default();
        match &receiver_head {
            Ty::Param(self_symbol @ Symbol::Protocol(_)) => {
                let receiver_assoc = self
                    .catalog
                    .protocols
                    .get(self_symbol)
                    .map(|info| info.assoc.clone())
                    .unwrap_or_default();
                for (name, owner_symbol) in &owner_assoc {
                    let substituted = receiver_assoc
                        .get(name)
                        .map(|refined| Ty::Param(*refined))
                        .unwrap_or_else(|| {
                            Ty::Proj(Box::new(receiver_head.clone()), protocol, *owner_symbol)
                        });
                    tys.insert(*owner_symbol, substituted);
                }
            }
            Ty::Param(_) | Ty::Proj(..) => {
                for (_, owner_symbol) in &owner_assoc {
                    tys.insert(
                        *owner_symbol,
                        Ty::Proj(Box::new(receiver_head.clone()), protocol, *owner_symbol),
                    );
                }
            }
            _ => {
                for (_, owner_symbol) in &owner_assoc {
                    tys.insert(
                        *owner_symbol,
                        Ty::Proj(Box::new(receiver.clone()), protocol, *owner_symbol),
                    );
                }
            }
        }
        tys.insert(protocol, receiver.clone());
        let mut effs = FxHashMap::default();
        effs.insert(
            requirement.symbol,
            EffTail::Var(self.store.fresh_eff(self.level, origin.node)),
        );
        let signature = requirement.sig.substitute(&tys, &effs, &Default::default());

        let mut local_wanteds = vec![];
        if let Ty::Func(params, ret, eff) = signature
            && !params.is_empty()
        {
            local_wanteds.push(Constraint::Eq(params[0].clone(), receiver.clone(), origin));
            local_wanteds.push(Constraint::Eq(
                member.clone(),
                Ty::Func(params[1..].to_vec(), ret, eff),
                origin,
            ));
        }
        let givens: Vec<Predicate> = requirement
            .predicates
            .iter()
            .map(|predicate| predicate.substitute(&tys, &effs, &Default::default()))
            .collect();
        if givens.is_empty() {
            queue.extend(local_wanteds);
        } else if !local_wanteds.is_empty() {
            queue.push(Constraint::Implic(Box::new(crate::types::constraint::Implication {
                level: self.level,
                givens,
                wanteds: local_wanteds,
            })));
        }
        queue.push(Constraint::Conforms {
            ty: receiver.clone(),
            protocol,
            origin,
        });
        self.member_resolutions.insert(
            origin.node,
            MemberResolution::ViaConformance { protocol, witness },
        );
    }

    /// The unique-owner improvement rule (Jones, FPCA 1995): a stuck
    /// HasMember whose label has exactly one owner determines its receiver —
    /// a protocol owner adds a bound, a nominal owner commits the variable.
    /// Ambiguity is an error, never a guess.
    fn improve(&mut self, stuck: &mut Vec<Constraint>, queue: &mut Vec<Constraint>) -> bool {
        let mut improved = false;
        let mut remaining = vec![];
        for constraint in stuck.drain(..) {
            let Constraint::HasMember {
                receiver,
                label,
                member,
                origin,
            } = constraint
            else {
                remaining.push(constraint);
                continue;
            };
            let shallow = self.store.shallow(&receiver);
            let owned = match &shallow {
                Ty::Var(v) => self.store.level(v.0) >= self.level,
                _ => false,
            };
            if !owned {
                // Concrete heads retry normally; outer-level variables may
                // be solved by a later group, so improvement (which commits)
                // must not fire — they float out instead.
                remaining.push(Constraint::HasMember {
                    receiver,
                    label,
                    member,
                    origin,
                });
                continue;
            }
            let label_str = label.to_string();
            let owners = self
                .catalog
                .member_owners
                .get(&label_str)
                .cloned()
                .unwrap_or_default();
            match owners.as_slice() {
                [MemberOwner::Protocol(protocol)] => {
                    if let Some((owner, requirement)) =
                        self.catalog.requirement_in(*protocol, &label_str)
                    {
                        let requirement = requirement.clone();
                        let witness = requirement.symbol;
                        self.bind_requirement(
                            owner,
                            &requirement,
                            &receiver,
                            &member,
                            origin,
                            queue,
                            witness,
                        );
                        improved = true;
                    } else {
                        remaining.push(Constraint::HasMember {
                            receiver,
                            label,
                            member,
                            origin,
                        });
                    }
                }
                [MemberOwner::Nominal(symbol)] => {
                    if !self.defaulting {
                        // One nominal owner, but a record receiver could
                        // also satisfy the use: hold the constraint on the
                        // binder's scheme; the final solve commits if no
                        // instantiation discharged it.
                        remaining.push(Constraint::HasMember {
                            receiver,
                            label,
                            member,
                            origin,
                        });
                        continue;
                    }
                    let params = self
                        .catalog
                        .structs
                        .get(symbol)
                        .map(|i| i.params.len())
                        .or_else(|| self.catalog.enums.get(symbol).map(|i| i.params.len()))
                        .unwrap_or(0);
                    let args: Vec<Ty> = (0..params)
                        .map(|_| Ty::Var(self.store.fresh_ty(self.level, origin.node)))
                        .collect();
                    queue.push(Constraint::Eq(
                        receiver.clone(),
                        Ty::Nominal(*symbol, args),
                        origin,
                    ));
                    queue.push(Constraint::HasMember {
                        receiver,
                        label,
                        member,
                        origin,
                    });
                    improved = true;
                }
                [] => {
                    // No nominal or protocol owns the label: the member
                    // is a record projection — default the receiver to an
                    // open record row (presence constraints become row
                    // unification: Gaster & Jones, POPL 1996; Leijen,
                    // Trends in FP 2005). The improvement gate above
                    // already restricts this to variables this group
                    // owns, so nominal information always wins, and the
                    // row tail generalizes if it survives the group.
                    let tail = self.store.fresh_row(self.level, origin.node);
                    let probe = Ty::Record(Row {
                        fields: vec![(label.clone(), member.clone())],
                        tail: Some(RowTail::Var(tail)),
                    });
                    queue.push(Constraint::Eq(receiver, probe, origin));
                    improved = true;
                }
                _many => {
                    // Several owners: the constraint stays open and rides
                    // the binder's scheme (qualified types — Jones 1994);
                    // each instantiation discharges it against a concrete
                    // receiver.
                    remaining.push(Constraint::HasMember {
                        receiver,
                        label,
                        member,
                        origin,
                    });
                }
            }
        }
        *stuck = remaining;
        improved
    }

    /// Solver-side symbol lookup: in-flight monomorphic signature, or a
    /// scheme instantiation (with its predicates emitted as new wanteds).
    fn symbol_ty(&mut self, symbol: Symbol, node: NodeID, queue: &mut Vec<Constraint>) -> Ty {
        if let Some(ty) = self.mono.get(&symbol) {
            return ty.clone();
        }
        if let Some(scheme) = self.schemes.get(&symbol) {
            let scheme = scheme.clone();
            return self.instantiate_scheme(&scheme, node, queue);
        }
        Ty::Var(self.store.fresh_ty(self.level, node))
    }

    fn instantiate_scheme(
        &mut self,
        scheme: &Scheme,
        node: NodeID,
        queue: &mut Vec<Constraint>,
    ) -> Ty {
        if scheme.params.is_empty() && scheme.eff_params.is_empty() && scheme.row_params.is_empty()
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
            effs.insert(*param, EffTail::Var(self.store.fresh_eff(self.level, node)));
        }
        let mut rows = FxHashMap::default();
        for param in &scheme.row_params {
            let var = self.store.fresh_row(self.level, node);
            // Recorded as an empty open record over the fresh variable
            // (zonked to the call's concrete row at finalize) for the
            // lowerer's per-call-site θ.
            recorded.push((
                *param,
                Ty::Record(Row {
                    fields: vec![],
                    tail: Some(RowTail::Var(var)),
                }),
            ));
            rows.insert(*param, RowTail::Var(var));
        }
        for predicate in &scheme.predicates {
            queue.push(
                predicate
                    .substitute(&tys, &effs, &rows)
                    .into_constraint(CtOrigin::new(node, CtReason::Apply)),
            );
        }
        self.instantiations
            .entry(node)
            .or_default()
            .extend(recorded);
        scheme.ty.substitute(&tys, &effs, &rows)
    }

    /// Robinson unification with eager decomposition; rule names follow the
    /// OutsideIn(X) simplifier's canonicalization (JFP 2011 §7.2-ish shapes).
    fn unify(&mut self, a: &Ty, b: &Ty, origin: CtOrigin, worklist: &mut Vec<Constraint>) {
        let a = self.store.shallow(a);
        let b = self.store.shallow(b);

        match (&a, &b) {
            // Error is poison: it unifies with anything silently so a single
            // mistake doesn't cascade into follow-on diagnostics.
            (Ty::Error, _) | (_, Ty::Error) => {}

            (Ty::Var(x), Ty::Var(y)) if self.store.find(x.0) == self.store.find(y.0) => {}
            (Ty::Var(x), Ty::Var(y)) => self.store.union(x.0, y.0),

            (Ty::Var(x), other) | (other, Ty::Var(x)) => {
                // Occurs check + Rémy level adjustment in one walk.
                let level = self.store.level(x.0);
                if self.occurs_and_adjust_ty(x.0, level, other) {
                    let rendered = self.store.render(other);
                    self.errors
                        .push((TypeError::InfiniteType { ty: rendered }, origin.node));
                    return;
                }
                self.store.bind(x.0, VarValue::Ty(other.clone()));
            }

            (Ty::Param(p), Ty::Param(q)) if p == q => {}

            // Projections are NOT injective (OutsideIn(X) treats type
            // functions as free symbols): `T.A ~ U.A` holds only when the
            // two are the same projection, never by decomposing to `T ~ U`.
            (Ty::Proj(b1, p1, a1), Ty::Proj(b2, p2, a2)) if p1 == p2 && a1 == a2 => {
                let z1 = self.store.zonk_ty(b1);
                let z2 = self.store.zonk_ty(b2);
                if z1 != z2 {
                    let expected = self.store.render(&a);
                    let found = self.store.render(&b);
                    self.errors
                        .push((TypeError::Mismatch { expected, found }, origin.node));
                }
            }

            (Ty::Nominal(s1, args1), Ty::Nominal(s2, args2))
                if s1 == s2 && args1.len() == args2.len() =>
            {
                for (a1, a2) in args1.iter().zip(args2) {
                    worklist.push(Constraint::Eq(a1.clone(), a2.clone(), origin));
                }
            }

            (Ty::Func(p1, r1, e1), Ty::Func(p2, r2, e2)) => {
                if p1.len() != p2.len() {
                    self.errors.push((
                        TypeError::ArityMismatch {
                            expected: p1.len(),
                            found: p2.len(),
                        },
                        origin.node,
                    ));
                    return;
                }
                for (a1, a2) in p1.iter().zip(p2) {
                    worklist.push(Constraint::Eq(a1.clone(), a2.clone(), origin));
                }
                worklist.push(Constraint::Eq((**r1).clone(), (**r2).clone(), origin));
                worklist.push(Constraint::EffEq(e1.clone(), e2.clone(), origin));
            }

            (Ty::Tuple(i1), Ty::Tuple(i2)) if i1.len() == i2.len() => {
                for (a1, a2) in i1.iter().zip(i2) {
                    worklist.push(Constraint::Eq(a1.clone(), a2.clone(), origin));
                }
            }

            (Ty::Record(r1), Ty::Record(r2)) => self.unify_rows(r1, r2, origin, worklist),

            _ => {
                let expected = self.store.render(&a);
                let found = self.store.render(&b);
                self.errors
                    .push((TypeError::Mismatch { expected, found }, origin.node));
            }
        }
    }

    /// Occurs check + level adjustment. Returns true when `root` occurs in
    /// `ty` (the infinite type). Adjusts every free variable in `ty` outward
    /// to at most `level` (Rémy 1992) — this is what keeps a variable shared
    /// with an outer binding group from being generalized by an inner one.
    fn occurs_and_adjust_ty(&mut self, root: u32, level: Level, ty: &Ty) -> bool {
        match self.store.shallow(ty) {
            Ty::Var(v) => {
                let r = self.store.find(v.0);
                if r == root {
                    return true;
                }
                if self.store.level(r) > level {
                    self.store.set_level(r, level);
                }
                false
            }
            Ty::Param(_) | Ty::Error => false,
            Ty::Nominal(_, args) => args
                .iter()
                .any(|a| self.occurs_and_adjust_ty(root, level, a)),
            Ty::Func(params, ret, eff) => {
                params
                    .iter()
                    .any(|p| self.occurs_and_adjust_ty(root, level, p))
                    || self.occurs_and_adjust_ty(root, level, &ret)
                    || self.occurs_and_adjust_eff(root, level, &eff)
            }
            Ty::Tuple(items) => items
                .iter()
                .any(|i| self.occurs_and_adjust_ty(root, level, i)),
            Ty::Proj(base, _, _) => self.occurs_and_adjust_ty(root, level, &base),
            Ty::Record(row) => {
                let (fields, tail) = self.store.flatten_row(&row);
                if let FlatTail::Var(v) = tail {
                    let r = self.store.find(v);
                    if r == root {
                        return true;
                    }
                    if self.store.level(r) > level {
                        self.store.set_level(r, level);
                    }
                }
                fields
                    .iter()
                    .any(|(_, t)| self.occurs_and_adjust_ty(root, level, t))
            }
        }
    }

    fn occurs_and_adjust_eff(&mut self, root: u32, level: Level, eff: &EffectRow) -> bool {
        let (_, tail) = self.store.flatten_eff(eff);
        if let FlatTail::Var(v) = tail {
            let r = self.store.find(v);
            if r == root {
                return true;
            }
            if self.store.level(r) > level {
                self.store.set_level(r, level);
            }
        }
        false
    }

    /// Effect-row unification: Leijen's scoped-label row rewriting,
    /// specialized to the Koka-style effect-label set Talk uses. The leftover
    /// labels of each side flow into the other side's tail via a fresh shared
    /// tail.
    fn unify_eff(&mut self, a: &EffectRow, b: &EffectRow, origin: CtOrigin) {
        let (sa, ta) = self.store.flatten_eff(a);
        let (sb, tb) = self.store.flatten_eff(b);

        let only_a: BTreeSet<Symbol> = sa.difference(&sb).cloned().collect();
        let only_b: BTreeSet<Symbol> = sb.difference(&sa).cloned().collect();

        let mismatch = |solver: &mut Self| {
            let expected = solver.store.render_eff(a);
            let found = solver.store.render_eff(b);
            solver
                .errors
                .push((TypeError::Mismatch { expected, found }, origin.node));
        };

        match (ta, tb) {
            (FlatTail::Var(x), FlatTail::Var(y)) if self.store.find(x) == self.store.find(y) => {
                // Same tail on both sides: the label sets must already agree
                // (with set semantics, s1 ∪ t = s2 ∪ t has no solution for t
                // we could pick without guessing).
                if !only_a.is_empty() || !only_b.is_empty() {
                    mismatch(self);
                }
            }
            (FlatTail::Var(x), FlatTail::Var(y)) => {
                let level = self.store.level(x).min(self.store.level(y));
                let fresh = self.store.fresh_eff(level, origin.node);
                self.store.bind(
                    x,
                    VarValue::Eff(EffectRow {
                        effects: only_b,
                        tail: Some(EffTail::Var(fresh)),
                    }),
                );
                self.store.bind(
                    y,
                    VarValue::Eff(EffectRow {
                        effects: only_a,
                        tail: Some(EffTail::Var(fresh)),
                    }),
                );
            }
            (FlatTail::Var(x), FlatTail::None) => {
                if !only_a.is_empty() {
                    mismatch(self);
                    return;
                }
                self.store.bind(
                    x,
                    VarValue::Eff(EffectRow {
                        effects: only_b,
                        tail: None,
                    }),
                );
            }
            (FlatTail::None, FlatTail::Var(y)) => {
                if !only_b.is_empty() {
                    mismatch(self);
                    return;
                }
                self.store.bind(
                    y,
                    VarValue::Eff(EffectRow {
                        effects: only_a,
                        tail: None,
                    }),
                );
            }
            (FlatTail::None, FlatTail::None) => {
                if !only_a.is_empty() || !only_b.is_empty() {
                    mismatch(self);
                }
            }
            (FlatTail::Param(p), FlatTail::Param(q)) => {
                if p != q || !only_a.is_empty() || !only_b.is_empty() {
                    mismatch(self);
                }
            }
            // Rigid tail vs variable tail: the variable side absorbs the
            // rigid tail. Sound only when the rigid side already covers the
            // other side's labels; we cannot look inside a rigid row.
            (FlatTail::Param(p), FlatTail::Var(y)) => {
                if !only_b.is_empty() {
                    mismatch(self);
                    return;
                }
                self.store.bind(
                    y,
                    VarValue::Eff(EffectRow {
                        effects: only_a,
                        tail: Some(EffTail::Param(p)),
                    }),
                );
            }
            (FlatTail::Var(x), FlatTail::Param(q)) => {
                if !only_a.is_empty() {
                    mismatch(self);
                    return;
                }
                self.store.bind(
                    x,
                    VarValue::Eff(EffectRow {
                        effects: only_b,
                        tail: Some(EffTail::Param(q)),
                    }),
                );
            }
            (FlatTail::Param(_), FlatTail::None) | (FlatTail::None, FlatTail::Param(_)) => {
                mismatch(self);
            }
        }
    }

    /// Record-row unification by decomposition (Leijen 2005 §3): fields
    /// common to both sides unify pointwise; each side's leftover fields
    /// flow into the other side's tail.
    fn unify_rows(&mut self, a: &Row, b: &Row, origin: CtOrigin, worklist: &mut Vec<Constraint>) {
        let (fa, ta) = self.store.flatten_row(a);
        let (fb, tb) = self.store.flatten_row(b);

        let labels_a: FxHashMap<&Label, &Ty> = fa.iter().map(|(l, t)| (l, t)).collect();
        let labels_b: FxHashMap<&Label, &Ty> = fb.iter().map(|(l, t)| (l, t)).collect();

        let mut only_a: Vec<(Label, Ty)> = vec![];
        for (label, ty) in &fa {
            match labels_b.get(label) {
                Some(other) => worklist.push(Constraint::Eq(ty.clone(), (*other).clone(), origin)),
                None => only_a.push((label.clone(), ty.clone())),
            }
        }
        let only_b: Vec<(Label, Ty)> = fb
            .iter()
            .filter(|(l, _)| !labels_a.contains_key(l))
            .cloned()
            .collect();

        let mismatch = |solver: &mut Self| {
            let expected = solver.store.render(&Ty::Record(a.clone()));
            let found = solver.store.render(&Ty::Record(b.clone()));
            solver
                .errors
                .push((TypeError::Mismatch { expected, found }, origin.node));
        };

        match (ta, tb) {
            (FlatTail::Var(x), FlatTail::Var(y)) if self.store.find(x) == self.store.find(y) => {
                if !only_a.is_empty() || !only_b.is_empty() {
                    mismatch(self);
                }
            }
            (FlatTail::Var(x), FlatTail::Var(y)) => {
                // Occurs check on row tails: each tail must not appear in the
                // row it absorbs (Leijen 2005's termination condition).
                let level = self.store.level(x).min(self.store.level(y));
                let fresh = self.store.fresh_row(level, origin.node);
                self.store.bind(
                    x,
                    VarValue::Row(Row {
                        fields: only_b,
                        tail: Some(RowTail::Var(fresh)),
                    }),
                );
                self.store.bind(
                    y,
                    VarValue::Row(Row {
                        fields: only_a,
                        tail: Some(RowTail::Var(fresh)),
                    }),
                );
            }
            (FlatTail::Var(x), FlatTail::None) => {
                if !only_a.is_empty() {
                    mismatch(self);
                    return;
                }
                self.store.bind(
                    x,
                    VarValue::Row(Row {
                        fields: only_b,
                        tail: None,
                    }),
                );
            }
            (FlatTail::None, FlatTail::Var(y)) => {
                if !only_b.is_empty() {
                    mismatch(self);
                    return;
                }
                self.store.bind(
                    y,
                    VarValue::Row(Row {
                        fields: only_a,
                        tail: None,
                    }),
                );
            }
            (FlatTail::None, FlatTail::None) => {
                if !only_a.is_empty() || !only_b.is_empty() {
                    mismatch(self);
                }
            }
            (FlatTail::Param(p), FlatTail::Param(q)) => {
                if p != q || !only_a.is_empty() || !only_b.is_empty() {
                    mismatch(self);
                }
            }
            (FlatTail::Param(p), FlatTail::Var(y)) => {
                if !only_b.is_empty() {
                    mismatch(self);
                    return;
                }
                self.store.bind(
                    y,
                    VarValue::Row(Row {
                        fields: only_a,
                        tail: Some(RowTail::Param(p)),
                    }),
                );
            }
            (FlatTail::Var(x), FlatTail::Param(q)) => {
                if !only_a.is_empty() {
                    mismatch(self);
                    return;
                }
                self.store.bind(
                    x,
                    VarValue::Row(Row {
                        fields: only_b,
                        tail: Some(RowTail::Param(q)),
                    }),
                );
            }
            (FlatTail::Param(_), FlatTail::None) | (FlatTail::None, FlatTail::Param(_)) => {
                mismatch(self);
            }
        }
    }
}

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

    fn mint_param(&mut self) -> Symbol {
        let param = Symbol::TypeParameter(self.symbols.next_type_parameter(self.module_id));
        self.minted.insert(param);
        param
    }

    fn quantify_predicate(&mut self, predicate: &Predicate) -> Predicate {
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

    fn quantify_row(&mut self, row: &Row) -> Row {
        match self.quantify_ty(&Ty::Record(row.clone())) {
            Ty::Record(row) => row,
            _ => row.clone(),
        }
    }

    fn quantify_ty(&mut self, ty: &Ty) -> Ty {
        match self.store.shallow(ty) {
            Ty::Var(v) => {
                let root = self.store.find(v.0);
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
            Ty::Param(sym) => {
                // Quantified earlier by this same group: include it in this
                // scheme's parameter list too (params are per-scheme). Rigid
                // params from elsewhere (a nominal's generics) stay free.
                if self.minted.contains(&sym) && !self.params.iter().any(|p| p.symbol == sym) {
                    self.params.push(SchemeParam { symbol: sym });
                }
                Ty::Param(sym)
            }
            Ty::Nominal(sym, args) => {
                Ty::Nominal(sym, args.iter().map(|a| self.quantify_ty(a)).collect())
            }
            Ty::Func(params, ret, eff) => {
                let params = params.iter().map(|p| self.quantify_ty(p)).collect();
                let ret = Box::new(self.quantify_ty(&ret));
                let eff = self.quantify_eff(&eff);
                Ty::Func(params, ret, eff)
            }
            Ty::Tuple(items) => Ty::Tuple(items.iter().map(|i| self.quantify_ty(i)).collect()),
            Ty::Proj(base, protocol, assoc) => {
                Ty::Proj(Box::new(self.quantify_ty(&base)), protocol, assoc)
            }
            Ty::Record(row) => {
                let zonked = self.store.zonk_row(&row);
                let fields = zonked
                    .fields
                    .iter()
                    .map(|(l, t)| (l.clone(), self.quantify_ty(t)))
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
                Ty::Record(Row { fields, tail })
            }
            Ty::Error => Ty::Error,
        }
    }

    fn quantify_eff(&mut self, eff: &EffectRow) -> EffectRow {
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

/// One-way structural match binding rigid params in `pattern` to the
/// corresponding pieces of `actual` (matching a conformance row's head
/// application against a concrete type).
/// One-way structural matching of a declared pattern type (over rigid
/// `Param`s) against a concrete actual: the binding a conformance row or
/// member owner performs at discharge. Shared with the lowerer, which
/// re-derives the same bindings when demanding specializations.
pub(crate) fn bind_param_pattern(pattern: &Ty, actual: &Ty, bindings: &mut FxHashMap<Symbol, Ty>) {
    match (pattern, actual) {
        (Ty::Param(symbol), concrete) => {
            bindings.entry(*symbol).or_insert_with(|| concrete.clone());
        }
        (Ty::Nominal(_, pattern_args), Ty::Nominal(_, actual_args)) => {
            for (p, a) in pattern_args.iter().zip(actual_args) {
                bind_param_pattern(p, a, bindings);
            }
        }
        (Ty::Func(p1, r1, _), Ty::Func(p2, r2, _)) => {
            for (p, a) in p1.iter().zip(p2) {
                bind_param_pattern(p, a, bindings);
            }
            bind_param_pattern(r1, r2, bindings);
        }
        (Ty::Tuple(p1), Ty::Tuple(p2)) => {
            for (p, a) in p1.iter().zip(p2) {
                bind_param_pattern(p, a, bindings);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiling::module::ModuleId;
    use crate::name_resolution::symbol::EffectId;
    use crate::types::constraint::CtReason;

    fn origin() -> CtOrigin {
        CtOrigin::new(NodeID::ANY, CtReason::Apply)
    }

    fn effect(id: u32) -> Symbol {
        Symbol::Effect(EffectId::new(ModuleId::Current, id))
    }

    struct Harness {
        store: VarStore,
        errors: Vec<(TypeError, NodeID)>,
        catalog: TypeCatalog,
        schemes: FxHashMap<Symbol, Scheme>,
        mono: FxHashMap<Symbol, Ty>,
        instantiations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
        member_resolutions: FxHashMap<NodeID, MemberResolution>,
    }

    impl Harness {
        fn new() -> Self {
            Harness {
                store: VarStore::default(),
                errors: vec![],
                catalog: TypeCatalog::default(),
                schemes: FxHashMap::default(),
                mono: FxHashMap::default(),
                instantiations: FxHashMap::default(),
                member_resolutions: FxHashMap::default(),
            }
        }

        fn solve(&mut self, wanteds: Vec<Constraint>) -> Vec<Constraint> {
            let mut solver = Solver {
                store: &mut self.store,
                errors: &mut self.errors,
                catalog: &self.catalog,
                schemes: &self.schemes,
                mono: &self.mono,
                instantiations: &mut self.instantiations,
                member_resolutions: &mut self.member_resolutions,
                level: Level(1),
                defaulting: false,
                givens: vec![],
                derived_seen: Default::default(),
            };
            solver.solve(wanteds)
        }
    }

    #[test]
    fn occurs_check_rejects_infinite_type() {
        let mut h = Harness::new();
        let var = h.store.fresh_ty(Level(1), NodeID::ANY);
        let infinite = Ty::Func(vec![Ty::Var(var)], Box::new(Ty::unit()), EffectRow::pure());
        h.solve(vec![Constraint::Eq(Ty::Var(var), infinite, origin())]);
        assert_eq!(h.errors.len(), 1);
        assert!(matches!(h.errors[0].0, TypeError::InfiniteType { .. }));
    }

    #[test]
    fn level_adjustment_propagates_outward() {
        // Rémy 1992: binding an outer-level var to a type containing an
        // inner-level var must drag the inner var's level out, so an inner
        // generalization point can no longer quantify it.
        let mut h = Harness::new();
        let outer = h.store.fresh_ty(Level(0), NodeID::ANY);
        let inner = h.store.fresh_ty(Level(1), NodeID::ANY);
        h.solve(vec![Constraint::Eq(
            Ty::Var(outer),
            Ty::Func(
                vec![Ty::Var(inner)],
                Box::new(Ty::unit()),
                EffectRow::pure(),
            ),
            origin(),
        )]);
        assert!(h.errors.is_empty(), "{:?}", h.errors);
        assert_eq!(h.store.level(inner.0), Level(0));
    }

    #[test]
    fn effect_rows_merge_through_open_tails() {
        // Leijen-style row rewriting over a Koka-style effect-label set:
        // <'a | t1> ~ <'b | t2> leaves both flattening to {'a, 'b | t3}.
        let mut h = Harness::new();
        let t1 = h.store.fresh_eff(Level(1), NodeID::ANY);
        let t2 = h.store.fresh_eff(Level(1), NodeID::ANY);
        let a = EffectRow {
            effects: [effect(1)].into(),
            tail: Some(EffTail::Var(t1)),
        };
        let b = EffectRow {
            effects: [effect(2)].into(),
            tail: Some(EffTail::Var(t2)),
        };
        h.solve(vec![Constraint::EffEq(a.clone(), b.clone(), origin())]);
        assert!(h.errors.is_empty(), "{:?}", h.errors);
        let (za, ta) = h.store.flatten_eff(&a);
        let (zb, tb) = h.store.flatten_eff(&b);
        assert_eq!(za, [effect(1), effect(2)].into());
        assert_eq!(zb, za);
        assert_eq!(ta, tb, "both rows share the fresh tail");
    }

    #[test]
    fn closed_effect_row_rejects_extra_labels() {
        let mut h = Harness::new();
        let open = EffectRow {
            effects: [effect(1)].into(),
            tail: None,
        };
        let closed = EffectRow::pure();
        h.solve(vec![Constraint::EffEq(open, closed, origin())]);
        assert_eq!(h.errors.len(), 1);
    }

    #[test]
    fn record_rows_unify_by_decomposition() {
        // { x: Int | r1 } ~ { y: Float | r2 }: each side's leftover field
        // flows into the other's tail (Leijen 2005 §3).
        let mut h = Harness::new();
        let r1 = h.store.fresh_row(Level(1), NodeID::ANY);
        let r2 = h.store.fresh_row(Level(1), NodeID::ANY);
        let a = Row {
            fields: vec![(Label::Named("x".into()), Ty::Nominal(Symbol::Int, vec![]))],
            tail: Some(RowTail::Var(r1)),
        };
        let b = Row {
            fields: vec![(Label::Named("y".into()), Ty::Nominal(Symbol::Float, vec![]))],
            tail: Some(RowTail::Var(r2)),
        };
        h.solve(vec![Constraint::Eq(
            Ty::Record(a.clone()),
            Ty::Record(b.clone()),
            origin(),
        )]);
        assert!(h.errors.is_empty(), "{:?}", h.errors);
        let za = h.store.zonk_row(&a);
        let zb = h.store.zonk_row(&b);
        assert_eq!(za.fields, zb.fields);
        assert_eq!(za.fields.len(), 2);
    }

    #[test]
    fn closed_record_rows_must_match_exactly() {
        let mut h = Harness::new();
        let a = Row::closed(vec![(
            Label::Named("x".into()),
            Ty::Nominal(Symbol::Int, vec![]),
        )]);
        let b = Row::closed(vec![]);
        h.solve(vec![Constraint::Eq(Ty::Record(a), Ty::Record(b), origin())]);
        assert_eq!(h.errors.len(), 1);
    }
}
