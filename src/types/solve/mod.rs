//! The constraint solver: one entry point, called once per binding group
//! (OutsideIn(X), Vytiniotis, Peyton Jones, Schrijvers & Sulzmann, JFP 2011 —
//! the simplifier of §7, instantiated for Talk's theory X = equalities over
//! types-with-rows, protocol conformance, and HasMember predicates).
//!
//! - Equalities solve by Robinson unification (JACM 1965) over a union-find
//!   `VarStore` with path compression.
//! - Variable levels follow Rémy (INRIA RR-1766, 1992): generalization
//!   quantifies exactly the variables deeper than the binding group's level,
//!   and binding a variable adjusts inner levels outward. Implications can
//!   also set a touchable level, using the same ordering to protect outer
//!   inference variables from local givens (OutsideIn §5, as in GHC's
//!   TcLevel).
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

use std::ops::ControlFlow;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::label::Label;
use crate::name_resolution::symbol::{Symbol, Symbols};
use crate::node_id::NodeID;
use crate::types::Level;
use crate::types::catalog::{MemberOwner, ProtocolApplication, Requirement, TypeCatalog};
use crate::types::constraint::{Constraint, CtOrigin, CtReason, Implication};
use crate::types::error::TypeError;
use crate::types::output::MemberResolution;
use crate::types::ty::{
    EffTail, EffVar, EffectEntry, EffectRow, Perm, PermVar, Predicate, ProtocolRef, Row, RowTail,
    RowVar, Scheme, SchemeParam, StaticAtom, StaticCmpOp, StaticInt, StaticValue, Ty, TyFold,
    TyVar, match_pattern,
};

const SOLVER_STEP_LIMIT: usize = 100_000;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ConformanceGoal {
    pub ty: Ty,
    pub protocol: ProtocolRef,
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
    /// Argument nodes where a borrowed value satisfied an owned CheapClone
    /// parameter by cloning (an O(1) buffer retain, emitted by lowering).
    pub coerce_clones: &'s mut FxHashSet<NodeID>,
    pub level: Level,
    /// True only in the final solve: committing a member constraint to its
    /// single nominal owner is defaulting, sound only once no later group
    /// can constrain the receiver further. Group solves hold such
    /// constraints instead, so they ride the binder's scheme (qualified
    /// types — Jones, *Qualified Types*, 1994).
    pub defaulting: bool,
    /// Local assumptions from declaration `where` clauses and GADT match
    /// refinements. They are erased evidence: used only to discharge wanteds
    /// while solving this implication.
    pub givens: Vec<Predicate>,
    /// When solving an implication, only variables at this level or deeper
    /// may be unified. Outer variables are untouchable in the OutsideIn(X)
    /// sense, so local givens cannot mutate global guesses.
    pub touchable_level: Option<Level>,
    /// Constructor-local skolems currently in scope. Residual constraints
    /// that mentioned these before local-given rewriting must not float out.
    pub local_params: Vec<Symbol>,
    /// In-flight auto-derived conformances, so recursive nominals resolve
    /// coinductively instead of looping. The complete goal matters: two
    /// applications of the same generic nominal can have different premises.
    pub(crate) derived_seen: rustc_hash::FxHashSet<ConformanceGoal>,
    /// Axiom-premise dependency edges seen during this solve. A new edge
    /// that reaches back to its source is a recursive conformance cycle.
    pub(crate) conformance_edges: FxHashMap<ConformanceGoal, FxHashSet<ConformanceGoal>>,
}

impl<'s> Solver<'s> {
    /// Solve to quiescence: run the worklist, retry stuck predicates while
    /// unification makes progress, then improve (unique-owner), then stop.
    /// Returns the residual variable-headed `Conforms` constraints for
    /// generalization; everything else unresolved becomes an error.
    pub fn solve(&mut self, wanteds: Vec<Constraint>) -> Vec<Constraint> {
        let mut queue = wanteds;
        let mut stuck: Vec<Constraint> = vec![];
        let mut preferred_equalities: Vec<(Ty, Ty, CtOrigin)> = vec![];
        // Handler-extent boundaries wait until everything else quiesces:
        // only then has the extent's row content surfaced (LIFO, so an
        // inner handler filters before the outer one it feeds).
        let mut handler_boundaries: Vec<Constraint> = vec![];
        // Effect flow from calls runs before handler elimination; explicit
        // function bounds run afterward against the handled body row.
        let mut effect_flows: Vec<Constraint> = vec![];
        let mut effect_bounds: Vec<Constraint> = vec![];
        let mut steps = 0usize;
        loop {
            let generation = self.store.generation();
            while let Some(constraint) = queue.pop() {
                steps += 1;
                if steps > SOLVER_STEP_LIMIT {
                    let node = Self::constraint_origin(&constraint)
                        .map_or(NodeID::SYNTHESIZED, |origin| origin.node);
                    let constraint = self.constraint_summary(&constraint);
                    self.errors.push((
                        TypeError::SolverOverflow {
                            limit: SOLVER_STEP_LIMIT,
                            constraint,
                        },
                        node,
                    ));
                    return vec![];
                }
                match constraint {
                    Constraint::HandleEffect { .. } => handler_boundaries.push(constraint),
                    Constraint::EffectSubset { origin, .. }
                        if origin.reason == CtReason::Effect =>
                    {
                        effect_bounds.push(constraint)
                    }
                    Constraint::EffectSubset { .. } => effect_flows.push(constraint),
                    Constraint::PreferEq(a, b, origin) => {
                        preferred_equalities.push((a, b, origin));
                    }
                    Constraint::Eq(a, b, origin) => {
                        let original_a = normalize_ty(self.store, self.catalog, &a);
                        let original_b = normalize_ty(self.store, self.catalog, &b);
                        let (a, a_local_param) =
                            self.rewrite_ty_from_givens_traced(original_a.clone());
                        let (b, b_local_param) =
                            self.rewrite_ty_from_givens_traced(original_b.clone());
                        let guarded = if let Some(param) = a_local_param {
                            Some(Constraint::Eq(original_a.clone(), Ty::Param(param), origin))
                        } else if let Some(param) = b_local_param {
                            Some(Constraint::Eq(original_b.clone(), Ty::Param(param), origin))
                        } else {
                            self.eq_residual_guard(&original_a, &original_b, origin)
                        };
                        if a == b {
                            continue;
                        }
                        if stuck_projection(self.store, &a)
                            || stuck_projection(self.store, &b)
                            || !self.unify(&a, &b, origin, &mut queue)
                        {
                            stuck.push(guarded.unwrap_or(Constraint::Eq(a, b, origin)));
                        }
                    }
                    Constraint::EffEq(a, b, origin) => {
                        if !self.unify_eff(&a, &b, origin) {
                            stuck.push(Constraint::EffEq(a, b, origin));
                        }
                    }
                    Constraint::ApplyBorrow {
                        expected_perm,
                        expected_inner,
                        found,
                        origin,
                    } => self.solve_apply_borrow(
                        expected_perm,
                        expected_inner,
                        found,
                        origin,
                        &mut queue,
                        &mut stuck,
                    ),
                    Constraint::CoerceOwned {
                        expected,
                        found,
                        origin,
                    } => self.solve_coerce_owned(expected, found, origin, &mut queue, &mut stuck),
                    Constraint::Conforms {
                        ty,
                        protocol,
                        origin,
                    } => {
                        if let Some(unsolved) = self.try_conforms(ty, protocol, origin, &mut queue)
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
                    Constraint::HasVariant {
                        enum_ty,
                        label,
                        payload,
                        ctor,
                        origin,
                    } => {
                        if let Some(unsolved) =
                            self.try_variant(enum_ty, label, payload, ctor, origin, &mut queue)
                        {
                            stuck.push(unsolved);
                        }
                    }
                    Constraint::PatternView {
                        scrutinee,
                        view,
                        origin,
                    } => match self.store.shallow(&scrutinee) {
                        Ty::Var(_) => stuck.push(Constraint::PatternView {
                            scrutinee,
                            view,
                            origin,
                        }),
                        Ty::Borrow(_, inner) => {
                            queue.push(Constraint::Eq(*inner, view, origin));
                        }
                        other => queue.push(Constraint::Eq(other, view, origin)),
                    },
                    Constraint::StringPattern { ty, origin } => match self.store.shallow(&ty) {
                        Ty::Var(_) => stuck.push(Constraint::StringPattern { ty, origin }),
                        Ty::Borrow(_, inner) => {
                            queue.push(Constraint::StringPattern { ty: *inner, origin });
                        }
                        Ty::Nominal(symbol, _)
                            if symbol == Symbol::String || symbol == Symbol::Substring => {}
                        other => self.report_mismatch(
                            &other,
                            &Ty::Nominal(Symbol::String, vec![]),
                            origin,
                        ),
                    },
                    // Static equality IS unification over the affine
                    // forms (it can solve metavariables); orderings go
                    // through evaluation/entailment.
                    Constraint::StaticCmp {
                        op: StaticCmpOp::Eq,
                        lhs,
                        rhs,
                        origin,
                    } => queue.push(Constraint::Eq(lhs, rhs, origin)),
                    Constraint::StaticCmp {
                        op,
                        lhs,
                        rhs,
                        origin,
                    } => {
                        if let Some(unsolved) = self.try_static_cmp(op, lhs, rhs, origin) {
                            stuck.push(unsolved);
                        }
                    }
                    Constraint::Implic(implication) => {
                        let residual = self.solve_implication(*implication);
                        queue.extend(residual);
                    }
                }
            }
            if stuck.is_empty() {
                if !effect_flows.is_empty() {
                    self.process_effect_subsets(&mut effect_flows, &mut stuck);
                    continue;
                }
                if !handler_boundaries.is_empty() {
                    self.process_handler_boundaries(&mut handler_boundaries, &mut stuck);
                    continue;
                }
                if !effect_bounds.is_empty() {
                    self.process_effect_subsets(&mut effect_bounds, &mut stuck);
                    continue;
                }
                if self.apply_preferred_equalities(&mut preferred_equalities, &mut queue) {
                    continue;
                }
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
            if !effect_flows.is_empty() {
                self.process_effect_subsets(&mut effect_flows, &mut stuck);
                queue.extend(std::mem::take(&mut stuck));
                continue;
            }
            if !handler_boundaries.is_empty() {
                self.process_handler_boundaries(&mut handler_boundaries, &mut stuck);
                queue.extend(std::mem::take(&mut stuck));
                continue;
            }
            if !effect_bounds.is_empty() {
                self.process_effect_subsets(&mut effect_bounds, &mut stuck);
                queue.extend(std::mem::take(&mut stuck));
                continue;
            }
            if self.default_apply_borrows(&mut stuck, &mut queue) {
                continue;
            }
            if self.apply_preferred_equalities(&mut preferred_equalities, &mut queue) {
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
                    if matches!(self.store.shallow(&ty), Ty::Var(_))
                        || protocol.args.iter().any(|arg| {
                            let arg = self.store.shallow(arg);
                            matches!(arg, Ty::Var(_))
                        })
                    {
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
                Constraint::EffEq(a, b, origin) => {
                    // Effect equalities can get stuck only when an
                    // implication makes the tail untouchable. Keep them so
                    // solve_implication can float them to a scope where that
                    // tail is touchable, or final solving can report the
                    // effect mismatch.
                    residual.push(Constraint::EffEq(a, b, origin));
                }
                bound @ Constraint::EffectSubset { .. } => {
                    residual.push(bound);
                }
                boundary @ Constraint::HandleEffect { .. } => {
                    // A handler boundary whose tails were untouchable here:
                    // float it to the scope (or the final solve) that owns
                    // them.
                    residual.push(boundary);
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
                Constraint::PatternView {
                    scrutinee,
                    view,
                    origin,
                } => {
                    // Float like HasMember: a later group may resolve the
                    // scrutinee's head.
                    residual.push(Constraint::PatternView {
                        scrutinee,
                        view,
                        origin,
                    });
                }
                string_pattern @ Constraint::StringPattern { .. } => {
                    residual.push(string_pattern);
                }
                variant @ Constraint::HasVariant { .. } => {
                    // Float like HasMember: a later group may resolve the
                    // enum's head.
                    residual.push(variant);
                }
                Constraint::ApplyBorrow {
                    expected_perm,
                    expected_inner,
                    found,
                    origin,
                } => {
                    residual.push(Constraint::ApplyBorrow {
                        expected_perm,
                        expected_inner,
                        found,
                        origin,
                    });
                }
                coerce @ Constraint::CoerceOwned { .. } => {
                    residual.push(coerce);
                }
                _ => {}
            }
        }
        residual
    }

    fn apply_preferred_equalities(
        &mut self,
        preferences: &mut Vec<(Ty, Ty, CtOrigin)>,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        let mut applied = false;
        for (left, right, origin) in std::mem::take(preferences) {
            let left = self.store.shallow(&left);
            let right = self.store.shallow(&right);
            if matches!(left, Ty::Var(_)) || matches!(right, Ty::Var(_)) {
                queue.push(Constraint::Eq(left, right, origin));
                applied = true;
            }
        }
        applied
    }

    fn solve_apply_borrow(
        &mut self,
        expected_perm: Perm,
        expected_inner: Ty,
        found: Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
        stuck: &mut Vec<Constraint>,
    ) {
        let expected_inner = normalize_ty(self.store, self.catalog, &expected_inner);
        let found = normalize_ty(self.store, self.catalog, &found);
        if stuck_projection(self.store, &expected_inner) || stuck_projection(self.store, &found) {
            stuck.push(Constraint::ApplyBorrow {
                expected_perm,
                expected_inner,
                found,
                origin,
            });
            return;
        }

        match self.store.shallow(&found) {
            Ty::Var(_) => stuck.push(Constraint::ApplyBorrow {
                expected_perm,
                expected_inner,
                found,
                origin,
            }),
            Ty::Borrow(found_perm, found_inner) => {
                let expected_perm = self.store.shallow_perm(expected_perm);
                let found_perm = self.store.shallow_perm(found_perm);
                if expected_perm == found_perm
                    || (expected_perm == Perm::Shared && found_perm == Perm::Exclusive)
                {
                    // Peeling the borrow consumes the application boundary:
                    // the inner equation demotes `Apply` so a nested
                    // function type unifies invariantly.
                    queue.push(Constraint::Eq(
                        expected_inner,
                        (*found_inner).clone(),
                        origin.nested(),
                    ));
                } else {
                    queue.push(Constraint::Eq(
                        Ty::Borrow(expected_perm, Box::new(expected_inner)),
                        found,
                        origin,
                    ));
                }
            }
            Ty::Error => {}
            _ => queue.push(Constraint::Eq(expected_inner, found, origin.nested())),
        }
    }

    /// The owned twin of `solve_apply_borrow`: an owned slot fed a
    /// still-unsolved argument. A borrow-resolved argument satisfies an
    /// owned `Param` only when its declared bounds prove it is Copy or
    /// CheapClone, or a concrete Copy/CheapClone nominal (the eager tier-2
    /// rule's deferred form); anything else is the plain equality this
    /// deferral replaced.
    fn solve_coerce_owned(
        &mut self,
        expected: Ty,
        found: Ty,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
        stuck: &mut Vec<Constraint>,
    ) {
        let found = normalize_ty(self.store, self.catalog, &found);
        match self.store.shallow(&found) {
            Ty::Var(_) => stuck.push(Constraint::CoerceOwned {
                expected,
                found,
                origin,
            }),
            Ty::Borrow(_, found_inner) => {
                let coerces = match self.store.shallow(&expected) {
                    // The slot's own type is still unsolved: whether this
                    // is a coercion (owned slot) or a plain borrow payload
                    // (e.g. `Optional<&T>`) is not decidable yet. Wait; the
                    // fixpoint default turns leftovers into the plain
                    // equality (today's inference).
                    Ty::Var(_) => {
                        stuck.push(Constraint::CoerceOwned {
                            expected,
                            found,
                            origin,
                        });
                        return;
                    }
                    Ty::Param(param) => {
                        let bounds = self
                            .catalog
                            .param_bounds
                            .get(&param)
                            .cloned()
                            .unwrap_or_default();
                        if let Some(kind) = self.catalog.bounds_coerce_kind(&bounds) {
                            if kind == crate::types::catalog::CoerceKind::CheapClone {
                                self.coerce_clones.insert(origin.node);
                            }
                            queue.push(Constraint::Eq(
                                expected,
                                (*found_inner).clone(),
                                origin.nested(),
                            ));
                        } else {
                            let rendered = self.store.render(&expected);
                            self.errors.push((
                                TypeError::NotConforming {
                                    ty: rendered,
                                    protocol: "Copy or CheapClone".to_string(),
                                },
                                origin.node,
                            ));
                        }
                        return;
                    }
                    Ty::Nominal(symbol, _) => {
                        if let Some(kind) = self.catalog.coerce_kind(symbol) {
                            if kind == crate::types::catalog::CoerceKind::CheapClone {
                                self.coerce_clones.insert(origin.node);
                            }
                            queue.push(Constraint::Eq(
                                expected,
                                (*found_inner).clone(),
                                origin.nested(),
                            ));
                            return;
                        }
                        false
                    }
                    _ => false,
                };
                if coerces {
                    self.coerce_clones.insert(origin.node);
                    queue.push(Constraint::Eq(
                        expected,
                        (*found_inner).clone(),
                        origin.nested(),
                    ));
                } else {
                    queue.push(Constraint::Eq(expected, found, origin.nested()));
                }
            }
            Ty::Error => {}
            _ => queue.push(Constraint::Eq(expected, found, origin.nested())),
        }
    }

    /// Commit still-variable auto-borrow/owned-slot arguments to their
    /// plain-equality reading. Defaulting a var another stuck constraint
    /// will WRITE once its own head resolves (a `HasVariant` payload, a
    /// `HasMember` member type) races that resolution: the chain floats to
    /// the final solve, so the premature owned equality contradicts the
    /// borrow the chain delivers (ADR 0017 bug B — a loop binder over a
    /// borrowed-receiver method source pinned owned inside its group,
    /// mismatching the `&Element` the `.some` payload resolves to). Such
    /// vars stay stuck and float out with their chain; everything else
    /// defaults here so in-group generalization still sees one type.
    fn default_apply_borrows(
        &mut self,
        stuck: &mut Vec<Constraint>,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        let pending_outputs = self.pending_output_vars(stuck);
        let mut remaining = Vec::with_capacity(stuck.len());
        let mut defaulted = false;
        for constraint in stuck.drain(..) {
            match constraint {
                Constraint::CoerceOwned {
                    expected,
                    found,
                    origin,
                } if (matches!(self.store.shallow(&found), Ty::Var(_))
                    || matches!(self.store.shallow(&expected), Ty::Var(_)))
                    && !self.mentions_pending_output(&found, &pending_outputs)
                    && !self.mentions_pending_output(&expected, &pending_outputs) =>
                {
                    queue.push(Constraint::Eq(expected, found, origin.nested()));
                    defaulted = true;
                }
                Constraint::ApplyBorrow {
                    expected_inner,
                    found,
                    origin,
                    ..
                } if matches!(self.store.shallow(&found), Ty::Var(_))
                    && !self.mentions_pending_output(&found, &pending_outputs) =>
                {
                    queue.push(Constraint::Eq(expected_inner, found, origin.nested()));
                    defaulted = true;
                }
                other => remaining.push(other),
            }
        }
        *stuck = remaining;
        defaulted
    }

    /// Root ids of variables a stuck constraint will still write when its
    /// pending head resolves: `HasVariant` payload/ctor slots and
    /// `HasMember` member types. These are outputs — the constraint waits
    /// on its receiver/enum head, not on them — so they may not be
    /// defaulted out from under the chain.
    fn pending_output_vars(&mut self, stuck: &[Constraint]) -> rustc_hash::FxHashSet<u32> {
        let mut outputs = rustc_hash::FxHashSet::default();
        let mut tys: Vec<Ty> = vec![];
        for constraint in stuck {
            match constraint {
                Constraint::HasVariant { payload, ctor, .. } => {
                    tys.extend(payload.iter().map(|(_, ty)| ty.clone()));
                    tys.extend(ctor.clone());
                }
                Constraint::HasMember { member, .. } => tys.push(member.clone()),
                _ => {}
            }
        }
        for ty in tys {
            let ty = self.store.zonk_ty(&ty);
            let mut vars = vec![];
            let _ = ty.try_visit(&mut |ty| {
                if let Ty::Var(var) = ty {
                    vars.push(var.0);
                }
                std::ops::ControlFlow::<()>::Continue(())
            });
            for var in vars {
                outputs.insert(self.store.find(var));
            }
        }
        outputs
    }

    fn mentions_pending_output(&mut self, ty: &Ty, pending: &rustc_hash::FxHashSet<u32>) -> bool {
        if pending.is_empty() {
            return false;
        }
        match self.store.shallow(ty) {
            Ty::Var(var) => pending.contains(&self.store.find(var.0)),
            _ => false,
        }
    }

    pub(super) fn eq_residual_guard(
        &mut self,
        a: &Ty,
        b: &Ty,
        origin: CtOrigin,
    ) -> Option<Constraint> {
        self.given_mentions_local_params(a, b)
            .map(|_| Constraint::Eq(a.clone(), b.clone(), origin))
    }

    fn constraint_summary(&mut self, constraint: &Constraint) -> String {
        match constraint {
            Constraint::Eq(a, b, _) => {
                let a = self.store.render(a);
                let b = self.store.render(b);
                format!("{a} == {b}")
            }
            Constraint::EffEq(a, b, _) => {
                let a = self.store.render_eff(a);
                let b = self.store.render_eff(b);
                format!("effects {a} == {b}")
            }
            Constraint::EffectSubset {
                inferred, allowed, ..
            } => {
                let inferred = self.store.render_eff(inferred);
                let allowed = self.store.render_eff(allowed);
                format!("effects {inferred} within {allowed}")
            }
            Constraint::PreferEq(a, b, _) => {
                let a = self.store.render(a);
                let b = self.store.render(b);
                format!("prefer {a} == {b}")
            }
            Constraint::Conforms { ty, protocol, .. } => {
                let ty = self.store.render(ty);
                let protocol = self.protocol_summary(protocol);
                format!("{ty} conforms to {protocol}")
            }
            Constraint::HasMember {
                receiver,
                label,
                member,
                ..
            } => {
                let receiver = self.store.render(receiver);
                let member = self.store.render(member);
                format!("{receiver} has member `{label}` of type {member}")
            }
            Constraint::HasVariant {
                enum_ty,
                label,
                payload,
                ctor,
                ..
            } => {
                let enum_ty = self.store.render(enum_ty);
                let payload = payload
                    .iter()
                    .map(|(payload_label, ty)| match payload_label {
                        Label::Named(label) => format!("{label}: {}", self.store.render(ty)),
                        Label::Positional(_) | Label::_Symbol(_) => self.store.render(ty),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                let ctor = ctor
                    .as_ref()
                    .map(|ty| format!(" with constructor {}", self.store.render(ty)))
                    .unwrap_or_default();
                format!("{enum_ty} has variant `.{label}({payload})`{ctor}")
            }
            Constraint::ApplyBorrow {
                expected_inner,
                found,
                ..
            } => {
                let expected_inner = self.store.render(expected_inner);
                let found = self.store.render(found);
                format!("borrowed argument &{expected_inner} accepts {found}")
            }
            Constraint::CoerceOwned {
                expected, found, ..
            } => {
                let expected = self.store.render(expected);
                let found = self.store.render(found);
                format!("owned slot {expected} accepts {found}")
            }
            Constraint::PatternView {
                scrutinee, view, ..
            } => {
                let scrutinee = self.store.render(scrutinee);
                let view = self.store.render(view);
                format!("pattern view of {scrutinee} as {view}")
            }
            Constraint::StringPattern { ty, .. } => {
                format!("string pattern over {}", self.store.render(ty))
            }
            Constraint::HandleEffect {
                inner,
                effects,
                outer,
                ..
            } => {
                let inner = self.store.render_eff(inner);
                let effects = effects
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                let outer = self.store.render_eff(outer);
                format!("handler boundary removes [{effects}] from {inner} into {outer}")
            }
            Constraint::StaticCmp { op, lhs, rhs, .. } => {
                let lhs = self.store.render(lhs);
                let rhs = self.store.render(rhs);
                format!("{lhs} {} {rhs}", op.as_str())
            }
            Constraint::Implic(implication) => format!(
                "implication with {} given(s) and {} wanted(s)",
                implication.givens.len(),
                implication.wanteds.len()
            ),
        }
    }

    fn protocol_summary(&mut self, protocol: &ProtocolRef) -> String {
        if protocol.args.is_empty() {
            return protocol.protocol.to_string();
        }
        let args = protocol
            .args
            .iter()
            .map(|arg| self.store.render(arg))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{}<{args}>", protocol.protocol)
    }
}

mod conformance;
mod generalize;
mod givens;
mod implication;
mod improve;
mod member;
mod normalize;
mod pattern;
mod static_cmp;
#[cfg(test)]
mod tests;
mod unify;
mod var_store;

impl<'s> Solver<'s> {
    /// The root tail variable a row currently flattens to, if any — the
    /// identity used to order handler boundaries by data flow.
    fn row_tail_root(&mut self, row: &EffectRow) -> Option<u32> {
        match self.store.flatten_eff(row).1 {
            FlatTail::Var(v) => Some(v),
            _ => None,
        }
    }

    /// Solve effect inclusion after rows reach quiescence. Calls flow their
    /// concrete labels into an open ambient row. Explicit annotations close
    /// the body row against allowed labels and report anything outside the
    /// bound.
    fn process_effect_subsets(
        &mut self,
        bounds: &mut Vec<Constraint>,
        stuck: &mut Vec<Constraint>,
    ) {
        while let Some(bound) = bounds.pop() {
            let Constraint::EffectSubset {
                inferred,
                allowed,
                origin,
            } = bound
            else {
                unreachable!("effect subset queues hold only EffectSubset");
            };
            let (inferred_entries, _) = self.store.flatten_eff(&inferred);
            let (allowed_entries, allowed_tail) = self.store.flatten_eff(&allowed);

            // Calls flow their concrete labels into an open ambient row while
            // leaving room for effects from sibling expressions.
            if origin.reason != CtReason::Effect {
                let required = EffectRow::open(self.store.fresh_eff(self.level, origin.node));
                let required = EffectRow::new(inferred_entries, required.tail);
                if !self.unify_eff(&required, &allowed, origin) {
                    stuck.push(Constraint::EffectSubset {
                        inferred,
                        allowed,
                        origin,
                    });
                }
                continue;
            }

            // A declared function bound is closed. If it is temporarily
            // untouchable inside an implication, float it instead of
            // diagnosing against an incomplete row.
            if !matches!(allowed_tail, FlatTail::None) {
                stuck.push(Constraint::EffectSubset {
                    inferred,
                    allowed,
                    origin,
                });
                continue;
            }

            let allowed_labels: FxHashSet<Symbol> =
                allowed_entries.iter().map(|entry| entry.effect).collect();
            let mut target_entries = inferred_entries.clone();
            for entry in &allowed_entries {
                if !target_entries
                    .iter()
                    .any(|inferred| inferred.effect == entry.effect)
                {
                    target_entries.push(entry.clone());
                }
            }
            let target = EffectRow::new(target_entries, None);
            if !self.unify_eff(&inferred, &target, origin) {
                stuck.push(Constraint::EffectSubset {
                    inferred,
                    allowed,
                    origin,
                });
                continue;
            }

            let mut undeclared: Vec<Symbol> = inferred_entries
                .iter()
                .map(|entry| entry.effect)
                .filter(|effect| !allowed_labels.contains(effect))
                .collect();
            undeclared.sort();
            undeclared.dedup();
            for effect in undeclared {
                self.errors.push((
                    TypeError::UndeclaredEffect {
                        effect: effect.to_string(),
                    },
                    origin.node,
                ));
            }
        }
    }

    /// Discharge handler-extent boundaries once the group's solve has
    /// quiesced: every occurrence of the covered labels in the extent's
    /// row is eliminated (label-scoped handling — one `@handle` covers
    /// every instantiation of its effect); the remaining occurrences and
    /// the residual tail flow to the outer row. Boundaries are processed
    /// innermost-first by data flow: one whose extent row is fed by
    /// another pending boundary's outer row must wait for it, or entries
    /// would slip past its filter.
    fn process_handler_boundaries(
        &mut self,
        boundaries: &mut Vec<Constraint>,
        stuck: &mut Vec<Constraint>,
    ) {
        while !boundaries.is_empty() {
            let outer_roots: Vec<Option<u32>> = boundaries
                .iter()
                .map(|boundary| match boundary {
                    Constraint::HandleEffect { outer, .. } => {
                        let outer = outer.clone();
                        self.row_tail_root(&outer)
                    }
                    _ => None,
                })
                .collect();
            let index = boundaries
                .iter()
                .enumerate()
                .position(|(i, boundary)| match boundary {
                    Constraint::HandleEffect { inner, .. } => {
                        let inner = inner.clone();
                        let inner_root = self.row_tail_root(&inner);
                        inner_root.is_none()
                            || !outer_roots
                                .iter()
                                .enumerate()
                                .any(|(j, root)| j != i && *root == inner_root)
                    }
                    _ => true,
                })
                .unwrap_or(0);
            let boundary = boundaries.remove(index);
            let Constraint::HandleEffect {
                inner,
                effects,
                outer,
                origin,
            } = boundary
            else {
                unreachable!("handler_boundaries holds only HandleEffect");
            };
            let (entries, tail) = self.store.flatten_eff(&inner);
            let rest: Vec<EffectEntry> = entries
                .into_iter()
                .filter(|entry| !effects.contains(&entry.effect))
                .collect();
            let tail = match tail {
                FlatTail::None => None,
                FlatTail::Var(v) => Some(EffTail::Var(EffVar(v))),
                FlatTail::Param(sym) => Some(EffTail::Param(sym)),
            };
            let rest_row = EffectRow::new(rest, tail);
            if !self.unify_eff(&rest_row, &outer, origin) {
                stuck.push(Constraint::HandleEffect {
                    inner,
                    effects,
                    outer,
                    origin,
                });
            }
        }
    }
}

pub use generalize::Generalizer;
pub(crate) use generalize::quantify_leftover_eff_vars;
pub use normalize::normalize_ty;
use normalize::stuck_projection;
pub(crate) use pattern::bind_param_pattern;
pub(crate) use var_store::TyNode;
pub use var_store::VarStore;
use var_store::{FlatTail, VarValue};
