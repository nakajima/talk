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
use crate::types::Level;
use crate::name_resolution::symbol::{Symbol, Symbols};
use crate::node_id::NodeID;
use crate::types::catalog::{MemberOwner, Requirement, TypeCatalog};
use crate::types::constraint::{Constraint, CtOrigin, CtReason, Implication};
use crate::types::error::TypeError;
use crate::types::output::MemberResolution;
use crate::types::ty::{
    EffTail, EffVar, EffectEntry, EffectRow, Perm, PermVar, Predicate, Row, RowTail, RowVar,
    Scheme, SchemeParam, Ty, TyFold, TyVar, match_pattern,
};

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
        // Handler-extent boundaries wait until everything else quiesces:
        // only then has the extent's row content surfaced (LIFO, so an
        // inner handler filters before the outer one it feeds).
        let mut handler_boundaries: Vec<Constraint> = vec![];
        loop {
            let generation = self.store.generation();
            while let Some(constraint) = queue.pop() {
                match constraint {
                    Constraint::HandleEffect { .. } => handler_boundaries.push(constraint),
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
                    Constraint::Implic(implication) => {
                        let residual = self.solve_implication(*implication);
                        queue.extend(residual);
                    }
                }
            }
            if stuck.is_empty() {
                if handler_boundaries.is_empty() {
                    return vec![];
                }
                self.process_handler_boundaries(&mut handler_boundaries, &mut stuck);
                continue;
            }
            if self.store.generation() != generation {
                queue = std::mem::take(&mut stuck);
                continue;
            }
            if self.improve(&mut stuck, &mut queue) {
                queue.extend(std::mem::take(&mut stuck));
                continue;
            }
            if !handler_boundaries.is_empty() {
                self.process_handler_boundaries(&mut handler_boundaries, &mut stuck);
                queue.extend(std::mem::take(&mut stuck));
                continue;
            }
            if self.default_apply_borrows(&mut stuck, &mut queue) {
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
                Constraint::EffEq(a, b, origin) => {
                    // Effect equalities can get stuck only when an
                    // implication makes the tail untouchable. Keep them so
                    // solve_implication can float them to a scope where that
                    // tail is touchable, or final solving can report the
                    // effect mismatch.
                    residual.push(Constraint::EffEq(a, b, origin));
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
                _ => {}
            }
        }
        residual
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
                    queue.push(Constraint::Eq(
                        expected_inner,
                        (*found_inner).clone(),
                        origin,
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
            _ => queue.push(Constraint::Eq(expected_inner, found, origin)),
        }
    }

    fn default_apply_borrows(
        &mut self,
        stuck: &mut Vec<Constraint>,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        let mut remaining = Vec::with_capacity(stuck.len());
        let mut defaulted = false;
        for constraint in stuck.drain(..) {
            match constraint {
                Constraint::ApplyBorrow {
                    expected_inner,
                    found,
                    origin,
                    ..
                } if matches!(self.store.shallow(&found), Ty::Var(_)) => {
                    queue.push(Constraint::Eq(expected_inner, found, origin));
                    defaulted = true;
                }
                other => remaining.push(other),
            }
        }
        *stuck = remaining;
        defaulted
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
}

mod conformance;
mod generalize;
mod givens;
mod implication;
mod improve;
mod member;
mod normalize;
mod pattern;
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
pub(crate) use normalize::reduce_projection;
use normalize::stuck_projection;
pub(crate) use pattern::bind_param_pattern;
pub(crate) use var_store::TyNode;
pub use var_store::VarStore;
use var_store::{FlatTail, VarValue};
