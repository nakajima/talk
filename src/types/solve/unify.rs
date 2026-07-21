use super::*;
use crate::types::catalog::{CoerceKind, Grade};
use crate::types::ty::Perm;

/// Where a leftover row/effect-row binds its tail when it flows into a
/// variable. Kind-agnostic: `unify_row_like` decides it from the flattened
/// tails alone, and each caller maps it to a concrete `EffTail`/`RowTail`.
enum TailSpec {
    Var(u32),
    Closed,
    Param(Symbol),
}

/// Outcome of permission unification: solved (or bound), a concrete
/// mismatch, or blocked on an untouchable variable inside an implication.
enum PermUnify {
    Ok,
    Mismatch,
    Defer,
}

impl<'s> Solver<'s> {
    /// OutsideIn(X)'s touchability test: inside an implication, only local
    /// unification variables may be solved; outer variables are protected
    /// from branch-local assumptions.
    pub(super) fn is_touchable(&mut self, var: u32) -> bool {
        let Some(level) = self.touchable_level else {
            return true;
        };
        self.store.level(var) >= level
    }

    /// Robinson unification with eager decomposition; rule names follow the
    /// OutsideIn(X) simplifier's canonicalization (JFP 2011 §7.2-ish shapes).
    /// Returns false when the only possible next step would bind an
    /// untouchable variable inside an implication.
    pub(super) fn unify(
        &mut self,
        a: &Ty,
        b: &Ty,
        origin: CtOrigin,
        worklist: &mut Vec<Constraint>,
    ) -> bool {
        let a = self.store.shallow(a);
        let b = self.store.shallow(b);

        match (&a, &b) {
            // Error is poison: it unifies with anything silently so a single
            // mistake doesn't cascade into follow-on diagnostics.
            (Ty::Error, _) | (_, Ty::Error) => {}

            (Ty::Unique(inner1), Ty::Unique(inner2)) => {
                worklist.push(Constraint::Eq(
                    (**inner1).clone(),
                    (**inner2).clone(),
                    origin,
                ));
            }

            // An owned value moves into a unique position at the immediate
            // application (the move makes it the sole reference).
            (Ty::Unique(inner), other) | (other, Ty::Unique(inner))
                if matches!(origin.reason, CtReason::Apply | CtReason::NestedApply) =>
            {
                worklist.push(Constraint::Eq(
                    (**inner).clone(),
                    other.clone(),
                    origin.nested(),
                ));
            }

            (Ty::Borrow(p1, inner1), Ty::Borrow(p2, inner2)) => match self.unify_perm(*p1, *p2) {
                PermUnify::Ok => worklist.push(Constraint::Eq(
                    (**inner1).clone(),
                    (**inner2).clone(),
                    origin,
                )),
                PermUnify::Mismatch => self.report_mismatch(&a, &b, origin),
                PermUnify::Defer => return false,
            },

            (Ty::Borrow(_, inner), other) if origin.reason == CtReason::Apply => {
                worklist.push(Constraint::Eq(
                    (**inner).clone(),
                    other.clone(),
                    origin.nested(),
                ));
            }

            // Tier-2 copy-out-of-borrow coercion: a borrowed argument
            // satisfies an owned parameter when extraction is free — Copy
            // grade (a scalar borrow is a value copy at runtime, nothing to
            // emit) or CheapClone (an O(1) buffer retain, emitted by
            // lowering at the recorded node).
            (Ty::Nominal(symbol, args), Ty::Borrow(_, found_inner))
                if origin.reason == CtReason::Apply
                    && self
                        .catalog
                        .coerce_kind_application(*symbol, args)
                        .is_some() =>
            {
                if self.catalog.coerce_kind_application(*symbol, args)
                    == Some(CoerceKind::CheapClone)
                {
                    self.coerce_clones.insert(origin.node);
                }
                worklist.push(Constraint::Eq(
                    a.clone(),
                    (**found_inner).clone(),
                    origin.nested(),
                ));
            }

            // Borrow erasure for Copy grades: `&T` and `T` are the same
            // type up to representation when T copies (using the value
            // never moves it, and a scalar borrow is a value copy), so they
            // unify in any position — annotations, nested arguments,
            // protocol signatures, and inference (`&Int` never surfaces as
            // an inferred binding type).
            (Ty::Borrow(_, inner), other) | (other, Ty::Borrow(_, inner))
                if matches!(
                    self.store.shallow(inner),
                    Ty::Nominal(symbol, args)
                        if self.catalog.grade_of_application(symbol, &args) == Grade::Copy
                ) =>
            {
                worklist.push(Constraint::Eq((**inner).clone(), other.clone(), origin));
            }

            // The deferred half of the same erasure: the borrow's payload is
            // still a variable (an inferred borrow-default parameter — plan
            // 3.3(b)) against a concrete nominal. When the nominal is
            // Copy-grade, erasing (payload := nominal) is the only possible
            // solution — the annotated twin's wrap never existed (`&Int`
            // never surfaces). Otherwise no payload can ever satisfy the
            // equation; bind it anyway so the mismatch reports the annotated
            // twin's rendering (`&String` vs `String`, not `&?3`) and the
            // body recovers with the same types.
            (Ty::Borrow(_, inner), other) | (other, Ty::Borrow(_, inner))
                if matches!(self.store.shallow(inner), Ty::Var(_))
                    && matches!(other, Ty::Nominal(..)) =>
            {
                let copy = matches!(other, Ty::Nominal(symbol, args)
                    if self.catalog.grade_of_application(*symbol, args) == Grade::Copy);
                if copy {
                    worklist.push(Constraint::Eq((**inner).clone(), other.clone(), origin));
                } else {
                    if let Ty::Var(v) = self.store.shallow(inner) {
                        let root = self.store.find(v.0);
                        let level = self.store.level(root);
                        if self.is_touchable(root) && !self.occurs_and_adjust_ty(root, level, other)
                        {
                            self.store.bind(root, VarValue::Ty(other.clone()));
                        }
                    }
                    self.report_mismatch(&a, &b, origin);
                }
            }

            // Static integer arguments (ADR 0035): a linear equation over
            // canonical affine forms. Runs BEFORE generic var binding so a
            // self-referential equation (`α ~ α + 1`) cancels to plain
            // unsatisfiable arithmetic instead of an infinite type, and so
            // var solutions get the affine treatment (cancellation, exact
            // division). Zonk first so already-solved atoms fold in.
            (
                Ty::Static(StaticValue::Int(_)),
                Ty::Static(StaticValue::Int(_)) | Ty::Param(_) | Ty::Var(_),
            )
            | (Ty::Param(_) | Ty::Var(_), Ty::Static(StaticValue::Int(_))) => {
                let lhs = self.store.zonk_ty(&a);
                let rhs = self.store.zonk_ty(&b);
                let (Some(lhs), Some(rhs)) = (StaticInt::from_ty(&lhs), StaticInt::from_ty(&rhs))
                else {
                    // An atom resolved to a non-index value; the kind error
                    // was reported where it was formed (or it is poison).
                    if !matches!(lhs, Ty::Error) && !matches!(rhs, Ty::Error) {
                        self.report_mismatch(&a, &b, origin);
                    }
                    return true;
                };
                return self.unify_static_int(&lhs, &rhs, &a, &b, origin);
            }

            (Ty::Var(x), Ty::Var(y)) if self.store.find(x.0) == self.store.find(y.0) => {}
            (Ty::Var(x), Ty::Var(y)) => {
                let x_root = self.store.find(x.0);
                let y_root = self.store.find(y.0);
                match (self.is_touchable(x_root), self.is_touchable(y_root)) {
                    (true, true) => self.store.union(x_root, y_root),
                    (true, false) => self
                        .store
                        .bind(x_root, VarValue::Ty(Ty::Var(TyVar(y_root)))),
                    (false, true) => self
                        .store
                        .bind(y_root, VarValue::Ty(Ty::Var(TyVar(x_root)))),
                    (false, false) => return false,
                }
            }

            (Ty::Var(x), other) | (other, Ty::Var(x)) => {
                let root = self.store.find(x.0);
                if !self.is_touchable(root) {
                    return false;
                }
                // Occurs check + Rémy level adjustment in one walk.
                let level = self.store.level(root);
                if self.occurs_and_adjust_ty(root, level, other) {
                    let rendered = self.store.render(other);
                    self.errors
                        .push((TypeError::InfiniteType { ty: rendered }, origin.node));
                    return true;
                }
                self.store.bind(root, VarValue::Ty(other.clone()));
            }

            (Ty::Param(p), Ty::Param(q)) if p == q => {}

            // Distinct rigid params can still be equal in the static
            // theory (`where N == M`). Ordinary type-param pairs have no
            // static facts and fail entailment into the same mismatch.
            (Ty::Param(_), Ty::Param(_)) => {
                let (Some(lhs), Some(rhs)) = (StaticInt::from_ty(&a), StaticInt::from_ty(&b))
                else {
                    self.report_mismatch(&a, &b, origin);
                    return true;
                };
                return self.unify_static_int(&lhs, &rhs, &a, &b, origin);
            }

            // Projections are NOT injective (OutsideIn(X) treats type
            // functions as free symbols): `T.A ~ U.A` holds only when the
            // two are the same projection, never by decomposing to `T ~ U`.
            (Ty::Proj(b1, p1, a1), Ty::Proj(b2, p2, a2)) if p1 == p2 && a1 == a2 => {
                let z1 = self.store.zonk_ty(b1);
                let z2 = self.store.zonk_ty(b2);
                if z1 != z2 {
                    let expected = self.store.render(&a);
                    let found = self.store.render(&b);
                    self.errors.push((
                        TypeError::Mismatch {
                            expected,
                            found,
                            reason: origin.reason,
                        },
                        origin.node,
                    ));
                }
            }

            (Ty::Nominal(s1, args1), Ty::Nominal(s2, args2))
                if s1 == s2 && args1.len() == args2.len() =>
            {
                let nested = origin.nested();
                for (a1, a2) in args1.iter().zip(args2) {
                    worklist.push(Constraint::Eq(a1.clone(), a2.clone(), nested));
                }
            }

            // Effect-arg padding: annotations spell nominal heads without
            // their implicit effect args (`Wrapper`, not `Wrapper<'e>`),
            // so a bare head ADOPTS the full head's eff suffix — the type
            // args still unify pairwise.
            (Ty::Nominal(s1, args1), Ty::Nominal(s2, args2))
                if s1 == s2 && args1.len() != args2.len() && {
                    let (short, long) = if args1.len() < args2.len() {
                        (args1, args2)
                    } else {
                        (args2, args1)
                    };
                    long[short.len()..].iter().all(|a| matches!(a, Ty::Eff(_)))
                        && !short.iter().any(|a| matches!(a, Ty::Eff(_)))
                } =>
            {
                let nested = origin.nested();
                let (short, long) = if args1.len() < args2.len() {
                    (args1, args2)
                } else {
                    (args2, args1)
                };
                for (a1, a2) in short.iter().zip(long) {
                    worklist.push(Constraint::Eq(a1.clone(), a2.clone(), nested));
                }
            }

            // Effect arguments (kind-restricted Nominal args) unify as the
            // rows they are.
            (Ty::Eff(e1), Ty::Eff(e2)) => {
                self.unify_eff(e1, e2, origin);
            }

            // The other static domains (Bool, enum cases) compare
            // structurally; mixed static kinds are mismatches.
            (Ty::Static(x), Ty::Static(y)) => {
                if x != y {
                    self.report_mismatch(&a, &b, origin);
                }
            }

            (
                Ty::Any {
                    protocol: p1,
                    assoc: a1,
                },
                Ty::Any {
                    protocol: p2,
                    assoc: a2,
                },
            ) if p1 == p2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2)
                    .all(|((left, _), (right, _))| left == right) =>
            {
                let nested = origin.nested();
                for ((_, left), (_, right)) in a1.iter().zip(a2) {
                    worklist.push(Constraint::Eq(left.clone(), right.clone(), nested));
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
                    return true;
                }
                // `Apply` auto-borrows the supplied argument to its parameter, but only at
                // the immediate application. `nested` drops `Apply`, so parameters of a
                // *nested* function type (which are contravariant) unify invariantly rather
                // than letting a function needing `&mut`/owned satisfy one invoked with `&`.
                let nested = origin.nested();
                for (a1, a2) in p1.iter().zip(p2) {
                    if origin.reason == CtReason::Apply {
                        self.push_apply_param_eq(a1, a2, nested, worklist);
                    } else {
                        worklist.push(Constraint::Eq(a1.clone(), a2.clone(), nested));
                    }
                }
                // Returns are covariant, so a found `&mut` return may downgrade to an
                // expected `&` return.
                self.push_borrow_downgrade_eq(r1, r2, nested, worklist);
                worklist.push(Constraint::EffEq(e1.clone(), e2.clone(), nested));
            }

            (Ty::Tuple(i1), Ty::Tuple(i2)) if i1.len() == i2.len() => {
                let nested = origin.nested();
                for (a1, a2) in i1.iter().zip(i2) {
                    worklist.push(Constraint::Eq(a1.clone(), a2.clone(), nested));
                }
            }

            (Ty::Record(r1), Ty::Record(r2)) => {
                if !self.unify_rows(r1, r2, origin.nested(), worklist) {
                    return false;
                }
            }

            _ if self.is_bare_param(&a) || self.is_bare_param(&b) => return false,

            _ => self.report_mismatch(&a, &b, origin),
        }
        true
    }

    /// Unify two borrow permissions over the two-point lattice. Invariant:
    /// subsumption (`Exclusive ≤ Shared`) lives only in the two coercion
    /// helpers below, never here — keeping plain unification syntactic keeps
    /// it decidable and principal. Perm vars bind like type vars (they share
    /// the `VarStore`), minus the occurs check: permissions have no structure.
    fn unify_perm(&mut self, a: Perm, b: Perm) -> PermUnify {
        let a = self.store.shallow_perm(a);
        let b = self.store.shallow_perm(b);
        if a == b {
            return PermUnify::Ok;
        }
        match (a, b) {
            (Perm::Var(x), Perm::Var(y)) => {
                match (self.is_touchable(x.0), self.is_touchable(y.0)) {
                    (true, _) => self.store.bind(x.0, VarValue::Perm(Perm::Var(y))),
                    (_, true) => self.store.bind(y.0, VarValue::Perm(Perm::Var(x))),
                    (false, false) => return PermUnify::Defer,
                }
                PermUnify::Ok
            }
            (Perm::Var(x), other) | (other, Perm::Var(x)) => {
                if !self.is_touchable(x.0) {
                    return PermUnify::Defer;
                }
                self.store.bind(x.0, VarValue::Perm(other));
                PermUnify::Ok
            }
            _ => PermUnify::Mismatch,
        }
    }

    /// Auto-borrow an immediate call argument to its parameter: an owned value
    /// satisfies a `&`/`&mut` parameter, and a `&mut` value satisfies a `&`
    /// parameter. Only called for `Apply` origins at the application boundary;
    /// the emitted sub-constraints use the (demoted) `origin` so nested
    /// function types do not coerce.
    fn push_apply_param_eq(
        &mut self,
        expected: &Ty,
        found: &Ty,
        origin: CtOrigin,
        worklist: &mut Vec<Constraint>,
    ) {
        if let Ty::Unique(expected_inner) = self.store.shallow(expected) {
            let constraint = match self.store.shallow(found) {
                Ty::Unique(found_inner) => {
                    Constraint::Eq((*expected_inner).clone(), (*found_inner).clone(), origin)
                }
                other => Constraint::Eq((*expected_inner).clone(), other.clone(), origin),
            };
            worklist.push(constraint);
            return;
        }
        match self.store.shallow(expected) {
            Ty::Borrow(expected_perm, expected_inner) => match self.store.shallow(found) {
                Ty::Borrow(found_perm, found_inner) => {
                    let expected_perm = self.store.shallow_perm(expected_perm);
                    let found_perm = self.store.shallow_perm(found_perm);
                    // `&mut` satisfies `&` at the application boundary; every
                    // other pairing (vars included) unifies invariantly via
                    // the full borrow types.
                    if expected_perm == found_perm
                        || (expected_perm == Perm::Shared && found_perm == Perm::Exclusive)
                    {
                        worklist.push(Constraint::Eq(
                            (*expected_inner).clone(),
                            (*found_inner).clone(),
                            origin,
                        ));
                    } else {
                        worklist.push(Constraint::Eq(expected.clone(), found.clone(), origin));
                    }
                }
                Ty::Var(_) => {
                    worklist.push(Constraint::ApplyBorrow {
                        expected_perm,
                        expected_inner: (*expected_inner).clone(),
                        found: found.clone(),
                        origin,
                    });
                }
                _ => {
                    worklist.push(Constraint::Eq(
                        (*expected_inner).clone(),
                        found.clone(),
                        origin,
                    ));
                }
            },
            _ => worklist.push(Constraint::Eq(expected.clone(), found.clone(), origin)),
        }
    }

    fn push_borrow_downgrade_eq(
        &mut self,
        expected: &Ty,
        found: &Ty,
        origin: CtOrigin,
        worklist: &mut Vec<Constraint>,
    ) {
        match (self.store.shallow(expected), self.store.shallow(found)) {
            (Ty::Borrow(expected_perm, expected_inner), Ty::Borrow(found_perm, found_inner))
                if self.store.shallow_perm(expected_perm) == Perm::Shared
                    && self.store.shallow_perm(found_perm) == Perm::Exclusive =>
            {
                worklist.push(Constraint::Eq(
                    (*expected_inner).clone(),
                    (*found_inner).clone(),
                    origin,
                ))
            }
            _ => worklist.push(Constraint::Eq(expected.clone(), found.clone(), origin)),
        }
    }

    pub(super) fn report_mismatch(&mut self, expected_ty: &Ty, found_ty: &Ty, origin: CtOrigin) {
        if origin.reason == CtReason::GadtBranch
            && self.gadt_branch_mismatch_is_ambiguous(expected_ty, found_ty)
        {
            self.errors
                .push((TypeError::AmbiguousGadtMatchResult, origin.node));
            return;
        }
        let expected = self.store.render(expected_ty);
        let found = self.store.render(found_ty);
        self.errors.push((
            TypeError::Mismatch {
                expected,
                found,
                reason: origin.reason,
            },
            origin.node,
        ));
    }

    pub(super) fn gadt_branch_mismatch_is_ambiguous(
        &mut self,
        expected_ty: &Ty,
        found_ty: &Ty,
    ) -> bool {
        let expected = self.store.shallow(expected_ty);
        let found = self.store.shallow(found_ty);
        match (&expected, &found) {
            (Ty::Nominal(left, _), Ty::Nominal(right, _)) if left != right => false,
            (Ty::Tuple(left), Ty::Tuple(right)) if left.len() != right.len() => false,
            (Ty::Func(left, ..), Ty::Func(right, ..)) if left.len() != right.len() => false,
            (
                Ty::Any {
                    protocol: left_protocol,
                    ..
                },
                Ty::Any {
                    protocol: right_protocol,
                    ..
                },
            ) if left_protocol != right_protocol => false,
            (left, right) if Self::same_ty_head_kind(left, right) => {
                self.ty_has_unresolved(&expected) || self.ty_has_unresolved(&found)
            }
            _ => false,
        }
    }

    pub(super) fn same_ty_head_kind(left: &Ty, right: &Ty) -> bool {
        matches!(
            (left, right),
            (Ty::Var(_), Ty::Var(_))
                | (Ty::Param(_), Ty::Param(_))
                | (Ty::Nominal(..), Ty::Nominal(..))
                | (Ty::Func(..), Ty::Func(..))
                | (Ty::Tuple(_), Ty::Tuple(_))
                | (Ty::Record(_), Ty::Record(_))
                | (Ty::Any { .. }, Ty::Any { .. })
                | (Ty::Proj(..), Ty::Proj(..))
                | (Ty::Error, Ty::Error)
        )
    }

    pub(super) fn ty_has_unresolved(&mut self, ty: &Ty) -> bool {
        // A bare variable, rigid param, or projection is unresolved, as is any
        // open row tail (variable or param). Effect tails do not count.
        self.store
            .query_resolved(ty, &mut |_, node| match node {
                TyNode::Ty(Ty::Var(_) | Ty::Param(_) | Ty::Proj(..)) | TyNode::RowTail(_) => {
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            })
            .is_break()
    }

    pub(super) fn is_bare_param(&mut self, ty: &Ty) -> bool {
        matches!(self.store.shallow(ty), Ty::Param(_))
    }

    /// One free variable seen during an occurs check: it *is* the cycle when
    /// its root is `root`; otherwise pull its level out to at most `level`
    /// (Rémy 1992). Returns true only when it is the cycle.
    fn occurs_var(&mut self, root: u32, level: Level, var: u32) -> bool {
        let r = self.store.find(var);
        if r == root {
            return true;
        }
        if self.store.level(r) > level {
            self.store.set_level(r, level);
        }
        false
    }

    /// Solve an affine static equality (ADR 0035 §4-5): move everything to
    /// one side and isolate a touchable metavariable whose coefficient
    /// divides the remainder exactly — the unique-solution rule; inference
    /// never guesses. Underdetermined equations (leftover variables, no
    /// exact isolation) defer; variable-free nonzero differences mismatch.
    fn unify_static_int(
        &mut self,
        lhs: &StaticInt,
        rhs: &StaticInt,
        a: &Ty,
        b: &Ty,
        origin: CtOrigin,
    ) -> bool {
        let difference = lhs.sub(rhs);
        if difference.is_zero() {
            return true;
        }
        for (atom, coeff) in &difference.terms {
            let StaticAtom::Var(var) = atom else {
                continue;
            };
            let root = self.store.find(var.0);
            if !self.is_touchable(root) {
                continue;
            }
            // var := -(difference - coeff·var) / coeff, when exact.
            let rest = difference
                .sub(&StaticInt::atom(*atom).scale(coeff))
                .scale(&(-1).into());
            let Some(value) = rest.div_exact(coeff) else {
                continue;
            };
            // Cancellation removed `var` from the solution, so this walk
            // is purely the Rémy level adjustment for the atoms the
            // solution carries.
            let value = value.into_ty();
            let level = self.store.level(root);
            if self.occurs_and_adjust_ty(root, level, &value) {
                self.report_mismatch(a, b, origin);
                return true;
            }
            self.store.bind(root, VarValue::Ty(value));
            return true;
        }
        if difference
            .terms
            .iter()
            .any(|(atom, _)| matches!(atom, StaticAtom::Var(_)))
        {
            return false;
        }
        // Rigid inequality is still equality modulo the declared static
        // theory: `Grid<N> ~ Grid<M>` holds under a given `N == M`. Both
        // directions must be entailed.
        let facts = self.static_facts(&difference);
        if crate::types::solve::static_cmp::entails_static(&facts, &difference)
            && crate::types::solve::static_cmp::entails_static(
                &facts,
                &difference.scale(&(-1).into()),
            )
        {
            return true;
        }
        // Bare rigid params defer like every other param equation: the
        // residual feeds skolem-escape analysis and final-solve blame.
        if self.is_bare_param(a) || self.is_bare_param(b) {
            return false;
        }
        self.report_mismatch(a, b, origin);
        true
    }

    /// Occurs check + level adjustment. Returns true when `root` occurs in
    /// `ty` (the infinite type). Adjusts every free variable in `ty` outward to
    /// at most `level` (Rémy 1992) — this is what keeps a variable shared with
    /// an outer binding group from being generalized by an inner one.
    ///
    /// Deliberately NOT a `TyFold` (ADR 0005): it *mutates* variable levels as
    /// it searches, so it is neither a pure rebuild nor a pure query. The
    /// per-variable step is shared via `occurs_var`.
    pub(super) fn occurs_and_adjust_ty(&mut self, root: u32, level: Level, ty: &Ty) -> bool {
        match self.store.shallow(ty) {
            Ty::Var(v) => self.occurs_var(root, level, v.0),
            Ty::Param(_) | Ty::Error => false,
            Ty::Nominal(_, args) => args
                .iter()
                .any(|a| self.occurs_and_adjust_ty(root, level, a)),
            Ty::Borrow(_, inner) => self.occurs_and_adjust_ty(root, level, &inner),
            Ty::Unique(inner) => self.occurs_and_adjust_ty(root, level, &inner),
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
            Ty::Any { assoc, .. } => assoc
                .iter()
                .any(|(_, ty)| self.occurs_and_adjust_ty(root, level, ty)),
            Ty::Proj(base, _, _) => self.occurs_and_adjust_ty(root, level, &base),
            Ty::Eff(eff) => {
                eff.effects.iter().any(|entry| {
                    entry
                        .args
                        .iter()
                        .any(|a| self.occurs_and_adjust_ty(root, level, a))
                }) || self.occurs_and_adjust_eff(root, level, &eff)
            }
            Ty::Record(row) => {
                let (fields, tail) = self.store.flatten_row(&row);
                if let FlatTail::Var(v) = tail
                    && self.occurs_var(root, level, v)
                {
                    return true;
                }
                fields
                    .iter()
                    .any(|(_, t)| self.occurs_and_adjust_ty(root, level, t))
            }
            Ty::Static(StaticValue::Int(int)) => int
                .terms
                .iter()
                .any(|(atom, _)| self.occurs_and_adjust_ty(root, level, &atom.as_ty())),
            Ty::Static(StaticValue::Bool(_) | StaticValue::Case(..)) => false,
        }
    }

    pub(super) fn occurs_and_adjust_eff(
        &mut self,
        root: u32,
        level: Level,
        eff: &EffectRow,
    ) -> bool {
        let (_, tail) = self.store.flatten_eff(eff);
        match tail {
            FlatTail::Var(v) => self.occurs_var(root, level, v),
            _ => false,
        }
    }

    pub(super) fn occurs_and_adjust_row_var(&mut self, root: u32, level: Level, row: &Row) -> bool {
        let (fields, tail) = self.store.flatten_row(row);
        if let FlatTail::Var(v) = tail
            && self.occurs_var(root, level, v)
        {
            return true;
        }
        fields
            .iter()
            .any(|(_, ty)| self.occurs_and_adjust_ty(root, level, ty))
    }

    pub(super) fn bind_row_or_report_infinite(
        &mut self,
        var: u32,
        row: Row,
        origin: CtOrigin,
    ) -> bool {
        let level = self.store.level(var);
        if self.occurs_and_adjust_row_var(var, level, &row) {
            let ty = Ty::Record(row);
            let rendered = self.store.render(&ty);
            self.errors
                .push((TypeError::InfiniteType { ty: rendered }, origin.node));
            return false;
        }
        self.store.bind(var, VarValue::Row(row));
        true
    }

    /// The shared skeleton of row and effect-row unification (Leijen 2005 §3,
    /// and its effect-label-set specialization, Koka). The decision — which
    /// tail absorbs which side's leftovers, when to mint a fresh shared tail,
    /// when a mismatch is unavoidable — depends only on the flattened tails
    /// and whether each side has leftovers, never on their contents. So both
    /// kinds share this match; callers supply only the per-kind operations.
    ///
    /// `bind` returns false to abort (a row's occurs check failed); `unify`
    /// has then already reported, so the whole unification returns success.
    #[allow(clippy::too_many_arguments)]
    fn unify_row_like<P>(
        &mut self,
        only_a: P,
        only_b: P,
        ta: FlatTail,
        tb: FlatTail,
        is_empty: impl Fn(&P) -> bool,
        fresh_tail: impl Fn(&mut Self, Level) -> u32,
        mut bind: impl FnMut(&mut Self, u32, P, TailSpec) -> bool,
        mut mismatch: impl FnMut(&mut Self),
    ) -> bool {
        match (ta, tb) {
            (FlatTail::Var(x), FlatTail::Var(y)) if self.store.find(x) == self.store.find(y) => {
                // Same tail on both sides: the leftovers must already agree
                // (e.g. with set semantics, s1 ∪ t = s2 ∪ t has no solution
                // for t we could pick without guessing).
                if !is_empty(&only_a) || !is_empty(&only_b) {
                    mismatch(self);
                }
            }
            (FlatTail::Var(x), FlatTail::Var(y)) => {
                match (self.is_touchable(x), self.is_touchable(y)) {
                    (true, true) => {
                        let level = self.store.level(x).min(self.store.level(y));
                        let fresh = fresh_tail(self, level);
                        if !bind(self, x, only_b, TailSpec::Var(fresh)) {
                            return true;
                        }
                        if !bind(self, y, only_a, TailSpec::Var(fresh)) {
                            return true;
                        }
                    }
                    (true, false) if is_empty(&only_a) => {
                        if !bind(self, x, only_b, TailSpec::Var(y)) {
                            return true;
                        }
                    }
                    (false, true) if is_empty(&only_b) => {
                        if !bind(self, y, only_a, TailSpec::Var(x)) {
                            return true;
                        }
                    }
                    _ => return false,
                }
            }
            (FlatTail::Var(x), FlatTail::None) => {
                if !self.is_touchable(x) {
                    return false;
                }
                if !is_empty(&only_a) {
                    mismatch(self);
                    return true;
                }
                if !bind(self, x, only_b, TailSpec::Closed) {
                    return true;
                }
            }
            (FlatTail::None, FlatTail::Var(y)) => {
                if !self.is_touchable(y) {
                    return false;
                }
                if !is_empty(&only_b) {
                    mismatch(self);
                    return true;
                }
                if !bind(self, y, only_a, TailSpec::Closed) {
                    return true;
                }
            }
            (FlatTail::None, FlatTail::None) => {
                if !is_empty(&only_a) || !is_empty(&only_b) {
                    mismatch(self);
                }
            }
            (FlatTail::Param(p), FlatTail::Param(q)) => {
                if p != q || !is_empty(&only_a) || !is_empty(&only_b) {
                    mismatch(self);
                }
            }
            // Rigid tail vs variable tail: the variable side absorbs the
            // rigid tail. Sound only when the rigid side already covers the
            // other side's leftovers; we cannot look inside a rigid row.
            (FlatTail::Param(p), FlatTail::Var(y)) => {
                if !self.is_touchable(y) {
                    return false;
                }
                if !is_empty(&only_b) {
                    mismatch(self);
                    return true;
                }
                if !bind(self, y, only_a, TailSpec::Param(p)) {
                    return true;
                }
            }
            (FlatTail::Var(x), FlatTail::Param(q)) => {
                if !self.is_touchable(x) {
                    return false;
                }
                if !is_empty(&only_a) {
                    mismatch(self);
                    return true;
                }
                if !bind(self, x, only_b, TailSpec::Param(q)) {
                    return true;
                }
            }
            (FlatTail::Param(_), FlatTail::None) | (FlatTail::None, FlatTail::Param(_)) => {
                mismatch(self);
            }
        }
        true
    }

    /// Multiset difference of two flattened entry lists: structurally
    /// equal occurrences (label AND instantiation, zonked) cancel; the
    /// rest are each side's leftovers. Entries never unify their
    /// instantiation arguments against each other — occurrences are inert
    /// until a handler's label filter discharges them or a closed row
    /// rejects them (docs/generic-effects-plan.md).
    fn diff_effect_entries(
        &mut self,
        ea: Vec<EffectEntry>,
        eb: Vec<EffectEntry>,
    ) -> (Vec<EffectEntry>, Vec<EffectEntry>) {
        let zonk = |solver: &mut Self, entries: Vec<EffectEntry>| -> Vec<EffectEntry> {
            entries
                .into_iter()
                .map(|entry| EffectEntry {
                    effect: entry.effect,
                    args: entry
                        .args
                        .iter()
                        .map(|ty| solver.store.zonk_ty(ty))
                        .collect(),
                })
                .collect()
        };
        let ea = zonk(self, ea);
        let eb = zonk(self, eb);
        let mut remaining_b: Vec<Option<EffectEntry>> = eb.into_iter().map(Some).collect();
        let mut only_a: Vec<EffectEntry> = vec![];
        for entry in ea {
            match remaining_b
                .iter_mut()
                .find(|slot| slot.as_ref() == Some(&entry))
            {
                Some(slot) => {
                    slot.take();
                }
                None => only_a.push(entry),
            }
        }
        let only_b: Vec<EffectEntry> = remaining_b.into_iter().flatten().collect();
        (only_a, only_b)
    }

    /// Effect-row unification over inert entry multisets: structurally
    /// equal occurrences cancel; each side's leftovers flow into the other
    /// side's tail via a fresh shared tail (Leijen-style row rewriting;
    /// entries with empty argument vectors behave exactly like the old
    /// label set).
    pub(super) fn unify_eff(&mut self, a: &EffectRow, b: &EffectRow, origin: CtOrigin) -> bool {
        let (ea, ta) = self.store.flatten_eff(a);
        let (eb, tb) = self.store.flatten_eff(b);
        let (only_a, only_b) = self.diff_effect_entries(ea, eb);

        self.unify_row_like(
            only_a,
            only_b,
            ta,
            tb,
            |effects: &Vec<EffectEntry>| effects.is_empty(),
            |solver, level| solver.store.fresh_eff(level, origin.node).0,
            |solver, var, effects, spec| {
                let tail = match spec {
                    TailSpec::Var(v) => Some(EffTail::Var(EffVar(v))),
                    TailSpec::Closed => None,
                    TailSpec::Param(p) => Some(EffTail::Param(p)),
                };
                solver
                    .store
                    .bind(var, VarValue::Eff(EffectRow::new(effects, tail)));
                true
            },
            |solver| {
                // Occurrences with nowhere to go — spilling into a CLOSED
                // row — are unhandled: no handler stands between the
                // perform and the top level. Anything else is an ordinary
                // row mismatch.
                let (ea, ta) = solver.store.flatten_eff(a);
                let (eb, tb) = solver.store.flatten_eff(b);
                let (extra_a, extra_b) = solver.diff_effect_entries(ea, eb);
                let mut unhandled: Vec<Symbol> = vec![];
                if matches!(ta, FlatTail::None) {
                    unhandled.extend(extra_b.iter().map(|entry| entry.effect));
                }
                if matches!(tb, FlatTail::None) {
                    unhandled.extend(extra_a.iter().map(|entry| entry.effect));
                }
                unhandled.sort();
                unhandled.dedup();
                if unhandled.is_empty() {
                    let expected = solver.store.render_eff(a);
                    let found = solver.store.render_eff(b);
                    solver.errors.push((
                        TypeError::Mismatch {
                            expected,
                            found,
                            reason: origin.reason,
                        },
                        origin.node,
                    ));
                }
                for effect in unhandled {
                    solver.errors.push((
                        TypeError::UnhandledEffect {
                            effect: effect.to_string(),
                        },
                        origin.node,
                    ));
                }
            },
        )
    }

    /// Record-row unification by decomposition (Leijen 2005 §3): fields
    /// common to both sides unify pointwise; each side's leftover fields
    /// flow into the other side's tail.
    pub(super) fn unify_rows(
        &mut self,
        a: &Row,
        b: &Row,
        origin: CtOrigin,
        worklist: &mut Vec<Constraint>,
    ) -> bool {
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

        self.unify_row_like(
            only_a,
            only_b,
            ta,
            tb,
            |fields| fields.is_empty(),
            |solver, level| solver.store.fresh_row(level, origin.node).0,
            |solver, var, fields, spec| {
                let tail = match spec {
                    TailSpec::Var(v) => Some(RowTail::Var(RowVar(v))),
                    TailSpec::Closed => None,
                    TailSpec::Param(p) => Some(RowTail::Param(p)),
                };
                // Occurs check on row tails: a tail must not appear in the row
                // it absorbs (Leijen 2005's termination condition).
                solver.bind_row_or_report_infinite(var, Row { fields, tail }, origin)
            },
            |solver| {
                let expected = solver.store.render(&Ty::Record(a.clone()));
                let found = solver.store.render(&Ty::Record(b.clone()));
                solver.errors.push((
                    TypeError::Mismatch {
                        expected,
                        found,
                        reason: origin.reason,
                    },
                    origin.node,
                ));
            },
        )
    }
}
