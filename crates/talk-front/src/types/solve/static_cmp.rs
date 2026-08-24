use super::*;

/// Deterministic, resource-bounded linear-integer entailment for static
/// predicates (ADR 0035 §4). Facts and goal are affine forms read as
/// `e >= 0`; the goal is proven by refuting its negation (`goal <= -1`)
/// with Fourier–Motzkin elimination over the affine atoms. Rational
/// refutation is sound for the integers, so a proof here is a proof;
/// failures (including resource-limit hits) are conservative rejections —
/// the checker never assumes a predicate.
const MAX_INEQUALITIES: usize = 512;

pub(super) fn entails_static(facts: &[StaticInt], goal: &StaticInt) -> bool {
    let negated = goal.scale(&(-1).into()).sub(&StaticInt::constant(1));
    let mut system: Vec<StaticInt> = facts.to_vec();
    system.push(negated);

    loop {
        let Some(atom) = system
            .iter()
            .flat_map(|e| e.terms.iter().map(|(atom, _)| *atom))
            .min()
        else {
            break;
        };
        let (with, without): (Vec<_>, Vec<_>) = system
            .into_iter()
            .partition(|e| e.terms.iter().any(|(a, _)| *a == atom));
        let mut next = without;
        let (pos, neg): (Vec<_>, Vec<_>) =
            with.into_iter().partition(|e| coeff_of(e, atom) > 0.into());
        // Pos-only or neg-only rows impose no joint bound on the atom and
        // drop; each pos/neg pair combines into an atom-free consequence.
        for p in &pos {
            for n in &neg {
                let a = coeff_of(p, atom);
                let b = coeff_of(n, atom);
                next.push(p.scale(&-b).add(&n.scale(&a)));
                if next.len() > MAX_INEQUALITIES {
                    return false;
                }
            }
        }
        system = next;
    }

    system.iter().any(|e| e.constant < 0.into())
}

fn coeff_of(e: &StaticInt, atom: StaticAtom) -> num_bigint::BigInt {
    e.terms
        .iter()
        .find(|(a, _)| *a == atom)
        .map(|(_, coeff)| coeff.clone())
        .unwrap_or_else(|| 0.into())
}

impl<'s> Solver<'s> {
    /// Attempt a static ordering wanted (equality delegates to
    /// unification in the dispatch). Closed forms evaluate; rigid forms
    /// are checked against the givens plus the ambient nonnegativity
    /// axiom (every static `Int` parameter carries an implicit `0 <= N`
    /// given — ADR 0035 §2); forms still holding metavariables defer
    /// until the final pass.
    pub(super) fn try_static_cmp(
        &mut self,
        op: StaticCmpOp,
        lhs: Ty,
        rhs: Ty,
        origin: CtOrigin,
    ) -> Option<Constraint> {
        let lhs_z = self.store.zonk_ty(&lhs);
        let rhs_z = self.store.zonk_ty(&rhs);
        if matches!(lhs_z, Ty::Error) || matches!(rhs_z, Ty::Error) {
            return None;
        }
        let (Some(lhs_aff), Some(rhs_aff)) =
            (StaticInt::from_ty(&lhs_z), StaticInt::from_ty(&rhs_z))
        else {
            // A non-index operand: the kind error was reported where the
            // operand was formed.
            self.report_unproven_static(op, &lhs_z, &rhs_z, origin);
            return None;
        };
        // Goal: rhs - lhs - slack >= 0 (slack 1 for <, 0 for <=).
        let slack = StaticInt::constant(match op {
            StaticCmpOp::Lt => 1,
            StaticCmpOp::Le | StaticCmpOp::Eq => 0,
        });
        let goal = rhs_aff.sub(&lhs_aff).sub(&slack);
        if let Some(constant) = goal.as_constant() {
            if *constant < 0.into() {
                self.report_unproven_static(op, &lhs_z, &rhs_z, origin);
            }
            return None;
        }
        if !self.defaulting
            && goal
                .terms
                .iter()
                .any(|(atom, _)| matches!(atom, StaticAtom::Var(_)))
        {
            return Some(Constraint::StaticCmp {
                op,
                lhs: lhs_z,
                rhs: rhs_z,
                origin,
            });
        }
        let facts = self.static_facts(&goal);
        if static_cmp::entails_static(&facts, &goal) {
            return None;
        }
        self.report_unproven_static(op, &lhs_z, &rhs_z, origin);
        None
    }

    /// The fact set for one entailment: every static ordering given as an
    /// `e >= 0` row, plus `0 <= p` for each rigid static `Int` parameter
    /// mentioned anywhere (nonnegativity is a formation invariant).
    pub(super) fn static_facts(&self, goal: &StaticInt) -> Vec<StaticInt> {
        let mut facts: Vec<StaticInt> = vec![];
        for given in &self.givens {
            let Predicate::StaticCmp { op, lhs, rhs } = given else {
                continue;
            };
            let (Some(lhs), Some(rhs)) = (StaticInt::from_ty(lhs), StaticInt::from_ty(rhs)) else {
                continue;
            };
            let slack = StaticInt::constant(match op {
                StaticCmpOp::Lt => 1,
                StaticCmpOp::Le | StaticCmpOp::Eq => 0,
            });
            let fact = rhs.sub(&lhs).sub(&slack);
            // Equality contributes both directions.
            if matches!(op, StaticCmpOp::Eq) {
                facts.push(fact.scale(&(-1).into()));
            }
            facts.push(fact);
        }
        let mut atoms: Vec<StaticAtom> = goal
            .terms
            .iter()
            .chain(facts.iter().flat_map(|fact| fact.terms.iter()))
            .map(|(atom, _)| *atom)
            .collect();
        atoms.sort();
        atoms.dedup();
        // Every rigid atom inside an affine form IS a static Int
        // parameter by construction (formation kind-checks operands), so
        // the nonnegativity axiom needs no registry lookup.
        for atom in atoms {
            if matches!(atom, StaticAtom::Param(_)) {
                facts.push(StaticInt::atom(atom));
            }
        }
        facts
    }

    fn report_unproven_static(&mut self, op: StaticCmpOp, lhs: &Ty, rhs: &Ty, origin: CtOrigin) {
        let predicate = Predicate::StaticCmp {
            op,
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        }
        .render_mono();
        self.errors.push((
            TypeError::UnprovenStaticPredicate { predicate },
            origin.node,
        ));
    }
}
