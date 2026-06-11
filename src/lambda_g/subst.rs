//! Dependency-aware substitution and β-reduction (Leißa & Griebler
//! §3.3–3.4, Eqs. 13–18 and Rule β). The central property: an expression is
//! rewritten only if its free variables intersect the substitution domain
//! (Eq. 14) — so β-reducing a loop header specializes exactly the functions
//! that depend on it (§2.2's peeling example), with no dominator tree and
//! no block floating. New functions are created with unset bodies first so
//! recursion ties its own knot (Eq. 18). Well-formedness and typing are
//! preserved (paper Lemma 3, Thms. 2–3 — Lean-verified).

use rustc_hash::FxHashMap;

use crate::lambda_g::expr::{ExprId, ExprKind};
use crate::lambda_g::program::{Label, Program};
use crate::lambda_g::sets::SetId;

pub struct Subst {
    /// V: variables → replacement expressions.
    v: FxHashMap<Label, ExprId>,
    /// dom(V) as a set, for the Eq. 14 disjointness test.
    vdom: SetId,
    /// F: functions → their rewritten counterparts (Eq. 17).
    f: FxHashMap<Label, Label>,
}

impl Subst {
    pub fn single(program: &mut Program, var: Label, replacement: ExprId) -> Self {
        let vdom = program.sets.singleton(var);
        let mut v = FxHashMap::default();
        v.insert(var, replacement);
        Subst {
            v,
            vdom,
            f: FxHashMap::default(),
        }
    }
}

impl Program {
    /// ⟨⟨V, F, P, e⟩⟩ (paper Eqs. 14–18).
    pub fn substitute(&mut self, subst: &mut Subst, e: ExprId) -> ExprId {
        // Eq. 14: untouched when FV(e) ∩ dom(V) = ∅.
        let efv = self.expr_fv(e);
        if !self.sets.intersects(efv, subst.vdom) {
            return e;
        }

        match self.expr(e).kind.clone() {
            // Eq. 16: a free variable's substitute comes from V (it must be
            // present, since FV(var ℓ) = {ℓ} intersected dom(V)).
            ExprKind::Var(l) => subst.v[&l],

            // Eq. 17 / Eq. 18.
            ExprKind::Func(l) => {
                if let Some(&l2) = subst.f.get(&l) {
                    return self.func_ref(l2);
                }
                let (dom, cod) = (self.dom(l), self.cod(l));
                let fresh_name = format!("{}'", self.name(l));
                let l2 = self.func(&fresh_name, dom, cod);
                // Redirect old variable and function to the new ones BEFORE
                // rewriting the body: the unset body of ℓ′ resolves
                // recursion (Eq. 18).
                let v2 = self.var(l2);
                subst.v.insert(l, v2);
                let singleton = self.sets.singleton(l);
                subst.vdom = self.sets.union(subst.vdom, singleton);
                subst.f.insert(l, l2);
                if let Some(body) = self.body(l) {
                    let body2 = self.substitute(subst, body);
                    self.set_body(l2, body2);
                }
                self.func_ref(l2)
            }

            ExprKind::App(a, b) => {
                let a2 = self.substitute(subst, a);
                let b2 = self.substitute(subst, b);
                self.app(a2, b2)
            }
            ExprKind::Tuple(items) => {
                let rebuilt: Vec<ExprId> =
                    items.iter().map(|i| self.substitute(subst, *i)).collect();
                self.tuple(&rebuilt)
            }
            ExprKind::Extract(inner, index) => {
                let inner2 = self.substitute(subst, inner);
                self.extract(inner2, index)
            }
            ExprKind::PrimOp(op, args, ty) => {
                let rebuilt: Vec<ExprId> =
                    args.iter().map(|a| self.substitute(subst, *a)).collect();
                self.primop(op, &rebuilt, ty)
            }
            // Constants have no free variables; Eq. 14 already returned.
            ExprKind::Const(_) => e,
        }
    }

    /// Rule β: P, ℓ e_v →_β P′, e_b′ — the one operation that subsumes
    /// inlining, monomorphic specialization, and loop peeling/unrolling
    /// (paper Table 2).
    pub fn beta_reduce(&mut self, label: Label, arg: ExprId) -> ExprId {
        let Some(body) = self.body(label) else {
            // β on an unset body is a caller bug (Progress assumes a set
            // body); surface loudly.
            unreachable!("β-reduction of a function with an unset body");
        };
        let mut subst = Subst::single(self, label, arg);
        self.substitute(&mut subst, body)
    }
}
