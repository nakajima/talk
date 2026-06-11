//! Free variables as a lazily computed, memoized least fixed point —
//! exactly the framework of Leißa & Griebler §3.1/§3.1.1:
//!
//!   fv(ℓ) = LV(body) ∪ ⋃_{m ∈ LF(body)} FV(m)  \  {var ℓ}      (Eqs. 7–10)
//!
//! with the mark/run iteration scheme: `mark = 0` invalid; `mark = run−1`
//! value from the previous pass; `mark = run` cyclic dependency in the
//! current pass (return the partial set); anything else: memoized and
//! sound. A new query bumps `run` by 2; each subsequent pass within the
//! query bumps it by 1 (the paper's worked example: runs 4, 5, 6). The
//! iteration count is bounded by the loop-connectedness d(G) + 2 (Kam &
//! Ullman, JACM 1976); acyclic queries terminate after one pass (the
//! paper's fast path). Invalidation is handled by `Program::invalidate`.

use crate::lambda_g::program::{Label, Program};
use crate::lambda_g::sets::SetId;

impl Program {
    /// FV_P(ℓ), memoized (paper Eq. 7–10 + §3.1.1).
    pub fn fv(&mut self, label: Label) -> SetId {
        if self.funcs[label.0 as usize].mark != 0 {
            return self.funcs[label.0 as usize].fv;
        }

        // New fixed-point computation: run += 2 distinguishes this query's
        // passes from any earlier marks.
        self.run += 2;
        loop {
            let run = self.run;
            let mut changed = false;
            let mut cyclic = false;
            self.fv_visit(label, run, &mut changed, &mut cyclic);
            if !cyclic || !changed {
                // Acyclic: one pass is sound. Cyclic: stop at the pass that
                // reached the fixed point (no set changed).
                break;
            }
            // Next pass within the same query.
            self.run += 1;
        }
        self.funcs[label.0 as usize].fv
    }

    fn fv_visit(&mut self, label: Label, run: u64, changed: &mut bool, cyclic: &mut bool) -> SetId {
        let mark = self.funcs[label.0 as usize].mark;
        if mark == run {
            // Cyclic dependency: yield the partial set accumulated so far
            // (case 3).
            *cyclic = true;
            return self.funcs[label.0 as usize].fv;
        }
        if mark != 0 && mark != run - 1 {
            // Valid memoized set from an earlier, completed query (case 4).
            return self.funcs[label.0 as usize].fv;
        }
        // Case 1 (invalid) or case 2 (previous pass): mark with the current
        // run and (re)compute.
        if mark == 0 {
            self.funcs[label.0 as usize].fv = SetId::EMPTY;
        }
        self.funcs[label.0 as usize].mark = run;

        let Some(body) = self.funcs[label.0 as usize].body else {
            // Unset body: fv = ∅ (paper Eq. 9).
            return SetId::EMPTY;
        };

        let lv = self.expr(body).lv;
        let lf = self.expr(body).lf;
        let mut acc = lv;
        for m in self.set_labels(lf) {
            let sub = self.fv_visit(m, run, changed, cyclic);
            acc = self.sets.union(acc, sub);
        }
        acc = self.sets.remove(acc, label);

        if acc != self.funcs[label.0 as usize].fv {
            *changed = true;
            self.funcs[label.0 as usize].fv = acc;
        }
        acc
    }

    /// Free variables of an arbitrary expression (paper Eq. 8):
    /// LV(e) ∪ ⋃ FV(LF(e)). Used by substitution's disjointness test.
    pub fn expr_fv(&mut self, e: crate::lambda_g::expr::ExprId) -> SetId {
        let lv = self.expr(e).lv;
        let lf = self.expr(e).lf;
        let mut acc = lv;
        for m in self.set_labels(lf) {
            let sub = self.fv(m);
            acc = self.sets.union(acc, sub);
        }
        acc
    }
}
