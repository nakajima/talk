//! Grammar-restricted program fuzzer for the ownership system (8.4/M8 of
//! docs/ownership-soundness-plan.md; the differential-testing extension of
//! the confidence plan's Track A2, McKeeman 1998).
//!
//! A small generator walks a typed grammar over the ownership-relevant
//! surface — owned Strings via concatenation, borrows (`&` annotations and
//! borrow-default params), `consume` params, loops with break/continue at
//! depth, closures and trailing blocks, effect handlers (resume AND abort),
//! matches (literal arms, binder arms, borrowed and rvalue scrutinees,
//! nesting), Array push/set/clone CoW shapes, `'heap` structs, user
//! `Deinit` with droppable fields, generic consumes instantiated at
//! droppable types, and early returns — weighted toward the COMPOSITIONS
//! every recent ownership bug lived in (closure x temp, borrowed receiver x
//! method x loop, handler x consume, clone x push).
//!
//! The oracle is exactly the stack the soundness plan built, reused via the
//! ordinary driver entry points: compiles => free-balance verifier passes
//! (asserted inside `Driver::lower` in test builds) => both engines agree
//! on result and stdout => zero live allocations at exit (the evaluator and
//! VM leak fences inside `eval_with_output`/`run_vm_with_output`). Checker
//! REJECTIONS are expected for some compositions — that is the reject path
//! working; the oracle applies only to programs that compile, and the CI
//! test asserts a floor on the compile-rate so the generator can't rot into
//! testing nothing.
//!
//! Deterministic and seeded: a fixed default base seed in CI, per-program
//! seeds derived by splitmix64, statements drawn from a hand-rolled
//! xorshift64* (no wall clock, no ambient entropy, no external PRNG crate).
//! Exploratory runs override via env:
//!
//! ```text
//! TALK_FUZZ_SEED=42 TALK_FUZZ_COUNT=5000 cargo test fuzz_ownership -- --nocapture
//! ```
//!
//! On a failure the harness greedily shrinks (statement removal + scope
//! unwrapping, re-running the oracle) to a minimal failing program and
//! writes it with its seed to `target/fuzz/`; shrunk repros become corpus
//! entries in tests/programs/ once fixed (plan 8.4).

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use crate::compiling::driver::{Driver, DriverConfig, Source};
    use crate::lambda_g::eval::EvalValue;
    use crate::vm::interp::Value;

    /// Fixed CI base seed. Chosen once, arbitrarily; changing it is a
    /// deliberate act (it changes which programs CI explores).
    const DEFAULT_SEED: u64 = 0x7A1C_5EED;
    /// Default program count: sized so the suite pays a few seconds
    /// (~115ms per program through compile + verify + both engines;
    /// measured 2026-07-12: 200 programs cost 22s, 60 cost ~7s).
    const DEFAULT_COUNT: usize = 60;
    /// Program indices excluded from the DEFAULT run only — each trips a
    /// real, currently-open finding (fuzzer findings F-B/F-C, plan 8.4
    /// notes; shrunk repros in target/fuzz/ and this module's report):
    ///
    /// - F-B: an abort through a function-VALUE call (`fn()` inside
    ///   `run_twice`) skips the unwind for frames above it, leaking the
    ///   installing frame's owned param — the plan's documented R9
    ///   residual, now with a runnable repro. Trips index 67.
    /// - F-C: an aborting perform whose argument is an owned temp
    ///   (`'oops("burn" + "!")`) leaks that temp on both engines even
    ///   with no other owned values live. Trips index 155.
    ///
    /// (F-A — clone temps in borrow position never dropped — is FIXED:
    /// `ExprKind::Clone` rvalues materialize temps with `TemporaryEnd`
    /// candidates, and the temp substituter no longer carries retain
    /// marks onto operand references. Pinned by the `clone_*` tests in
    /// vm_tests; its indices 43/87/127/149/152/173/197 are unskipped.)
    ///
    /// Delete an index once its finding is fixed; the run goes red on the
    /// regression otherwise. Indices past DEFAULT_COUNT keep default-seed
    /// exploratory runs (`TALK_FUZZ_COUNT=200`) clean of KNOWN findings.
    const DEFAULT_SKIPS: &[usize] = &[67, 155];
    /// Compile-rate floor: below this the generator is testing too little
    /// of the accept path and the grammar must be tightened.
    const COMPILE_RATE_FLOOR: f64 = 0.6;
    /// Oracle-call budget per shrink, bounding worst-case failure cost.
    const SHRINK_BUDGET: usize = 400;

    // ------------------------------------------------------------------
    // PRNG — xorshift64* (Vigna, "An experimental exploration of
    // Marsaglia's xorshift generators", 2016). Distribution quality is
    // irrelevant here; determinism and zero dependencies are the point.
    // ------------------------------------------------------------------

    struct Rng(u64);

    impl Rng {
        fn new(seed: u64) -> Self {
            // xorshift has a zero fixed point; nudge it off.
            Self(if seed == 0 {
                0x9E37_79B9_7F4A_7C15
            } else {
                seed
            })
        }

        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }

        fn range(&mut self, lo: usize, hi: usize) -> usize {
            lo + self.below(hi - lo + 1)
        }

        fn chance(&mut self, pct: u64) -> bool {
            self.next() % 100 < pct
        }

        fn pick<'a, T>(&mut self, options: &'a [T]) -> &'a T {
            &options[self.below(options.len())]
        }
    }

    /// splitmix64 — derives independent per-program seeds from the base
    /// seed, so program N is reproducible without generating 0..N-1.
    fn splitmix64(mut z: u64) -> u64 {
        z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn derive_seed(base: u64, index: u64) -> u64 {
        splitmix64(base ^ splitmix64(index))
    }

    // ------------------------------------------------------------------
    // Program tree — shrinkable statement structure. `Leaf` is verbatim
    // lines (relative tabs allowed); `Scope` is a braced region whose
    // `fixed` lines are scaffolding the shrinker must not touch (loop
    // counter increments — removing one would un-terminate the loop).
    // ------------------------------------------------------------------

    #[derive(Clone)]
    enum Node {
        Leaf(String),
        Scope {
            head: String,
            fixed: Vec<String>,
            body: Vec<Node>,
            tail: String,
        },
    }

    fn push_lines(text: &str, depth: usize, out: &mut String) {
        for line in text.split('\n') {
            for _ in 0..depth {
                out.push('\t');
            }
            out.push_str(line);
            out.push('\n');
        }
    }

    fn render_into(nodes: &[Node], depth: usize, out: &mut String) {
        for node in nodes {
            match node {
                Node::Leaf(text) => push_lines(text, depth, out),
                Node::Scope {
                    head,
                    fixed,
                    body,
                    tail,
                } => {
                    push_lines(head, depth, out);
                    for line in fixed {
                        push_lines(line, depth + 1, out);
                    }
                    render_into(body, depth + 1, out);
                    push_lines(tail, depth, out);
                }
            }
        }
    }

    fn render(nodes: &[Node]) -> String {
        let mut out = String::new();
        render_into(nodes, 0, &mut out);
        out
    }

    // ------------------------------------------------------------------
    // Generator — typed grammar with a scope stack, so most programs are
    // type- and ownership-correct by construction. A small "spice" rate
    // deliberately violates the tracking (consume through a borrow, mutate
    // an iterated array) to keep the reject path exercised.
    // ------------------------------------------------------------------

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum VTy {
        Int,
        Str,
        Arr,
        Loud,
        Heap,
    }

    #[derive(Clone)]
    struct Var {
        name: String,
        ty: VTy,
        /// Passed to a consume param (or otherwise unusable from here on).
        consumed: bool,
        /// Borrowed storage: `&` params, borrow-default params, for-loop
        /// binders. Excluded from consume/mutate productions (mostly).
        borrowed: bool,
        /// Locally `let`-declared, so reassignment is legal.
        assignable: bool,
    }

    struct Frame {
        vars: Vec<Var>,
        /// Closure/function boundary: consume productions do not reach
        /// past a barrier (a consume of a captured outer value is almost
        /// always a rejection — generated only as spice).
        barrier: bool,
    }

    #[derive(Clone, Copy)]
    enum PKind {
        IntP,
        StrDefault,
        StrConsume,
        StrBorrow,
        ArrDefault,
        ArrConsume,
    }

    #[derive(Clone)]
    struct FnSig {
        name: String,
        params: Vec<PKind>,
    }

    #[derive(Clone, Copy)]
    struct Ctx {
        depth: usize,
        in_loop: bool,
        can_return: bool,
        handles_oops: bool,
        handles_ask: bool,
    }

    const STR_LITS: &[&str] = &["a", "b", "ok", "zed", "hey", "q", "w"];

    struct Gen {
        rng: Rng,
        fresh: usize,
        frames: Vec<Frame>,
        funcs: Vec<FnSig>,
    }

    impl Gen {
        fn new(seed: u64) -> Self {
            Self {
                rng: Rng::new(seed),
                fresh: 0,
                frames: vec![],
                funcs: vec![],
            }
        }

        fn fresh(&mut self, prefix: &str) -> String {
            self.fresh += 1;
            format!("{prefix}{}", self.fresh)
        }

        fn declare(&mut self, name: &str, ty: VTy) {
            self.declare_full(name, ty, false, true);
        }

        fn declare_full(&mut self, name: &str, ty: VTy, borrowed: bool, assignable: bool) {
            self.frames.last_mut().expect("frame").vars.push(Var {
                name: name.to_string(),
                ty,
                consumed: false,
                borrowed,
                assignable,
            });
        }

        /// A readable (borrow-position) variable of `ty`, any scope.
        fn usable(&mut self, ty: VTy) -> Option<String> {
            let names: Vec<String> = self
                .frames
                .iter()
                .flat_map(|f| f.vars.iter())
                .filter(|v| v.ty == ty && !v.consumed)
                .map(|v| v.name.clone())
                .collect();
            if names.is_empty() {
                None
            } else {
                Some(self.rng.pick(&names).clone())
            }
        }

        /// A mutable (non-borrowed) variable of `ty` — the target set for
        /// `push`/`set`, which need `&mut` and reject borrow-default
        /// params.
        fn mutable(&mut self, ty: VTy) -> Option<String> {
            let names: Vec<String> = self
                .frames
                .iter()
                .flat_map(|f| f.vars.iter())
                .filter(|v| v.ty == ty && !v.consumed && !v.borrowed)
                .map(|v| v.name.clone())
                .collect();
            if names.is_empty() {
                None
            } else {
                Some(self.rng.pick(&names).clone())
            }
        }

        /// A reassignable local of `ty`.
        fn assignable(&mut self, ty: VTy) -> Option<String> {
            let names: Vec<String> = self
                .frames
                .iter()
                .flat_map(|f| f.vars.iter())
                .filter(|v| v.ty == ty && !v.consumed && !v.borrowed && v.assignable)
                .map(|v| v.name.clone())
                .collect();
            if names.is_empty() {
                None
            } else {
                Some(self.rng.pick(&names).clone())
            }
        }

        /// Pick and mark a consumable variable of `ty`. Normally only
        /// non-borrowed vars up to the nearest barrier; ~10% "spice" picks
        /// from anywhere including borrowed storage — deliberately feeding
        /// the reject path (move-out-of-borrow, loop-carried moves,
        /// consume-under-re-entrant-body).
        fn consumable(&mut self, ty: VTy) -> Option<String> {
            let spice = self.rng.chance(10);
            let mut candidates: Vec<(usize, usize)> = vec![];
            for (fi, frame) in self.frames.iter().enumerate().rev() {
                for (vi, var) in frame.vars.iter().enumerate() {
                    if var.ty == ty && !var.consumed && (spice || !var.borrowed) {
                        candidates.push((fi, vi));
                    }
                }
                if frame.barrier && !spice {
                    break;
                }
            }
            if candidates.is_empty() {
                return None;
            }
            let (fi, vi) = *self.rng.pick(&candidates);
            let var = &mut self.frames[fi].vars[vi];
            var.consumed = true;
            Some(var.name.clone())
        }

        fn str_lit(&mut self) -> String {
            format!("\"{}\"", self.rng.pick(STR_LITS))
        }

        /// An owned, heap-allocating String expression.
        fn str_expr(&mut self) -> String {
            let mut options = vec![0u32];
            if self.usable(VTy::Str).is_some() {
                options.extend([1, 2]);
            }
            match *self.rng.pick(&options) {
                1 => {
                    let s = self.usable(VTy::Str).expect("checked");
                    let lit = self.str_lit();
                    format!("{s} + {lit}")
                }
                2 => {
                    let s = self.usable(VTy::Str).expect("checked");
                    format!("{s}.clone()")
                }
                _ => {
                    let a = self.str_lit();
                    let b = self.str_lit();
                    format!("{a} + {b}")
                }
            }
        }

        fn int_expr(&mut self) -> String {
            let mut options: Vec<String> = vec![format!("{}", self.rng.below(9))];
            if let Some(n) = self.usable(VTy::Int) {
                options.push(n.clone());
                options.push(format!("{n} + {}", 1 + self.rng.below(3)));
            }
            if let Some(s) = self.usable(VTy::Str) {
                options.push(format!("{s}.byte_count"));
                options.push(format!("blen({s})"));
            }
            if let Some(a) = self.usable(VTy::Arr) {
                options.push(format!("{a}.count"));
            }
            if let Some(l) = self.usable(VTy::Loud) {
                options.push(format!("{l}.s.byte_count"));
            }
            if let Some(h) = self.usable(VTy::Heap) {
                options.push(format!("{h}.n"));
            }
            self.rng.pick(&options).clone()
        }

        fn bool_expr(&mut self) -> String {
            let lhs = self
                .usable(VTy::Int)
                .unwrap_or_else(|| format!("{}", self.rng.below(5)));
            let op = *self.rng.pick(&[">", "==", "<"]);
            format!("{lhs} {op} {}", self.rng.below(4))
        }

        // ----- statements ------------------------------------------------

        fn block(&mut self, ctx: Ctx, min: usize, max: usize) -> Vec<Node> {
            let mut out = vec![];
            let count = self.rng.range(min, max);
            for _ in 0..count {
                self.stmt(ctx, &mut out);
            }
            out
        }

        fn stmt(&mut self, ctx: Ctx, out: &mut Vec<Node>) {
            // (tag, weight); gates checked per roll, with a Print fallback.
            const TABLE: &[(u32, u32)] = &[
                (0, 12), // let String
                (1, 7),  // let Array<String>
                (2, 5),  // let Loud (Deinit struct)
                (3, 4),  // let 'heap struct
                (4, 10), // print evidence
                (5, 10), // consume call
                (6, 6),  // borrow call
                (7, 8),  // array push/set/clone
                (8, 5),  // string/int accumulate (mutation)
                (9, 6),  // if
                (10, 6), // counter loop
                (11, 5), // for over array
                (12, 6), // match
                (13, 4), // trailing block
                (14, 4), // early exit
                (15, 4), // effectful call under installed handler
                (16, 3), // call an earlier generated function
            ];
            let total: u32 = TABLE.iter().map(|(_, w)| w).sum();
            for _attempt in 0..6 {
                let mut roll = self.rng.below(total as usize) as u32;
                let mut tag = 0;
                for (t, w) in TABLE {
                    if roll < *w {
                        tag = *t;
                        break;
                    }
                    roll -= w;
                }
                if self.try_stmt(tag, ctx, out) {
                    return;
                }
            }
            // Fallback that always applies.
            let e = self.int_expr();
            out.push(Node::Leaf(format!("print({e})")));
        }

        /// Emit statement `tag` if its guards hold; false asks for a reroll.
        fn try_stmt(&mut self, tag: u32, ctx: Ctx, out: &mut Vec<Node>) -> bool {
            let structural_ok = ctx.depth < 3;
            match tag {
                0 => {
                    let name = self.fresh("s");
                    let e = self.str_expr();
                    out.push(Node::Leaf(format!("let {name} = {e}")));
                    self.declare(&name, VTy::Str);
                }
                1 => {
                    let name = self.fresh("xs");
                    let count = self.rng.range(1, 3);
                    let elems: Vec<String> = (0..count).map(|_| self.str_expr()).collect();
                    out.push(Node::Leaf(format!("let {name} = [{}]", elems.join(", "))));
                    self.declare(&name, VTy::Arr);
                }
                2 => {
                    let name = self.fresh("l");
                    let e = self.str_expr();
                    out.push(Node::Leaf(format!("let {name} = Loud(s: {e})")));
                    self.declare(&name, VTy::Loud);
                }
                3 => {
                    let name = self.fresh("h");
                    let e = self.str_expr();
                    let n = self.rng.below(9);
                    out.push(Node::Leaf(format!("let {name} = Jar(key: {e}, n: {n})")));
                    self.declare(&name, VTy::Heap);
                }
                4 => {
                    let mut options: Vec<String> = vec![self.int_expr()];
                    if let Some(s) = self.usable(VTy::Str) {
                        options.push(s.clone());
                        options.push(format!("\"p:\" + {s}"));
                    }
                    if let Some(a) = self.usable(VTy::Arr) {
                        options.push(format!("{a}.get(0)"));
                    }
                    if let Some(l) = self.usable(VTy::Loud) {
                        options.push(format!("{l}.s"));
                    }
                    if let Some(h) = self.usable(VTy::Heap) {
                        options.push(format!("{h}.key"));
                    }
                    let arg = self.rng.pick(&options).clone();
                    out.push(Node::Leaf(format!("print({arg})")));
                }
                5 => {
                    // Consume call: eat / eat_arr / gulp (generic consume
                    // instantiated at every droppable type in the program).
                    let name = self.fresh("e");
                    let call = match self.rng.below(4) {
                        0 => {
                            let arg = self.consumable(VTy::Str).unwrap_or_else(|| self.str_expr());
                            format!("eat({arg})")
                        }
                        1 => match self.consumable(VTy::Arr) {
                            Some(arg) => format!("eat_arr({arg})"),
                            None => {
                                let e = self.str_expr();
                                format!("eat_arr([{e}])")
                            }
                        },
                        2 => match self
                            .consumable(VTy::Loud)
                            .or_else(|| self.consumable(VTy::Heap))
                        {
                            Some(arg) => format!("gulp({arg})"),
                            None => {
                                let e = self.str_expr();
                                format!("gulp(Loud(s: {e}))")
                            }
                        },
                        _ => {
                            let arg = self.consumable(VTy::Str).unwrap_or_else(|| self.str_expr());
                            format!("gulp({arg})")
                        }
                    };
                    out.push(Node::Leaf(format!("let {name} = {call}")));
                    self.declare(&name, VTy::Int);
                }
                6 => {
                    let Some(s) = self.usable(VTy::Str) else {
                        return false;
                    };
                    let name = self.fresh("b");
                    let callee = *self.rng.pick(&["blen", "dlen"]);
                    out.push(Node::Leaf(format!("let {name} = {callee}({s})")));
                    self.declare(&name, VTy::Int);
                }
                7 => match self.rng.below(3) {
                    0 => {
                        let Some(xs) = self.mutable(VTy::Arr) else {
                            return false;
                        };
                        let e = self.str_expr();
                        out.push(Node::Leaf(format!("{xs}.push({e})")));
                    }
                    1 => {
                        let Some(xs) = self.mutable(VTy::Arr) else {
                            return false;
                        };
                        let e = self.str_expr();
                        out.push(Node::Leaf(format!("{xs}.set(0, {e})")));
                    }
                    _ => {
                        let Some(xs) = self.usable(VTy::Arr) else {
                            return false;
                        };
                        let name = self.fresh("c");
                        out.push(Node::Leaf(format!("let {name} = {xs}.clone()")));
                        self.declare(&name, VTy::Arr);
                    }
                },
                8 => match self.rng.below(2) {
                    0 => {
                        let Some(s) = self.assignable(VTy::Str) else {
                            return false;
                        };
                        let lit = self.str_lit();
                        out.push(Node::Leaf(format!("{s} = {s} + {lit}")));
                    }
                    _ => {
                        let Some(n) = self.assignable(VTy::Int) else {
                            return false;
                        };
                        out.push(Node::Leaf(format!("{n} = {n} + {}", 1 + self.rng.below(3))));
                    }
                },
                9 => {
                    if !structural_ok {
                        return false;
                    }
                    let cond = self.bool_expr();
                    self.frames.push(Frame {
                        vars: vec![],
                        barrier: false,
                    });
                    let body = self.block(
                        Ctx {
                            depth: ctx.depth + 1,
                            ..ctx
                        },
                        1,
                        3,
                    );
                    self.frames.pop();
                    out.push(Node::Scope {
                        head: format!("if {cond} {{"),
                        fixed: vec![],
                        body,
                        tail: "}".into(),
                    });
                }
                10 => {
                    if !structural_ok {
                        return false;
                    }
                    let i = self.fresh("i");
                    let bound = self.rng.range(2, 3);
                    // Counter scaffold is `fixed` so shrinking can never
                    // remove the increment and un-terminate the loop.
                    // The body frame is a barrier: consuming a var from
                    // outside the loop is a loop-carried move (rejected),
                    // so it stays spice-only.
                    self.declare(&i, VTy::Int);
                    self.frames.push(Frame {
                        vars: vec![],
                        barrier: true,
                    });
                    let body = self.block(
                        Ctx {
                            depth: ctx.depth + 1,
                            in_loop: true,
                            ..ctx
                        },
                        1,
                        3,
                    );
                    self.frames.pop();
                    out.push(Node::Scope {
                        head: format!("let {i} = 0\nloop {i} < {bound} {{"),
                        fixed: vec![format!("{i} = {i} + 1")],
                        body,
                        tail: "}".into(),
                    });
                }
                11 => {
                    if !structural_ok {
                        return false;
                    }
                    let Some(xs) = self.usable(VTy::Arr) else {
                        return false;
                    };
                    // Iterating borrows the array: unless spicing the
                    // reject path, fence it off from mutation/consumption
                    // inside the body by marking it consumed for the
                    // body's duration.
                    let spice = self.rng.chance(10);
                    let mut restore = None;
                    if !spice {
                        'mark: for (fi, frame) in self.frames.iter().enumerate() {
                            for (vi, var) in frame.vars.iter().enumerate() {
                                if var.name == xs {
                                    restore = Some((fi, vi));
                                    break 'mark;
                                }
                            }
                        }
                        if let Some((fi, vi)) = restore {
                            self.frames[fi].vars[vi].consumed = true;
                        }
                    }
                    let x = self.fresh("x");
                    self.frames.push(Frame {
                        vars: vec![],
                        barrier: true,
                    });
                    self.declare_full(&x, VTy::Str, true, false);
                    let body = self.block(
                        Ctx {
                            depth: ctx.depth + 1,
                            in_loop: true,
                            ..ctx
                        },
                        1,
                        3,
                    );
                    self.frames.pop();
                    if let Some((fi, vi)) = restore {
                        self.frames[fi].vars[vi].consumed = false;
                    }
                    out.push(Node::Scope {
                        head: format!("for {x} in {xs} {{"),
                        fixed: vec![],
                        body,
                        tail: "}".into(),
                    });
                }
                12 => {
                    let name = self.fresh("m");
                    let leaf = match self.rng.below(3) {
                        0 => {
                            // Literal arms; var (borrowed) or rvalue temp
                            // scrutinee (the B8 shape). The temp comes from
                            // a declared helper — a bare `"a" + "b"`
                            // scrutinee is falsely rejected (`?N.Ret` vs
                            // String, reason Pattern: operator-call result
                            // metas never solve against literal patterns),
                            // a checker paper-cut found by this fuzzer.
                            let scrutinee = match self.usable(VTy::Str) {
                                Some(s) if self.rng.chance(70) => s,
                                Some(s) => format!("mk({s})"),
                                None => {
                                    let lit = self.str_lit();
                                    format!("mk({lit})")
                                }
                            };
                            let lit = self.str_lit();
                            let a = self.int_expr();
                            let b = self.int_expr();
                            format!(
                                "let {name} = match {scrutinee} {{\n\t{lit} -> {a},\n\t_ -> {b}\n}}"
                            )
                        }
                        1 => {
                            // Binder arm over a droppable payload; the
                            // consuming variant exercises S3 territory.
                            let o = self.fresh("o");
                            let v = self.fresh("v");
                            let payload = self.str_expr();
                            let some_arm = if self.rng.chance(40) {
                                format!("eat({v})")
                            } else {
                                format!("blen({v})")
                            };
                            format!(
                                "let {o} = Optional.some({payload})\nlet {name} = match {o} {{\n\t.some({v}) -> {some_arm},\n\t.none -> 0\n}}"
                            )
                        }
                        _ => {
                            // Nested int match in an arm.
                            let outer = self.int_expr();
                            let inner = self.int_expr();
                            let a = self.int_expr();
                            let b = self.int_expr();
                            let c = self.int_expr();
                            format!(
                                "let {name} = match {outer} {{\n\t0 -> {a},\n\t_ -> match {inner} {{\n\t\t1 -> {b},\n\t\t_ -> {c}\n\t}}\n}}"
                            )
                        }
                    };
                    out.push(Node::Leaf(leaf));
                    self.declare(&name, VTy::Int);
                }
                13 => {
                    if !structural_ok {
                        return false;
                    }
                    let name = self.fresh("t");
                    // run_twice makes the body re-entrant: a consume of a
                    // capture inside it is the S5 shape (must reject).
                    let runner = if self.rng.chance(35) {
                        "run_twice"
                    } else {
                        "run_once"
                    };
                    self.frames.push(Frame {
                        vars: vec![],
                        barrier: true,
                    });
                    let body = self.block(
                        Ctx {
                            depth: ctx.depth + 1,
                            in_loop: false,
                            can_return: false,
                            ..ctx
                        },
                        1,
                        3,
                    );
                    self.frames.pop();
                    out.push(Node::Scope {
                        head: format!("let {name} = {runner} {{"),
                        fixed: vec![],
                        body,
                        tail: "}".into(),
                    });
                    self.declare(&name, VTy::Int);
                }
                14 => {
                    let cond = self.bool_expr();
                    if ctx.in_loop {
                        let exit = *self.rng.pick(&["break", "continue"]);
                        out.push(Node::Leaf(format!("if {cond} {{\n\t{exit}\n}}")));
                    } else if ctx.can_return {
                        let val = self.int_expr();
                        out.push(Node::Leaf(format!("if {cond} {{\n\treturn {val}\n}}")));
                    } else {
                        return false;
                    }
                }
                15 => {
                    if !ctx.handles_oops && !ctx.handles_ask {
                        return false;
                    }
                    let name = self.fresh("r");
                    let use_oops = ctx.handles_oops && (!ctx.handles_ask || self.rng.chance(60));
                    let call = if use_oops {
                        if self.rng.chance(50) {
                            // consume param + abort: the discarded frame
                            // holds an owned value (ADR 0027 unwind).
                            let arg = self.consumable(VTy::Str).unwrap_or_else(|| self.str_expr());
                            format!("risky_eat({arg}, {})", self.rng.below(5))
                        } else {
                            format!("risky({})", self.rng.below(5))
                        }
                    } else {
                        format!("bonus({})", self.rng.below(5))
                    };
                    out.push(Node::Leaf(format!("let {name} = {call}")));
                    self.declare(&name, VTy::Int);
                }
                16 => {
                    if self.funcs.is_empty() {
                        return false;
                    }
                    let sig = self.rng.pick(&self.funcs).clone();
                    let name = self.fresh("g");
                    let call = self.call_of(&sig);
                    out.push(Node::Leaf(format!("let {name} = {call}")));
                    self.declare(&name, VTy::Int);
                }
                _ => return false,
            }
            true
        }

        fn call_of(&mut self, sig: &FnSig) -> String {
            let args: Vec<String> = sig
                .params
                .iter()
                .map(|kind| match kind {
                    PKind::IntP => self.int_expr(),
                    PKind::StrDefault | PKind::StrBorrow => match self.usable(VTy::Str) {
                        Some(s) if self.rng.chance(60) => s,
                        _ => self.str_expr(),
                    },
                    PKind::StrConsume => {
                        self.consumable(VTy::Str).unwrap_or_else(|| self.str_expr())
                    }
                    PKind::ArrDefault => match self.usable(VTy::Arr) {
                        Some(a) if self.rng.chance(60) => a,
                        _ => {
                            let e = self.str_expr();
                            format!("[{e}]")
                        }
                    },
                    PKind::ArrConsume => match self.consumable(VTy::Arr) {
                        Some(a) => a,
                        None => {
                            let e = self.str_expr();
                            format!("[{e}]")
                        }
                    },
                })
                .collect();
            format!("{}({})", sig.name, args.join(", "))
        }

        // ----- declarations ----------------------------------------------

        fn function(&mut self) -> Node {
            let name = format!("f{}", self.funcs.len());
            let kinds: Vec<PKind> = (0..self.rng.below(3))
                .map(|_| {
                    *self.rng.pick(&[
                        PKind::IntP,
                        PKind::StrDefault,
                        PKind::StrConsume,
                        PKind::StrBorrow,
                        PKind::ArrDefault,
                        PKind::ArrConsume,
                    ])
                })
                .collect();
            self.frames.push(Frame {
                vars: vec![],
                barrier: true,
            });
            let params: Vec<String> = kinds
                .iter()
                .map(|kind| {
                    let p = self.fresh("p");
                    match kind {
                        PKind::IntP => {
                            self.declare_full(&p, VTy::Int, false, false);
                            format!("{p}: Int")
                        }
                        PKind::StrDefault => {
                            // Borrow-default param (ADR 0018): borrowed
                            // storage despite the owned spelling.
                            self.declare_full(&p, VTy::Str, true, false);
                            format!("{p}: String")
                        }
                        PKind::StrConsume => {
                            self.declare_full(&p, VTy::Str, false, false);
                            format!("consume {p}: String")
                        }
                        PKind::StrBorrow => {
                            self.declare_full(&p, VTy::Str, true, false);
                            format!("{p}: &String")
                        }
                        PKind::ArrDefault => {
                            self.declare_full(&p, VTy::Arr, true, false);
                            format!("{p}: Array<String>")
                        }
                        PKind::ArrConsume => {
                            self.declare_full(&p, VTy::Arr, false, false);
                            format!("consume {p}: Array<String>")
                        }
                    }
                })
                .collect();

            // Handlers install only at a body's root (the nested-block
            // fence); abort-handler bodies produce the function's Int.
            let handles_oops = self.rng.chance(35);
            let handles_ask = self.rng.chance(30);
            let mut body = vec![];
            if handles_oops {
                let binder = self.fresh("mv");
                let fallback = self.rng.below(9);
                body.push(Node::Leaf(format!(
                    "@handle 'oops {{ {binder} in\n\tprint(\"caught:\" + {binder})\n\t{fallback}\n}}"
                )));
            }
            if handles_ask {
                body.push(Node::Leaf(format!(
                    "@handle 'ask {{ continue {} }}",
                    1 + self.rng.below(5)
                )));
            }
            let ctx = Ctx {
                depth: 0,
                in_loop: false,
                can_return: true,
                handles_oops,
                handles_ask,
            };
            body.extend(self.block(ctx, 3, 6));
            let tail = self.int_expr();
            body.push(Node::Leaf(tail));
            self.frames.pop();

            self.funcs.push(FnSig {
                name: name.clone(),
                params: kinds,
            });
            Node::Scope {
                head: format!("func {name}({}) -> Int {{", params.join(", ")),
                fixed: vec![],
                body,
                tail: "}".into(),
            }
        }

        /// Fixed declarations every program shares: the effects, the
        /// droppable-field `Deinit` struct, the `'heap` struct, and the
        /// helper functions the statement grammar calls into. All plain
        /// nodes — the shrinker may delete unused ones.
        fn prelude(&self) -> Vec<Node> {
            [
                "effect 'oops(msg: String) -> Never",
                "effect 'ask() -> Int",
                "struct Loud {\n\tlet s: String\n}",
                "extend Loud: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tprint(\"~\" + self.s)\n\t}\n}",
                "struct Jar 'heap {\n\tlet key: String\n\tlet n: Int\n}",
                "func blen(s: &String) -> Int {\n\ts.byte_count\n}",
                "func mk(s: &String) -> String {\n\ts + \"!\"\n}",
                "func dlen(s: String) -> Int {\n\ts.byte_count\n}",
                "func eat(consume s: String) -> Int {\n\ts.byte_count\n}",
                "func eat_arr(consume xs: Array<String>) -> Int {\n\txs.count\n}",
                "func gulp<T>(consume x: T) -> Int {\n\t1\n}",
                "func run_once(fn: () -> ()) -> Int {\n\tfn()\n\t1\n}",
                "func run_twice(fn: () -> ()) -> Int {\n\tfn()\n\tfn()\n\t2\n}",
                "func risky(n: Int) 'oops -> Int {\n\tif n > 2 {\n\t\t'oops(\"boom\")\n\t}\n\tn + 1\n}",
                "func bonus(n: Int) 'ask -> Int {\n\t'ask() + n\n}",
                "func risky_eat(consume s: String, n: Int) 'oops -> Int {\n\tif n > 2 {\n\t\t'oops(\"burn:\" + s)\n\t}\n\ts.byte_count\n}",
            ]
            .iter()
            .map(|text| Node::Leaf((*text).to_string()))
            .collect()
        }

        fn program(&mut self) -> Vec<Node> {
            let mut nodes = self.prelude();
            self.frames.push(Frame {
                vars: vec![],
                barrier: true,
            });
            for _ in 0..self.rng.range(1, 3) {
                nodes.push(self.function());
            }
            let ctx = Ctx {
                depth: 0,
                in_loop: false,
                can_return: false,
                handles_oops: false,
                handles_ask: false,
            };
            let mut top = self.block(ctx, 4, 8);
            // Every generated function is exercised at least once.
            for sig in self.funcs.clone() {
                let call = self.call_of(&sig);
                top.push(Node::Leaf(format!("print({call})")));
            }
            top.push(Node::Leaf("0".into()));
            self.frames.pop();
            nodes.extend(top);
            nodes
        }
    }

    // ------------------------------------------------------------------
    // Oracle — the plan's stack, via the ordinary driver entry points.
    // ------------------------------------------------------------------

    enum Verdict {
        /// Front-half rejection (parse/resolve/check/lower diagnostics).
        /// Expected for a minority of compositions: the reject path.
        Rejected { stage: &'static str, detail: String },
        /// Compiled, verified balanced, both engines agreed, leak fences
        /// held.
        Passed,
        /// Any oracle violation: balance-verifier report, leak-fence trip,
        /// engine divergence, runtime error, or internal panic.
        Failed(String),
    }

    fn panic_text(payload: &(dyn std::any::Any + Send)) -> String {
        payload
            .downcast_ref::<&str>()
            .map(|s| (*s).to_string())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "non-string panic payload".to_string())
    }

    fn evaluate(code: &str) -> Verdict {
        match catch_unwind(AssertUnwindSafe(|| pipeline(code))) {
            Ok(verdict) => verdict,
            Err(payload) => Verdict::Failed(panic_text(payload.as_ref())),
        }
    }

    fn pipeline(code: &str) -> Verdict {
        let driver = Driver::new(vec![Source::from(code)], DriverConfig::new("FuzzTest"));
        let parsed = match driver.parse() {
            Ok(parsed) => parsed,
            Err(err) => {
                return Verdict::Rejected {
                    stage: "parse",
                    detail: format!("{err:?}"),
                };
            }
        };
        let resolved = match parsed.resolve_names() {
            Ok(resolved) => resolved,
            Err(err) => {
                return Verdict::Rejected {
                    stage: "resolve",
                    detail: format!("{err:?}"),
                };
            }
        };
        let typed = resolved.type_check();
        if typed.has_errors() {
            return Verdict::Rejected {
                stage: "check",
                detail: format!("{:?}", typed.diagnostics()),
            };
        }
        // The free-balance verifier (ADR 0017 stage 2) asserts inside
        // `lower()` in test builds; a report arrives as a caught panic.
        let mut lowered = typed.lower();
        if !lowered.phase.diagnostics.is_empty() {
            return Verdict::Rejected {
                stage: "lower",
                detail: format!("{:?}", lowered.phase.diagnostics),
            };
        }
        // VM first: the substitution evaluator mutates the program. Both
        // runs assert the leak fences (zero live allocations beyond the
        // result footprint) internally.
        let (vm_value, vm_out) = match lowered.run_vm_with_output() {
            Ok(pair) => pair,
            Err(err) => return Verdict::Failed(format!("vm run: {err}")),
        };
        let (eval_value, eval_out) = match lowered.eval_with_output() {
            Ok(pair) => pair,
            Err(err) => return Verdict::Failed(format!("evaluator run: {err:?}")),
        };
        if vm_out != eval_out {
            return Verdict::Failed(format!(
                "stdout diverged:\n--- vm ---\n{vm_out}\n--- evaluator ---\n{eval_out}"
            ));
        }
        // Programs end in an Int; scalar results must agree. Non-scalar
        // shapes have no cross-engine comparison — stdout already did the
        // differential work.
        let scalars_agree = match (&eval_value, &vm_value) {
            (EvalValue::I64(a), Value::I64(b)) => a == b,
            (EvalValue::F64(a), Value::F64(b)) => a == b,
            (EvalValue::Bool(a), Value::Bool(b)) => a == b,
            (EvalValue::Void, Value::Void) => true,
            _ => true,
        };
        if !scalars_agree {
            return Verdict::Failed(format!(
                "result diverged: evaluator {eval_value:?} != vm {vm_value:?}"
            ));
        }
        Verdict::Passed
    }

    // ------------------------------------------------------------------
    // Shrinking — greedy delta debugging over the node tree: try removing
    // each node, and splicing each scope's body over itself, keeping any
    // change under which the oracle still fails. Dependency breakage needs
    // no bookkeeping: a reduction that no longer compiles no longer fails
    // the oracle, so it is simply not taken.
    // ------------------------------------------------------------------

    #[derive(Clone, Copy)]
    enum Op {
        Remove,
        Unwrap,
        /// Replace a leaf with `0` — unlocks removing a `let` a body's
        /// Int-typed tail expression still references.
        Zero,
    }

    fn paths(nodes: &[Node], prefix: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        for (i, node) in nodes.iter().enumerate() {
            prefix.push(i);
            out.push(prefix.clone());
            if let Node::Scope { body, .. } = node {
                paths(body, prefix, out);
            }
            prefix.pop();
        }
    }

    fn with_op(nodes: &[Node], path: &[usize], op: Op) -> Option<Vec<Node>> {
        let mut out = nodes.to_vec();
        let i = path[0];
        if path.len() == 1 {
            match op {
                Op::Remove => {
                    out.remove(i);
                }
                Op::Unwrap => match &nodes[i] {
                    Node::Scope { body, .. } => {
                        let inner = body.clone();
                        out.splice(i..=i, inner);
                    }
                    Node::Leaf(_) => return None,
                },
                Op::Zero => match &nodes[i] {
                    Node::Leaf(text) if text != "0" => out[i] = Node::Leaf("0".into()),
                    _ => return None,
                },
            }
            Some(out)
        } else {
            match &nodes[i] {
                Node::Scope {
                    head,
                    fixed,
                    body,
                    tail,
                } => {
                    let new_body = with_op(body, &path[1..], op)?;
                    out[i] = Node::Scope {
                        head: head.clone(),
                        fixed: fixed.clone(),
                        body: new_body,
                        tail: tail.clone(),
                    };
                    Some(out)
                }
                Node::Leaf(_) => None,
            }
        }
    }

    fn shrink(
        mut program: Vec<Node>,
        still_fails: &mut dyn FnMut(&str) -> bool,
        budget: usize,
    ) -> Vec<Node> {
        let mut remaining = budget;
        'progress: loop {
            let mut all = vec![];
            paths(&program, &mut vec![], &mut all);
            for path in &all {
                for op in [Op::Remove, Op::Unwrap, Op::Zero] {
                    let Some(candidate) = with_op(&program, path, op) else {
                        continue;
                    };
                    if remaining == 0 {
                        return program;
                    }
                    remaining -= 1;
                    if still_fails(&render(&candidate)) {
                        program = candidate;
                        continue 'progress;
                    }
                }
            }
            return program;
        }
    }

    // ------------------------------------------------------------------
    // Runner
    // ------------------------------------------------------------------

    struct Failure {
        index: usize,
        seed: u64,
        reason: String,
        shrunk: String,
        file: std::path::PathBuf,
    }

    struct Stats {
        count: usize,
        passed: usize,
        rejected: BTreeMap<&'static str, usize>,
        /// First line of each rejection detail, tallied — the signal for
        /// which grammar production is costing compile rate.
        reject_reasons: BTreeMap<String, usize>,
        failures: Vec<Failure>,
    }

    impl Stats {
        /// Fraction of programs the checker accepted (`talk check` passed;
        /// includes lowering-diagnostic rejects, which are post-check).
        fn compile_rate(&self) -> f64 {
            let front_rejects: usize = self
                .rejected
                .iter()
                .filter(|(stage, _)| **stage != "lower")
                .map(|(_, n)| n)
                .sum();
            (self.count - front_rejects) as f64 / self.count.max(1) as f64
        }

        fn report(&self, base_seed: u64) -> String {
            let mut out = format!(
                "fuzz: base seed {base_seed:#x}, {} programs: {} passed the full oracle, {} failed, compile rate {:.0}%\n",
                self.count,
                self.passed,
                self.failures.len(),
                self.compile_rate() * 100.0
            );
            for (stage, n) in &self.rejected {
                out.push_str(&format!("  rejected at {stage}: {n}\n"));
            }
            let mut reasons: Vec<(&String, &usize)> = self.reject_reasons.iter().collect();
            reasons.sort_by(|a, b| b.1.cmp(a.1));
            for (reason, n) in reasons.iter().take(8) {
                out.push_str(&format!("    {n} x {reason}\n"));
            }
            for failure in &self.failures {
                out.push_str(&format!(
                    "  FAILURE program #{} (TALK_FUZZ_SEED={base_seed} derived seed {:#x}) — {}\n  shrunk repro at {}:\n{}\n",
                    failure.index,
                    failure.seed,
                    failure.reason.lines().next().unwrap_or(""),
                    failure.file.display(),
                    failure.shrunk
                ));
            }
            out
        }
    }

    fn generate(seed: u64) -> Vec<Node> {
        Gen::new(seed).program()
    }

    fn fuzz(base_seed: u64, count: usize, skips: &[usize]) -> Stats {
        let mut stats = Stats {
            count: 0,
            passed: 0,
            rejected: BTreeMap::new(),
            reject_reasons: BTreeMap::new(),
            failures: vec![],
        };
        for index in 0..count {
            if skips.contains(&index) {
                continue;
            }
            stats.count += 1;
            let seed = derive_seed(base_seed, index as u64);
            let program = generate(seed);
            match evaluate(&render(&program)) {
                Verdict::Passed => stats.passed += 1,
                Verdict::Rejected { stage, detail } => {
                    *stats.rejected.entry(stage).or_default() += 1;
                    // Key on the diagnostic kind, not the node/detail, so
                    // the tally groups by grammar production at fault.
                    let start = detail.find("kind: ").map(|i| i + 6).unwrap_or(0);
                    let key: String = detail[start..].chars().take(90).collect();
                    *stats.reject_reasons.entry(key).or_default() += 1;
                    // Grammar-maintenance aid: dump rejected programs for
                    // inspection when tightening the compile rate.
                    if std::env::var("TALK_FUZZ_DUMP_REJECTS").is_ok() {
                        let dir = std::path::Path::new("target/fuzz/rejects");
                        std::fs::create_dir_all(dir).expect("create rejects dir");
                        std::fs::write(
                            dir.join(format!("reject_{base_seed:x}_{index}.tlk")),
                            format!("// {stage}: {detail}\n{}", render(&program)),
                        )
                        .expect("write reject");
                    }
                }
                Verdict::Failed(reason) => {
                    let budget = env_u64("TALK_FUZZ_SHRINK_BUDGET")
                        .map(|n| n as usize)
                        .unwrap_or(SHRINK_BUDGET);
                    let shrunk_nodes = shrink(
                        program,
                        &mut |code| matches!(evaluate(code), Verdict::Failed(_)),
                        budget,
                    );
                    let shrunk = render(&shrunk_nodes);
                    let final_reason = match evaluate(&shrunk) {
                        Verdict::Failed(r) => r,
                        _ => reason.clone(),
                    };
                    let dir = std::path::Path::new("target/fuzz");
                    std::fs::create_dir_all(dir).expect("create target/fuzz");
                    let file = dir.join(format!("failure_{base_seed:x}_{index}.tlk"));
                    let commented: String = final_reason
                        .lines()
                        .map(|line| format!("// {line}\n"))
                        .collect();
                    std::fs::write(
                        &file,
                        format!(
                            "// TALK_FUZZ_SEED={base_seed} program #{index} (derived seed {seed:#x})\n{commented}\n{shrunk}"
                        ),
                    )
                    .expect("write failure repro");
                    stats.failures.push(Failure {
                        index,
                        seed,
                        reason: final_reason,
                        shrunk,
                        file,
                    });
                }
            }
        }
        stats
    }

    fn env_u64(name: &str) -> Option<u64> {
        let raw = std::env::var(name).ok()?;
        let raw = raw.trim();
        if let Some(hex) = raw.strip_prefix("0x") {
            u64::from_str_radix(hex, 16).ok()
        } else {
            raw.parse().ok()
        }
    }

    // ------------------------------------------------------------------
    // Infrastructure tests
    // ------------------------------------------------------------------

    #[test]
    fn fuzz_generator_is_deterministic() {
        let a = render(&generate(derive_seed(DEFAULT_SEED, 7)));
        let b = render(&generate(derive_seed(DEFAULT_SEED, 7)));
        assert_eq!(a, b, "same seed must generate the same program");
        let c = render(&generate(derive_seed(DEFAULT_SEED, 8)));
        assert_ne!(a, c, "different seeds should generate different programs");
        assert!(
            a.contains("func f0("),
            "programs define generated functions"
        );
    }

    #[test]
    fn fuzz_oracle_classifies_rejections_and_passes() {
        match evaluate("let x: Int = \"nope\"\n0") {
            Verdict::Rejected { stage, .. } => assert_eq!(stage, "check"),
            _ => panic!("type error must classify as a check rejection"),
        }
        match evaluate("let s = \"a\" + \"b\"\nprint(s)\n0") {
            Verdict::Passed => {}
            Verdict::Rejected { stage, detail } => {
                panic!("trivial program rejected at {stage}: {detail}")
            }
            Verdict::Failed(reason) => panic!("trivial program failed the oracle: {reason}"),
        }
    }

    #[test]
    fn fuzz_shrinker_reduces_to_the_failing_core() {
        let program = vec![
            Node::Leaf("let a = 1".into()),
            Node::Scope {
                head: "if true {".into(),
                fixed: vec![],
                body: vec![Node::Leaf("MARKER".into()), Node::Leaf("let b = 2".into())],
                tail: "}".into(),
            },
            Node::Leaf("let c = 3".into()),
        ];
        let shrunk = shrink(program, &mut |code| code.contains("MARKER"), SHRINK_BUDGET);
        assert_eq!(render(&shrunk).trim(), "MARKER");
    }

    /// Debugging entry: run one program file through the exact oracle
    /// (`TALK_FUZZ_PROBE=path cargo test fuzz_probe -- --nocapture`).
    /// A no-op without the env var. Runs the evaluator on a separate
    /// compile as well, so a leak can be attributed per engine (the
    /// pipeline's VM-first fence otherwise masks the evaluator's).
    #[test]
    fn fuzz_probe_from_env() {
        let Ok(path) = std::env::var("TALK_FUZZ_PROBE") else {
            return;
        };
        let code = std::fs::read_to_string(&path).expect("read probe program");
        match evaluate(&code) {
            Verdict::Passed => println!("probe {path}: PASSED"),
            Verdict::Rejected { stage, detail } => {
                println!("probe {path}: REJECTED at {stage}\n{detail}")
            }
            Verdict::Failed(reason) => println!("probe {path}: FAILED\n{reason}"),
        }
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let driver = Driver::new(
                vec![Source::from(code.as_str())],
                DriverConfig::new("FuzzProbe"),
            );
            let mut lowered = driver
                .parse()
                .expect("parse")
                .resolve_names()
                .expect("resolve")
                .type_check()
                .lower();
            lowered
                .eval_with_output()
                .map(|(value, _)| format!("{value:?}"))
        }));
        match outcome {
            Ok(Ok(value)) => println!("probe {path}: evaluator-only run balanced, value {value}"),
            Ok(Err(err)) => println!("probe {path}: evaluator-only run errored: {err:?}"),
            Err(payload) => println!(
                "probe {path}: evaluator-only run failed: {}",
                panic_text(payload.as_ref())
            ),
        }
    }

    // ------------------------------------------------------------------
    // The fuzz test proper
    // ------------------------------------------------------------------

    /// CI entry point: deterministic (fixed base seed, derived per-program
    /// seeds, no clocks or entropy). Exploratory runs override via
    /// `TALK_FUZZ_SEED` / `TALK_FUZZ_COUNT`; overriding the seed also
    /// clears the default-skip list, since skips are pinned to the default
    /// sequence's indices.
    #[test]
    fn fuzz_ownership_grammar_holds_the_oracle() {
        let base_seed = env_u64("TALK_FUZZ_SEED").unwrap_or(DEFAULT_SEED);
        let count = env_u64("TALK_FUZZ_COUNT")
            .map(|n| n as usize)
            .unwrap_or(DEFAULT_COUNT);
        let skips: &[usize] = if base_seed == DEFAULT_SEED {
            DEFAULT_SKIPS
        } else {
            &[]
        };
        let stats = fuzz(base_seed, count, skips);
        println!("{}", stats.report(base_seed));
        assert!(
            stats.failures.is_empty(),
            "ownership fuzzer found {} failing program(s):\n{}",
            stats.failures.len(),
            stats.report(base_seed)
        );
        assert!(
            stats.passed > 0,
            "no generated program passed the oracle — the grammar is broken"
        );
        assert!(
            stats.compile_rate() >= COMPILE_RATE_FLOOR,
            "compile rate {:.0}% is under the {:.0}% floor — tighten the grammar\n{}",
            stats.compile_rate() * 100.0,
            COMPILE_RATE_FLOOR * 100.0,
            stats.report(base_seed)
        );
    }
}
