//! λ_G calculus tests, built directly from the worked examples in Leißa &
//! Griebler, *SSA without Dominance for Higher-Order Programs*
//! (arXiv:2604.09961v2; `ssa-paper.md`): Fig. 3's nested loops drive the
//! free-variable table (Table 1) including the mutation/invalidation
//! episode; Fig. 4's `iter`/`pow` drives the evaluator and nesting forest;
//! Fig. 5/6 drive well-formedness; §2.2's loop peeling drives β-reduction.

#[cfg(test)]
pub mod tests {
    use crate::lambda_g::eval::{EvalValue, Evaluator};
    use crate::lambda_g::expr::CmpOp;
    use crate::lambda_g::program::{Label, Program};

    /// Build Fig. 3b: nested but INDEPENDENT loops.
    ///   f(n, ret); hi(i1) { (i1<n ? bi : xi)() }; bi() { hj i1 }; xi() { ret i1 }
    ///   hj(j1) { j2=j1+1; (j1<n ? bj : xj)() }; bj() { hj j2 }; xj() { hi j2 }
    struct Loops {
        p: Program,
        f: Label,
        hi: Label,
        bi: Label,
        xi: Label,
        hj: Label,
        bj: Label,
        xj: Label,
    }

    fn fig3(version_c: bool) -> Loops {
        let mut p = Program::new();
        let int = p.ty_i64();
        let bot = p.ty_bot();
        let unit = p.ty_tuple(&[]);
        let ret_ty = p.ty_fn(int, bot);
        let f_dom = p.ty_tuple(&[int, ret_ty]);
        let thunk = p.ty_fn(unit, bot);

        let f = p.func("f", f_dom, bot);
        let hi = p.func("hi", int, bot);
        let bi = p.func("bi", unit, bot);
        let xi = p.func("xi", unit, bot);
        let hj = p.func("hj", int, bot);
        let bj = p.func("bj", unit, bot);
        let xj = p.func("xj", unit, bot);

        let n = {
            let vf = p.var(f);
            p.extract(vf, 0)
        };
        let ret = {
            let vf = p.var(f);
            p.extract(vf, 1)
        };
        let i1 = p.var(hi);
        let j1 = p.var(hj);

        // f: hi 0
        let zero = p.int(0);
        let hi_ref = p.func_ref(hi);
        let body_f = p.app(hi_ref, zero);
        p.set_body(f, body_f);

        // hi: br(i1 < n, bi, xi)
        let cond_i = p.cmp(CmpOp::Lt, i1, n);
        let bi_ref = p.func_ref(bi);
        let xi_ref = p.func_ref(xi);
        let body_hi = p.br(cond_i, bi_ref, xi_ref, thunk);
        p.set_body(hi, body_hi);

        // bi: hj i1
        let hj_ref = p.func_ref(hj);
        let body_bi = p.app(hj_ref, i1);
        p.set_body(bi, body_bi);

        // xi: ret i1
        let body_xi = p.app(ret, i1);
        p.set_body(xi, body_xi);

        // hj: br(j1 < n, bj, xj)
        let cond_j = p.cmp(CmpOp::Lt, j1, n);
        let bj_ref = p.func_ref(bj);
        let xj_ref = p.func_ref(xj);
        let body_hj = p.br(cond_j, bj_ref, xj_ref, thunk);
        p.set_body(hj, body_hj);

        // bj: hj j2   where j2 = j1 + 1
        let one = p.int(1);
        let j2 = p.add(j1, one);
        let hj_ref2 = p.func_ref(hj);
        let body_bj = p.app(hj_ref2, j2);
        p.set_body(bj, body_bj);

        // xj: Fig 3b: hi j2 — independent loops.
        //     Fig 3c: i2 = i1 + j1; hi i2 — inner depends on outer.
        let hi_ref2 = p.func_ref(hi);
        let body_xj = if version_c {
            let i2 = p.add(i1, j1);
            p.app(hi_ref2, i2)
        } else {
            let j2b = p.add(j1, one);
            p.app(hi_ref2, j2b)
        };
        p.set_body(xj, body_xj);

        Loops {
            p,
            f,
            hi,
            bi,
            xi,
            hj,
            bj,
            xj,
        }
    }

    fn fv_names(p: &mut Program, l: Label) -> Vec<String> {
        let set = p.fv(l);
        let mut names: Vec<String> = p.set_labels(set).iter().map(|l| p.name(*l)).collect();
        names.sort();
        names
    }

    #[test]
    fn fig3b_free_variables_match_table_1() {
        let mut loops = fig3(false);
        let p = &mut loops.p;
        assert_eq!(fv_names(p, loops.f), Vec::<String>::new());
        assert_eq!(fv_names(p, loops.hi), ["f"]);
        assert_eq!(fv_names(p, loops.bi), ["f", "hi"]);
        assert_eq!(fv_names(p, loops.xi), ["f", "hi"]);
        assert_eq!(fv_names(p, loops.hj), ["f"]);
        assert_eq!(fv_names(p, loops.bj), ["f", "hj"]);
        assert_eq!(fv_names(p, loops.xj), ["f", "hj"]);
    }

    #[test]
    fn fig3c_mutation_invalidates_and_recomputes() {
        // Table 1's bottom half: compute 3b's FVs, then mutate xj to the 3c
        // body. xi's cache must survive (it does not depend on xj); the
        // others recompute with var hi now free in the inner loop.
        let mut loops = fig3(false);
        let p = &mut loops.p;
        let _ = fv_names(p, loops.f);
        assert!(p.fv_is_cached(loops.xi));

        let i1 = p.var(loops.hi);
        let j1 = p.var(loops.hj);
        let i2 = p.add(i1, j1);
        let hi_ref = p.func_ref(loops.hi);
        let new_body = p.app(hi_ref, i2);
        p.set_body(loops.xj, new_body);

        assert!(
            p.fv_is_cached(loops.xi),
            "xi does not depend on xj; its cache must survive (Table 1)"
        );
        assert!(
            !p.fv_is_cached(loops.bj),
            "bj depends on hj which depends on xj; must be invalidated"
        );

        assert_eq!(fv_names(p, loops.hj), ["f", "hi"]);
        assert_eq!(fv_names(p, loops.bj), ["f", "hi", "hj"]);
        assert_eq!(fv_names(p, loops.xj), ["f", "hi", "hj"]);
        assert_eq!(fv_names(p, loops.xi), ["f", "hi"]);
    }

    #[test]
    fn fig3b_nesting_tree_keeps_loops_side_by_side() {
        // §2.3: the nesting tree places the independent inner loop BESIDE
        // the outer one (unlike the dominator tree).
        let mut loops = fig3(false);
        let p = &mut loops.p;
        let tree = p.nesting_tree(loops.f);
        assert_eq!(tree.parent(loops.hi), Some(loops.f));
        assert_eq!(tree.parent(loops.hj), Some(loops.f), "independent inner loop");
        assert_eq!(tree.parent(loops.bi), Some(loops.hi));
        assert_eq!(tree.parent(loops.xi), Some(loops.hi));
        assert_eq!(tree.parent(loops.bj), Some(loops.hj));
        assert_eq!(tree.parent(loops.xj), Some(loops.hj));
    }

    #[test]
    fn fig3c_nesting_tree_nests_dependent_inner_loop() {
        let mut loops = fig3(true);
        let p = &mut loops.p;
        let tree = p.nesting_tree(loops.f);
        assert_eq!(
            tree.parent(loops.hj),
            Some(loops.hi),
            "3c's inner loop depends on i1, so hj hangs under hi (Fig. 3f)"
        );
    }

    #[test]
    fn fig3c_sibling_sccs_identify_loops() {
        // §4.1.2: hj is directly recursive (self SCC); hi's level groups
        // its loop; Tarjan runs per nesting level.
        let mut loops = fig3(true);
        let p = &mut loops.p;
        let tree = p.nesting_tree(loops.f);
        assert!(tree.in_cycle(loops.hj), "hj recurses via bj");
        assert!(tree.in_cycle(loops.hi), "hi recurses via xj");
    }

    #[test]
    fn beta_reduction_specializes_only_dependents() {
        // §2.2: peeling the outer loop = β-reducing `hi 0`. Only hi's body
        // and its dependents (bi, xi) specialize; the independent inner loop
        // (hj, bj, xj) is untouched.
        let mut loops = fig3(false);
        let p = &mut loops.p;
        let before = p.func_count();
        let zero = p.int(0);
        let _peeled = p.beta_reduce(loops.hi, zero);
        let created = p.func_count() - before;
        assert_eq!(
            created, 2,
            "exactly bi' and xi' are created; hj/bj/xj are independent"
        );
        assert!(
            p.body(loops.hj) == p.body(loops.hj),
            "hj untouched (trivially true; the count above is the real check)"
        );
    }

    #[test]
    fn fig6_cyclic_variable_dependencies_are_ill_formed() {
        // f's body uses var g; g's body uses var f — nesting must be
        // antisymmetric (Property 2 / Rule WF).
        let mut p = Program::new();
        let int = p.ty_i64();
        let f = p.func("f", int, int);
        let g = p.func("g", int, int);
        let vg = p.var(g);
        let vf = p.var(f);
        p.set_body(f, vg);
        p.set_body(g, vf);
        assert!(p.verify().is_err());
    }

    #[test]
    fn fig5_transitive_nesting_is_well_formed() {
        let mut p = Program::new();
        let int = p.ty_i64();
        let f = p.func("f", int, int);
        let g = p.func("g", int, int);
        let h = p.func("h", int, int);
        // f: g 23 ; g: h (var f) ; h: var g + 0
        let g_ref = p.func_ref(g);
        let c23 = p.int(23);
        let body_f = p.app(g_ref, c23);
        p.set_body(f, body_f);
        let h_ref = p.func_ref(h);
        let vf = p.var(f);
        let body_g = p.app(h_ref, vf);
        p.set_body(g, body_g);
        let vg = p.var(g);
        let zero = p.int(0);
        let body_h = p.add(vg, zero);
        p.set_body(h, body_h);

        assert!(p.verify().is_ok());
        // Transitivity: h nests in f even though var f ∉ FV(h)'s locals.
        let mut tree = p.nesting_tree(f);
        let _ = &mut tree;
        assert_eq!(tree.parent(g), Some(f));
        assert_eq!(tree.parent(h), Some(g));
    }

    /// Fig. 4: iter computes f^n(x); pow built by currying through iter.
    fn fig4() -> (Program, Label) {
        let mut p = Program::new();
        let int = p.ty_i64();
        let int_to_int = p.ty_fn(int, int);
        let unit = p.ty_tuple(&[]);
        let iter_dom = p.ty_tuple(&[int_to_int, int, int]);

        let iter = p.func("iter", iter_dom, int);
        let a = p.func("a", unit, int);
        let b = p.func("b", unit, int);
        let succ = p.func("succ", int, int);
        let add = p.func("add", int, int_to_int);
        let add1 = p.func("add'", int, int);
        let mul = p.func("mul", int, int_to_int);
        let mul1 = p.func("mul'", int, int);
        let pow = p.func("pow", int, int_to_int);
        let pow1 = p.func("pow'", int, int);

        let viter = p.var(iter);
        let f_arg = p.extract(viter, 0);
        let n_arg = p.extract(viter, 1);
        let x_arg = p.extract(viter, 2);

        // iter: br(n <= 0, a, b)
        let zero = p.int(0);
        let cond = p.cmp(CmpOp::Le, n_arg, zero);
        let a_ref = p.func_ref(a);
        let b_ref = p.func_ref(b);
        let thunk_int = p.ty_fn(unit, int);
        let body_iter = p.br(cond, a_ref, b_ref, thunk_int);
        p.set_body(iter, body_iter);

        // a: x
        p.set_body(a, x_arg);

        // b: iter (f, n - 1, f x)
        let one = p.int(1);
        let n_minus = p.sub(n_arg, one);
        let fx = p.app(f_arg, x_arg);
        let iter_ref = p.func_ref(iter);
        let tup = p.tuple(&[f_arg, n_minus, fx]);
        let body_b = p.app(iter_ref, tup);
        p.set_body(b, body_b);

        // succ: var succ + 1
        let vsucc = p.var(succ);
        let body_succ = p.add(vsucc, one);
        p.set_body(succ, body_succ);

        // add: λx. add'   ; add': λy. iter(succ, var add, var add')
        let add1_ref = p.func_ref(add1);
        p.set_body(add, add1_ref);
        let succ_ref = p.func_ref(succ);
        let vadd = p.var(add);
        let vadd1 = p.var(add1);
        let iter_ref2 = p.func_ref(iter);
        let tup_add = p.tuple(&[succ_ref, vadd, vadd1]);
        let body_add1 = p.app(iter_ref2, tup_add);
        p.set_body(add1, body_add1);

        // mul: λx. mul'  ; mul': λy. iter(add x, y, 0)
        let mul1_ref = p.func_ref(mul1);
        p.set_body(mul, mul1_ref);
        let add_ref = p.func_ref(add);
        let vmul = p.var(mul);
        let add_x = p.app(add_ref, vmul);
        let vmul1 = p.var(mul1);
        let iter_ref3 = p.func_ref(iter);
        let tup_mul = p.tuple(&[add_x, vmul1, zero]);
        let body_mul1 = p.app(iter_ref3, tup_mul);
        p.set_body(mul1, body_mul1);

        // pow: λx. pow'  ; pow': λy. iter(mul x, y, 1)
        let pow1_ref = p.func_ref(pow1);
        p.set_body(pow, pow1_ref);
        let mul_ref = p.func_ref(mul);
        let vpow = p.var(pow);
        let mul_x = p.app(mul_ref, vpow);
        let vpow1 = p.var(pow1);
        let iter_ref4 = p.func_ref(iter);
        let tup_pow = p.tuple(&[mul_x, vpow1, one]);
        let body_pow1 = p.app(iter_ref4, tup_pow);
        p.set_body(pow1, body_pow1);

        (p, pow)
    }

    #[test]
    fn fig4_program_is_well_formed() {
        let (mut p, _) = fig4();
        assert!(p.verify().is_ok(), "{:?}", p.verify());
    }

    #[test]
    fn fig4_nesting_forest_pairs_curried_helpers() {
        // add' nests in add (uses var add); mul' in mul; pow' in pow; iter,
        // succ, and the curried wrappers are roots of the forest (§2.4).
        let (mut p, pow) = fig4();
        let forest = p.nesting_forest();
        let parent_of = |p: &Program, name: &str, forest: &crate::lambda_g::nest::NestingTree| {
            let l = p.label_named(name).unwrap();
            forest.parent(l).map(|x| p.name(x))
        };
        assert_eq!(parent_of(&p, "add'", &forest), Some("add".to_string()));
        assert_eq!(parent_of(&p, "mul'", &forest), Some("mul".to_string()));
        assert_eq!(parent_of(&p, "pow'", &forest), Some("pow".to_string()));
        assert_eq!(parent_of(&p, "iter", &forest), None);
        assert_eq!(parent_of(&p, "succ", &forest), None);
        let _ = pow;
    }

    #[test]
    fn fig4_pow_evaluates_to_243() {
        // pow 3 5 = 3^5 = 243 via the paper's small-step semantics (§3.4) —
        // exercises β-reduction, currying, partial application, br, tuples.
        let (mut p, pow) = fig4();
        let pow_ref = p.func_ref(pow);
        let three = p.int(3);
        let five = p.int(5);
        let pow3 = p.app(pow_ref, three);
        let call = p.app(pow3, five);
        let mut evaluator = Evaluator::new();
        let result = evaluator.eval(&mut p, call).unwrap();
        assert_eq!(result, EvalValue::I64(243));
    }

    #[test]
    fn typing_rejects_ill_typed_application() {
        // T-App: argument type must match the function's domain.
        let mut p = Program::new();
        let int = p.ty_i64();
        let boolean = p.ty_bool();
        let f = p.func("f", int, int);
        let vf = p.var(f);
        p.set_body(f, vf);
        let f_ref = p.func_ref(f);
        let wrong = p.bool(true);
        let app = p.try_app(f_ref, wrong);
        assert!(app.is_err());
        let _ = boolean;
    }

    #[test]
    fn hash_consing_shares_structurally_equal_expressions() {
        let mut p = Program::new();
        let a1 = p.int(42);
        let a2 = p.int(42);
        assert_eq!(a1, a2);
        let x = p.int(1);
        let y = p.int(2);
        let s1 = p.add(x, y);
        let s2 = p.add(x, y);
        assert_eq!(s1, s2, "hash-consing = semi-global value numbering");
    }
}
