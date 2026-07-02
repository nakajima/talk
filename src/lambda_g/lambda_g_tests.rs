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
        assert_eq!(
            tree.parent(loops.hj),
            Some(loops.f),
            "independent inner loop"
        );
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
    fn rendering_reads_like_plain_functions() {
        // The textual form is for humans debugging the pipeline
        // (`talk lower`): function syntax, named ops, no notation that
        // needs a paper to decode.
        let mut p = Program::new();
        let int = p.ty_i64();
        let bot = p.ty_bot();
        let ret_ty = p.ty_fn(int, bot);
        let dom = p.ty_tuple(&[int, ret_ty]);
        let double = p.func("double", dom, bot);
        let v = p.var(double);
        let x = p.extract(v, 0);
        let k = p.extract(v, 1);
        let two = p.int(2);
        let doubled = p.primop(crate::lambda_g::expr::Op::Mul, &[x, two], int);
        let body = p.app(k, doubled);
        p.set_body(double, body);
        // Without parameter names, references are positional.
        assert_eq!(
            p.render_func(double),
            "func double(int, fn(int)) { var double.1(mul(var double.0, 2)) }"
        );
        // With names (the lowerer records them), the header and every
        // reference use them.
        p.name_params(double, &["x", "k"]);
        assert_eq!(
            p.render_func(double),
            "func double(x: int, k: fn(int)) { var double.k(mul(var double.x, 2)) }"
        );
        // A function whose body is not set yet renders honestly.
        let pending = p.func("pending", int, bot);
        assert_eq!(p.render_func(pending), "func pending(int) { unset }");
    }

    #[test]
    fn rendering_can_color_with_ansi() {
        // `talk lower` on a terminal: keywords, function names, types,
        // and constants get the same palette the REPL highlighter uses.
        let mut p = Program::new();
        let int = p.ty_i64();
        let bot = p.ty_bot();
        let ret_ty = p.ty_fn(int, bot);
        let dom = p.ty_tuple(&[int, ret_ty]);
        let double = p.func("double", dom, bot);
        p.name_params(double, &["x", "k"]);
        let v = p.var(double);
        let x = p.extract(v, 0);
        let k = p.extract(v, 1);
        let two = p.int(2);
        let doubled = p.primop(crate::lambda_g::expr::Op::Mul, &[x, two], int);
        let body = p.app(k, doubled);
        p.set_body(double, body);
        let colored = p.render_ansi();
        assert!(colored.contains("\x1b[1;35mfunc\x1b[0m"), "{colored:?}");
        assert!(colored.contains("\x1b[1;33mdouble\x1b[0m"), "{colored:?}");
        assert!(colored.contains("\x1b[1;34mint\x1b[0m"), "{colored:?}");
        assert!(colored.contains("\x1b[36m2\x1b[0m"), "{colored:?}");
        // The plain rendering stays plain.
        assert!(!p.render().contains('\x1b'));
    }

    #[test]
    fn rendering_groups_continuations_under_their_owner() {
        // The whole-program rendering nests each function under the one
        // whose variable it uses (the nesting tree), so a function's
        // helper continuations read like local functions.
        let mut p = Program::new();
        let int = p.ty_i64();
        let bot = p.ty_bot();
        let ret_ty = p.ty_fn(int, bot);
        let outer = p.func("outer", ret_ty, bot);
        let inner = p.func("inner", int, bot);
        p.name_params(outer, &["k"]);
        p.name_params(inner, &["x"]);
        let vo = p.var(outer);
        let vi = p.var(inner);
        let inner_body = p.app(vo, vi);
        p.set_body(inner, inner_body);
        let inner_ref = p.func_ref(inner);
        let seven = p.int(7);
        let outer_body = p.app(inner_ref, seven);
        p.set_body(outer, outer_body);
        assert_eq!(
            p.render(),
            "\
func outer(k: fn(int)) {
  inner(7)

  func inner(x: int) {
    var outer(var inner)
  }
}
"
        );
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

    // ----- 'heap object ops (regions substrate) ---------------------------------

    use crate::lambda_g::expr::Op;

    fn build_object_main(finalize: bool) -> (Program, Label, crate::lambda_g::expr::TyId) {
        let mut p = Program::new();
        let int = p.ty_i64();
        let bot = p.ty_bot();
        let void = p.ty_void();
        let ret_ty = p.ty_fn(int, bot);
        let main_dom = p.ty_tuple(&[ret_ty]);
        let main = p.func("main", main_dom, bot);

        // Finalizer: λ(self, k) { k(()) }.
        let k_ty = p.ty_fn(void, bot);
        let fin_dom = p.ty_tuple(&[void, k_ty]);
        let fin = p.func("fin", fin_dom, bot);
        {
            let vf = p.var(fin);
            let fk = p.extract(vf, 1);
            let unit = p.void();
            let body = p.app(fk, unit);
            p.set_body(fin, body);
        }

        // CPS bindings: objects flow through continuations (expressions
        // re-evaluate per reference — the same reason lowering binds).
        let bind_a = p.func("bind_a", void, bot);
        let bind_b = p.func("bind_b", void, bot);
        let a = p.var(bind_a);
        let b = p.var(bind_b);

        // bind_b body: link, mutate through the alias, read through the
        // other name, release both, return the read value. Effects sequence
        // through continuations (the scheduler elides tuple-carried
        // effects), mirroring lowering's sequence_void_effect.
        {
            // Built back-to-front.
            let vmain = p.var(main);
            let k = p.extract(vmain, 0);
            let bind_read = p.func("bind_read", int, bot);
            let read_value = p.var(bind_read);
            // …after releases: k(read_value)
            let mut rest = p.app(k, read_value);
            for (name, target) in [("rel_b", b), ("rel_a", a)] {
                let cont = p.func(name, void, bot);
                p.set_body(cont, rest);
                let cont_ref = p.func_ref(cont);
                let release = p.primop(Op::RegionRelease, &[target], void);
                rest = p.app(cont_ref, release);
            }
            p.set_body(bind_read, rest);
            // read a.f1 through the other name, bound via bind_read.
            let bind_read_ref = p.func_ref(bind_read);
            let read = p.primop(Op::ObjectGet(1), &[a], int);
            let mut body = p.app(bind_read_ref, read);
            // …before the read: the writes (and finalizers), innermost last.
            let via = p.primop(Op::ObjectGet(0), &[b], void); // aliases a
            let forty_two = p.int(42);
            let set_via = p.primop(Op::ObjectSet(1), &[via, forty_two], void);
            let link_b = p.primop(Op::ObjectSet(0), &[b, a], void);
            let link_a = p.primop(Op::ObjectSet(0), &[a, b], void);
            let mut effects = vec![set_via, link_b, link_a];
            if finalize {
                let fin_ref_b = p.func_ref(fin);
                effects.push(p.primop(Op::SetFinalizer, &[b, fin_ref_b], void));
                let fin_ref_a = p.func_ref(fin);
                effects.push(p.primop(Op::SetFinalizer, &[a, fin_ref_a], void));
            }
            for (i, effect) in effects.into_iter().enumerate() {
                let cont = p.func(&format!("after_{i}"), void, bot);
                p.set_body(cont, body);
                let cont_ref = p.func_ref(cont);
                body = p.app(cont_ref, effect);
            }
            p.set_body(bind_b, body);
        }

        // bind_a body: allocate b, enter bind_b.
        {
            let z1 = p.int(0);
            let z2 = p.int(0);
            let new_b = p.primop(Op::ObjectNew, &[z1, z2], void);
            let bind_b_ref = p.func_ref(bind_b);
            let body = p.app(bind_b_ref, new_b);
            p.set_body(bind_a, body);
        }

        // main body: allocate a, enter bind_a.
        {
            let z1 = p.int(0);
            let z2 = p.int(0);
            let new_a = p.primop(Op::ObjectNew, &[z1, z2], void);
            let bind_a_ref = p.func_ref(bind_a);
            let body = p.app(bind_a_ref, new_a);
            p.set_body(main, body);
        }
        (p, main, int)
    }

    #[test]
    fn object_ops_alias_and_free_in_the_evaluator() {
        let (mut p, main, int) = build_object_main(false);
        let mut eval = Evaluator::new();
        let value = eval.run_main(&mut p, main, int).expect("eval");
        assert_eq!(value, EvalValue::I64(42), "mutation visible through the alias");
        assert_eq!(eval.live_objects(), 0, "cycle freed at last release");
    }

    #[test]
    fn finalizers_run_before_free_in_the_evaluator() {
        let (mut p, main, int) = build_object_main(true);
        let mut eval = Evaluator::new();
        let value = eval.run_main(&mut p, main, int).expect("eval");
        assert_eq!(value, EvalValue::I64(42));
        assert_eq!(eval.live_objects(), 0, "finalizer walk then bulk free");
    }


    #[test]
    fn object_ops_agree_across_engines() {
        // The same hand-built program through the reference evaluator and
        // the scheduled VM must produce the same value.
        let (mut p, main, int) = build_object_main(true);
        let mut entry = rustc_hash::FxHashSet::default();
        entry.insert(main);
        let fin = p
            .labels()
            .find(|l| p.name(*l) == "fin")
            .expect("fin label");
        entry.insert(fin);
        let module = crate::vm::schedule::schedule(&mut p, main, &entry).expect("schedule");
        let mut io = crate::vm::io::CaptureIO::default();
        let vm_value = talk_runtime::interp::run(&module, &mut io).expect("vm");

        let (mut p2, main2, int2) = build_object_main(true);
        let mut eval = Evaluator::new();
        let eval_value = eval.run_main(&mut p2, main2, int2).expect("eval");
        let _ = int;
        assert_eq!(eval_value, EvalValue::I64(42));
        assert!(
            matches!(vm_value, talk_runtime::interp::Value::I64(42)),
            "vm disagreed: {vm_value:?}"
        );
    }

}
