#[cfg(test)]
pub mod tests {
    use crate::compiling::driver::{Driver, DriverConfig, Source, Typed};
    use crate::diagnostic::AnyDiagnostic;

    /// Parse, resolve, and type-check a source string. Mirrors
    /// `name_resolver_tests::tests::resolve`. Sources should start with
    /// `// no-core` to opt out of the core prelude for isolation.
    pub fn check(code: &'static str) -> Driver<Typed> {
        let driver = Driver::new_bare(vec![Source::from(code)], DriverConfig::new("TypesTest"));
        driver
            .parse()
            .expect("parse failed")
            .resolve_names()
            .expect("name resolution failed")
            .type_check()
    }

    /// Render the scheme of a named top-level binding. Nominal heads display
    /// with their source names via the symbol-name context.
    pub fn ty_of(driver: &Driver<Typed>, name: &str) -> String {
        let resolved = &driver.phase.resolved_names;
        let _names = crate::name_resolution::symbol::set_symbol_names(
            resolved.symbol_names.clone(),
        );
        let mut candidates: Vec<_> = resolved
            .symbol_names
            .iter()
            .filter(|(sym, n)| n.as_str() == name && driver.phase.types.schemes.contains_key(sym))
            .map(|(sym, _)| *sym)
            .collect();
        candidates.sort();
        let Some(symbol) = candidates.first() else {
            panic!(
                "no scheme found for {name:?}; schemes: {:?}",
                driver
                    .phase
                    .types
                    .schemes
                    .keys()
                    .map(|k| resolved.symbol_names.get(k))
                    .collect::<Vec<_>>()
            );
        };
        driver.phase.types.schemes[symbol].render()
    }

    pub fn type_errors(driver: &Driver<Typed>) -> Vec<String> {
        driver
            .phase
            .diagnostics
            .iter()
            .filter_map(|d| match d {
                AnyDiagnostic::Types(diag) => Some(diag.kind.to_string()),
                _ => None,
            })
            .collect()
    }

    pub fn assert_clean(driver: &Driver<Typed>) {
        let errors = type_errors(driver);
        assert!(errors.is_empty(), "expected no type errors, got: {errors:?}");
    }

    #[test]
    fn types_int_literal() {
        let t = check("// no-core\nlet a = 123");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "a"), "Int");
    }

    #[test]
    fn types_other_literals() {
        let t = check("// no-core\nlet a = 1.5\nlet b = true\nlet c = \"hi\"");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "a"), "Float");
        assert_eq!(ty_of(&t, "b"), "Bool");
        assert_eq!(ty_of(&t, "c"), "String");
    }

    #[test]
    fn annotated_let_checks() {
        let t = check("// no-core\nlet a: Int = 123");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "a"), "Int");
    }

    #[test]
    fn annotated_let_mismatch_errors() {
        let t = check("// no-core\nlet a: Int = 1.5");
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "errors: {errors:?}");
        assert!(errors[0].contains("Int"), "error mentions Int: {errors:?}");
        assert!(
            errors[0].contains("Float"),
            "error mentions Float: {errors:?}"
        );
    }

    #[test]
    fn identity_generalizes() {
        // Damas-Milner generalization at the top-level binding group:
        // identity gets a polymorphic scheme, each call site instantiates fresh.
        let t = check(
            "// no-core\nfunc identity(x) { x }\nlet a = identity(123)\nlet b = identity(1.5)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "identity"), "<T0>(T0) -> T0");
        assert_eq!(ty_of(&t, "a"), "Int");
        assert_eq!(ty_of(&t, "b"), "Float");
    }

    #[test]
    fn if_expression_joins_branches() {
        let t = check("// no-core\nlet a = if true { 1 } else { 2 }");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "a"), "Int");
    }

    #[test]
    fn if_branch_mismatch_errors() {
        let t = check("// no-core\nlet a = if true { 1 } else { 1.5 }");
        assert_eq!(type_errors(&t).len(), 1);
    }

    #[test]
    fn block_values_are_last_expression() {
        let t = check("// no-core\nlet a = if true { let b = 1\n b } else { 2 }");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "a"), "Int");
    }

    #[test]
    fn nested_closure_types() {
        // Capture.tlk shape (minus operators, which arrive in M3)
        let t = check("// no-core\nfunc makeCounter() {\n\tlet i = 0\n\treturn func() { i }\n}\nlet counter = makeCounter()");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "makeCounter"), "() -> () -> Int");
        assert_eq!(ty_of(&t, "counter"), "() -> Int");
    }

    #[test]
    fn local_closure_invoked() {
        // Local lets are monomorphic (OutsideIn(X) §4.2 / MonoLocalBinds);
        // calling one pins its parameter type.
        // NOTE: immediate invocation `func(x) { x }(123)` (AnonFunc.tlk) does
        // not parse as a call today — the parser splits it into a func decl
        // and a parenthesized statement. Tracked for milestone 7.
        let t = check("// no-core\nfunc main() {\n\tlet f = func(x) { x }\n\tf(123)\n}");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "main"), "() -> Int");
    }

    #[test]
    fn recursion_against_skeleton() {
        // Monomorphic recursion within a binding group (THIH binding groups):
        // the recursive call types against the group's skeleton, generalization
        // happens after.
        let t = check("// no-core\nfunc f(n) { f(n) }");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "f"), "<T0, T1>(T0) -> T1");
    }

    #[test]
    fn effect_polymorphic_apply() {
        // The effect row of `f` unifies with apply's ambient row; both
        // generalize together (display elides pure/quantified-tail rows).
        let t = check("// no-core\nfunc apply(f) { f() }");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "apply"), "<T0>(() -> T0) -> T0");
    }

    #[test]
    fn binding_groups_solve_in_dependency_order() {
        // f calls g, which is defined later; g's group must be solved (and
        // generalized) before f's so f sees g's finished type.
        let t = check("// no-core\nfunc f() { g() }\nfunc g() { 123 }");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "g"), "() -> Int");
        assert_eq!(ty_of(&t, "f"), "() -> Int");
    }

    #[test]
    fn return_statements_unify_with_return_type() {
        let t = check("// no-core\nfunc f(x) {\n\tif true { return x }\n\treturn x\n}");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "f"), "<T0>(T0) -> T0");
    }

    #[test]
    fn call_arity_mismatch_errors() {
        let t = check("// no-core\nfunc f(x) { x }\nf(1, 2)");
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "errors: {errors:?}");
        assert!(errors[0].contains("argument"), "errors: {errors:?}");
    }

    #[test]
    fn assignment_mismatch_errors() {
        let t = check("// no-core\nfunc f() {\n\tlet i = 0\n\ti = 1.5\n}");
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "errors: {errors:?}");
    }

    #[test]
    fn assignment_consistent_is_clean() {
        let t = check("// no-core\nfunc f() {\n\tlet i = 0\n\ti = 2\n\ti\n}");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "f"), "() -> Int");
    }

    #[test]
    fn calling_non_function_errors() {
        let t = check("// no-core\nlet a = 123\na(1)");
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "errors: {errors:?}");
    }

    #[test]
    fn node_types_recorded_for_expressions() {
        let t = check("// no-core\nlet a = 123");
        assert!(
            !t.phase.types.node_types.is_empty(),
            "expected node types to be recorded"
        );
    }

    // ----- Milestone 2: nominals, records, patterns ---------------------

    #[test]
    fn struct_with_explicit_init() {
        // Struct.tlk shape
        let t = check(
            "// no-core\nstruct Person {\n\tlet age: Int\n\tinit(age: Int) {\n\t\tself.age = age\n\t\tself\n\t}\n}\nlet pat = Person(age: 30)\nlet age = pat.age",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "pat"), "Person");
        assert_eq!(ty_of(&t, "age"), "Int");
    }

    #[test]
    fn memberwise_init_is_synthesized() {
        let t = check(
            "// no-core\nstruct Point {\n\tlet x: Int\n\tlet y: Int\n}\nlet p = Point(x: 1, y: 2)\nlet x = p.x",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "p"), "Point");
        assert_eq!(ty_of(&t, "x"), "Int");
    }

    #[test]
    fn init_argument_mismatch_errors() {
        let t = check(
            "// no-core\nstruct Point {\n\tlet x: Int\n\tlet y: Int\n}\nlet p = Point(x: 1, y: 2.5)",
        );
        assert_eq!(type_errors(&t).len(), 1, "{:?}", type_errors(&t));
    }

    #[test]
    fn methods_bind_self() {
        // Methods get an implicit self parameter (PrependSelfToMethods); the
        // bound method drops it at the call site.
        let t = check(
            "// no-core\nstruct Counter {\n\tlet n: Int\n\tfunc get() { self.n }\n}\nlet c = Counter(n: 1)\nlet v = c.get()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "get"), "(Counter) -> Int");
        assert_eq!(ty_of(&t, "v"), "Int");
    }

    #[test]
    fn methods_call_each_other_within_the_group() {
        // Methods of one nominal are a single binding group: in-flight
        // signatures are monomorphic skeletons (THIH §11.6.3).
        let t = check(
            "// no-core\nstruct S {\n\tlet n: Int\n\tfunc a() { self.b() }\n\tfunc b() { self.n }\n}\nlet s = S(n: 1)\nlet v = s.a()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "v"), "Int");
    }

    #[test]
    fn enum_with_generic_payload() {
        // MatchBind.tlk shape
        let t = check(
            "// no-core\nenum Maybe<T> {\n\tcase definitely(T)\n\tcase nope\n}\nlet maybe = Maybe.definitely(1234)\nlet result = match maybe {\n\t.definitely(x) -> x,\n\t.nope -> 0\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "maybe"), "Maybe<Int>");
        assert_eq!(ty_of(&t, "result"), "Int");
    }

    #[test]
    fn variant_payload_arity_mismatch_errors() {
        let t = check(
            "// no-core\nenum Maybe<T> {\n\tcase definitely(T)\n\tcase nope\n}\nlet maybe = Maybe.definitely(1, 2)",
        );
        assert_eq!(type_errors(&t).len(), 1, "{:?}", type_errors(&t));
    }

    #[test]
    fn unknown_variant_in_pattern_errors() {
        let t = check(
            "// no-core\nenum Maybe<T> {\n\tcase definitely(T)\n\tcase nope\n}\nlet maybe = Maybe.nope\nmatch maybe {\n\t.bogus -> 1,\n\t.nope -> 0\n}",
        );
        assert_eq!(type_errors(&t).len(), 1, "{:?}", type_errors(&t));
    }

    #[test]
    fn structural_records_match_exact_shapes() {
        // StructuralTyping.tlk shape
        let t = check(
            "// no-core\nlet record = { x: 123, y: 456 }\nlet result = match record {\n\t{ x, y: 123 } -> false,\n\t{ x, y: 456 } -> true,\n\t{ x, y: _ } -> true\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "record"), "{ x: Int, y: Int }");
        assert_eq!(ty_of(&t, "result"), "Bool");
    }

    #[test]
    fn record_field_access() {
        let t = check("// no-core\nlet r = { x: 1 }\nlet v = r.x");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "v"), "Int");
    }

    #[test]
    fn missing_record_field_errors() {
        let t = check("// no-core\nlet r = { x: 1 }\nlet v = r.y");
        assert_eq!(type_errors(&t).len(), 1, "{:?}", type_errors(&t));
    }

    // ----- Milestone 3: protocols, bounds, HasMember inference ----------

    #[test]
    fn retroactive_conformance_with_bounded_generic() {
        // Protocols.tlk shape: classes-as-predicates (Wadler & Blott 1989),
        // retroactive conformance via extend, declared bound on T.
        let t = check(
            "// no-core\nprotocol Foo {\n\tfunc foo() -> Int\n}\nstruct Thing {}\nextend Thing: Foo {\n\tfunc foo() { 123 }\n}\nfunc fizz<T: Foo>(t: T) { t.foo() }\nlet r = fizz(Thing())",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "fizz"), "<T0: Foo>(T0) -> Int");
        assert_eq!(ty_of(&t, "r"), "Int");
    }

    #[test]
    fn conformance_violation_errors() {
        let t = check(
            "// no-core\nprotocol Foo {\n\tfunc foo() -> Int\n}\nfunc fizz<T: Foo>(t: T) { t.foo() }\nfizz(123)",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("Foo"), "{errors:?}");
    }

    #[test]
    fn member_call_through_extend_witness() {
        let t = check(
            "// no-core\nprotocol Foo {\n\tfunc foo() -> Int\n}\nstruct Thing {}\nextend Thing: Foo {\n\tfunc foo() { 123 }\n}\nlet thing = Thing()\nlet v = thing.foo()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "v"), "Int");
    }

    #[test]
    fn missing_witness_errors() {
        let t = check(
            "// no-core\nprotocol Foo {\n\tfunc foo() -> Int\n\tfunc bar() -> Int\n}\nstruct Thing {}\nextend Thing: Foo {\n\tfunc foo() { 123 }\n}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("bar"), "{errors:?}");
    }

    #[test]
    fn member_on_unknown_improves_to_unique_protocol() {
        // HasMember predicate (Gaster & Jones 1996) + unique-owner
        // improvement (Jones, FPCA 1995): x.show() pins T0: Show.
        let t = check(
            "// no-core\nprotocol Show {\n\tfunc show() -> Int\n}\nfunc showit(x) { x.show() }",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "showit"), "<T0: Show>(T0) -> Int");
    }

    #[test]
    fn member_on_unknown_improves_to_unique_nominal() {
        let t = check(
            "// no-core\nstruct Box {\n\tlet val: Int\n}\nfunc get(b) { b.val }\nlet r = get(Box(val: 3))",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "get"), "(Box) -> Int");
        assert_eq!(ty_of(&t, "r"), "Int");
    }

    #[test]
    fn ambiguous_member_errors() {
        let t = check(
            "// no-core\nprotocol A {\n\tfunc m() -> Int\n}\nprotocol B {\n\tfunc m() -> Int\n}\nfunc f(x) { x.m() }",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
    }

    #[test]
    fn zero_annotation_fib_with_operators() {
        // The milestone-3 capstone: operators desugar to protocol-static
        // calls (Add.add(lhs, rhs)); HasMember/Conforms predicates collect on
        // n, improvement and generalization produce a bounded scheme, and
        // the call site discharges against Int's conformances with
        // associated-type bindings (Chakravarty et al., ICFP 2005).
        let t = check(
            "// no-core\nprotocol Add {\n\tassociated RHS\n\tassociated Ret\n\tfunc add(rhs: RHS) -> Ret\n}\nprotocol Subtract {\n\tassociated RHS\n\tassociated Ret\n\tfunc minus(rhs: RHS) -> Ret\n}\nprotocol Comparable {\n\tassociated RHS\n\tfunc lte(rhs: RHS) -> Bool\n}\nextend Int: Add {\n\tfunc add(rhs: Int) -> Int { 0 }\n}\nextend Int: Subtract {\n\tfunc minus(rhs: Int) -> Int { 0 }\n}\nextend Int: Comparable {\n\tfunc lte(rhs: Int) -> Bool { true }\n}\nfunc fib(n) {\n\tif n <= 1 { return n }\n\treturn fib(n - 2) + fib(n - 1)\n}\nlet x = fib(24)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Int");
        assert_eq!(ty_of(&t, "fib"), "<T0: Add + Subtract + Comparable>(T0) -> T0");
    }

    #[test]
    fn generic_bound_call_at_two_types() {
        // Show.tlk shape (two conforming types through one bounded generic).
        let t = check(
            "// no-core\nprotocol Showy {\n\tfunc show() -> Int\n}\nstruct Fizz {\n\tlet a: Int\n}\nextend Fizz: Showy {\n\tfunc show() { self.a }\n}\nextend Int: Showy {\n\tfunc show() { 0 }\n}\nfunc printy<T: Showy>(s: T) { s.show() }\nprinty(123)\nprinty(Fizz(a: 1))",
        );
        assert_clean(&t);
    }

    // ----- Milestone 5: effects -----------------------------------------

    #[test]
    fn lexically_handled_effects_do_not_escape() {
        // The resolver routes each perform to its lexical handler; a handled
        // perform never reaches the function's latent row (the row-typing
        // reading of handler discharge, Leijen POPL 2017).
        let t = check(
            "// no-core\neffect 'oops(e) -> Never\n@handle 'oops { e in 0 }\nfunc safe() {\n\t'oops(1)\n\t2\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "safe"), "() -> Int");
    }

    #[test]
    fn unhandled_effects_grow_the_latent_row() {
        let t = check(
            "// no-core\neffect 'oops(e) -> Never\nfunc risky() {\n\t'oops(1)\n\t2\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "risky"), "() -> Int ! <'oops>");
    }

    #[test]
    fn closed_effect_annotation_rejects_undeclared_effects() {
        let t = check(
            "// no-core\neffect 'a() -> ()\neffect 'b() -> ()\nfunc f() 'a -> () {\n\t'b()\n}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("'b"), "{errors:?}");
    }

    #[test]
    fn closed_effect_annotation_accepts_declared_effects() {
        let t = check(
            "// no-core\neffect 'a() -> ()\nfunc f() 'a -> () {\n\t'a()\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn handler_parameters_infer_from_perform_sites() {
        // `effect 'oops(e)` has no annotation: the perform's argument and the
        // handler's parameter meet in the effect signature's shared
        // placeholder, so both get Int here.
        let t = check(
            "// no-core\neffect 'oops(e) -> Never\nfunc wants(i: Int) { i }\n@handle 'oops { e in wants(e) }\n'oops(123)",
        );
        assert_clean(&t);
    }

    #[test]
    fn handler_parameter_type_conflicts_error() {
        let t = check(
            "// no-core\neffect 'oops(e) -> Never\nfunc wants(i: Int) { i }\n@handle 'oops { e in wants(e) }\n'oops(1.5)",
        );
        assert_eq!(type_errors(&t).len(), 1, "{:?}", type_errors(&t));
    }

    // ----- Projection types (associated type synonyms) ------------------

    #[test]
    fn projections_reduce_at_concrete_instantiation() {
        // mk's return is the projection T.D (Chakravarty et al., ICFP 2005);
        // instantiating T at Int normalizes it through Int's conformance.
        let t = check(
            "// no-core\nprotocol Defaulted {\n\tassociated D\n\tfunc make() -> D\n}\nextend Int: Defaulted {\n\tfunc make() -> Bool { true }\n}\nfunc mk<T: Defaulted>(t: T) { t.make() }\nlet v = mk(123)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "mk"), "<T0: Defaulted>(T0) -> T0.D");
        assert_eq!(ty_of(&t, "v"), "Bool");
    }

    #[test]
    fn projections_on_the_same_param_are_consistent() {
        let t = check(
            "// no-core\nprotocol Defaulted {\n\tassociated D\n\tfunc make() -> D\n}\nfunc two<T: Defaulted>(t: T) {\n\tlet a = t.make()\n\tlet b = t.make()\n\tif true { a } else { b }\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn projections_reject_unprovable_equalities_on_rigid_params() {
        // `a + 1` inside `<T: Add>` claims T.RHS = Int, which no bound
        // states; type families are not injective and rigid projections
        // only equal themselves (OutsideIn(X) treats F as a free function
        // symbol) — so this must error rather than silently hold.
        let t = check(
            "// no-core\nprotocol Add {\n\tassociated RHS\n\tassociated Ret\n\tfunc add(rhs: RHS) -> Ret\n}\nfunc bad<T: Add>(a: T) { a + 1 }",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("RHS"), "{errors:?}");
    }

    // ----- Protocol default bodies ---------------------------------------

    #[test]
    fn default_bodies_are_checked() {
        let t = check(
            "// no-core\nprotocol P {\n\tfunc base() -> Int\n\tfunc doubled() -> Int {\n\t\tself.base()\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn default_body_type_errors_are_reported() {
        let t = check(
            "// no-core\nprotocol P {\n\tfunc base() -> Int\n\tfunc doubled() -> Int {\n\t\t1.5\n\t}\n}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
    }

    #[test]
    fn default_bodies_use_associated_types_rigidly() {
        // Inside the default, `self.get()` types at the protocol's own
        // associated param (checked once, generically over Self — the
        // class-default treatment of Wadler & Blott's translation).
        let t = check(
            "// no-core\nprotocol Q {\n\tassociated A\n\tfunc get() -> A\n\tfunc also() -> A {\n\t\tself.get()\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn logical_operators_type_as_bool() {
        // `a || b` desugars to an if/else whose blocks hold bare
        // `Node::Expr`s (not statements) — the block walker must value them.
        let t = check("// no-core\nlet a = true\nlet b = false\nlet c = a || b\nlet d = a && b");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "c"), "Bool");
        assert_eq!(ty_of(&t, "d"), "Bool");
    }

    #[test]
    fn instantiations_recorded_at_call_sites() {
        let t = check("// no-core\nfunc identity(x) { x }\nlet a = identity(123)");
        assert_clean(&t);
        let instantiations = &t.phase.types.instantiations;
        let int_instantiation = instantiations.values().any(|subst| {
            subst
                .iter()
                .any(|(_, ty)| ty.render_mono() == "Int")
        });
        assert!(
            int_instantiation,
            "expected an instantiation at Int, got: {instantiations:?}"
        );
    }
}


#[cfg(test)]
mod with_core {
    use crate::compiling::driver::{Driver, DriverConfig, Source, Typed};
    use crate::diagnostic::AnyDiagnostic;

    /// Check a source against the full core prelude.
    fn check_with_core(source: Source) -> Driver<Typed> {
        let driver = Driver::new(vec![source], DriverConfig::new("WithCore"));
        driver
            .parse()
            .expect("parse failed")
            .resolve_names()
            .expect("resolve failed")
            .type_check()
    }

    fn type_errors(driver: &Driver<Typed>) -> Vec<String> {
        driver
            .phase
            .diagnostics
            .iter()
            .filter_map(|d| match d {
                AnyDiagnostic::Types(diag) => Some(format!("{:?}: {}", diag.id, diag.kind)),
                _ => None,
            })
            .collect()
    }

    fn example(name: &str) -> Source {
        let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join(name);
        Source::from(path)
    }

    /// Every example in examples/ type-checks clean against the core
    /// prelude. (AnonFunc.tlk currently parses its trailing `(123)` as a
    /// separate grouped statement — a parser gap noted for the lowerer
    /// milestones — but it checks clean either way.)
    const CLEAN_EXAMPLES: &[&str] = &[
        "AnonFunc.tlk",
        "Array.tlk",
        "Capture.tlk",
        "ChatClient.tlk",
        "ChatServer.tlk",
        "Effects.tlk",
        "Exports.tlk",
        "Fib.tlk",
        "FileIO.tlk",
        "ForLoop.tlk",
        "HelloWorld.tlk",
        "Http.tlk",
        "Identity.tlk",
        "Imports.tlk",
        "Iteratin.tlk",
        "Loop.tlk",
        "MatchBind.tlk",
        "Protocols.tlk",
        "Show.tlk",
        "Sleep.tlk",
        "Strings.tlk",
        "Struct.tlk",
        "StructuralTyping.tlk",
        "Sum.tlk",
        "TrailingBlock.tlk",
        "WebApi.tlk",
        "Website.tlk",
    ];

    #[test]
    fn every_example_type_checks_clean() {
        let mut failures = vec![];
        for name in CLEAN_EXAMPLES {
            let typed = check_with_core(example(name));
            let errors = type_errors(&typed);
            if !errors.is_empty() {
                failures.push(format!("{name}: {errors:?}"));
            }
        }
        assert!(
            failures.is_empty(),
            "examples with errors:\n{}",
            failures.join("\n")
        );
    }

    #[test]
    fn external_module_types_cross_the_boundary() {
        // Compile module A, import it into module B as an external module:
        // A's schemes and catalog must arrive with symbols remapped to B's
        // view of A (milestone 6).
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let driver_a = Driver::new(
            vec![Source::from(
                "public struct Hello {\n\tlet x: Int\n}\npublic func make(v: Int) -> Hello { Hello(x: v) }",
            )],
            DriverConfig::new("A"),
        );
        let module_a = driver_a
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check()
            .module("A");

        let mut modules = ModuleEnvironment::default();
        modules.import(module_a);
        let config = crate::compiling::driver::DriverConfig {
            module_id: ModuleId::Current,
            modules: Rc::new(modules),
            mode: crate::compiling::driver::CompilationMode::Library,
            module_name: "B".to_string(),
            parse_mode: crate::compiling::driver::ParseMode::Strict,
            preserve_comments: false,
        };
        let driver_b = Driver::new(vec![Source::from("let v = make(3).x\nlet bad: Int = make(3)")], config);
        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        let errors = type_errors(&typed);
        // `v` is fine; `bad` is a real mismatch (Hello is not Int) — which
        // proves the imported types are actually being applied.
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("Hello"), "{errors:?}");
        let resolved = &typed.phase.resolved_names;
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let v = resolved
            .symbol_names
            .iter()
            .find(|(sym, n)| n.as_str() == "v" && typed.phase.types.schemes.contains_key(sym))
            .map(|(sym, _)| *sym)
            .expect("v scheme");
        assert_eq!(typed.phase.types.schemes[&v].render(), "Int");
    }

    #[test]
    fn fib_against_core_is_int() {
        let typed = check_with_core(Source::from("let x = fib(24)\nfunc fib(n) {\n\tif n <= 1 { return n }\n\treturn fib(n - 2) + fib(n - 1)\n}"));
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
        let resolved = &typed.phase.resolved_names;
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let symbol = resolved
            .symbol_names
            .iter()
            .find(|(sym, n)| n.as_str() == "x" && typed.phase.types.schemes.contains_key(sym))
            .map(|(sym, _)| *sym)
            .expect("x scheme");
        assert_eq!(typed.phase.types.schemes[&symbol].render(), "Int");
    }
}
