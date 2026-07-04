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
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
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
        types_with_severity(driver, crate::diagnostic::Severity::Error)
    }

    pub fn type_warnings(driver: &Driver<Typed>) -> Vec<String> {
        types_with_severity(driver, crate::diagnostic::Severity::Warn)
    }

    fn types_with_severity(
        driver: &Driver<Typed>,
        severity: crate::diagnostic::Severity,
    ) -> Vec<String> {
        driver
            .phase
            .diagnostics
            .iter()
            .filter_map(|d| match d {
                AnyDiagnostic::Types(diag) if diag.severity == severity => {
                    Some(diag.kind.to_string())
                }
                _ => None,
            })
            .collect()
    }

    pub fn assert_clean(driver: &Driver<Typed>) {
        let errors = type_errors(driver);
        assert!(
            errors.is_empty(),
            "expected no type errors, got: {errors:?}"
        );
    }

    /// The previous type checker's suite, replayed against this one
    /// (every case dispositioned in docs/parity-test-audit.md; the
    /// handful tied to changed semantics or known gaps are listed
    /// there instead of here).
    #[test]
    fn previous_checker_suite_behaviors_hold() {
        // (name, source, expect_clean, with_core_prelude)
        let cases: &[(&str, &str, bool, bool)] = &[
            (
                "types::row_projection_polymorphic",
                "\n        func fstA(r) { r.a }\n        (fstA({ a: 1 }), fstA({ a: 2, b: true }))\n    ",
                true,
                false,
            ),
            (
                "types::row_presence_constraint_is_polymorphic",
                "\n        func useA(r) { r.a } // imposes HasField(row_var, \"a\", Int)\n        (useA({ a: 1 }), useA({ a: 2, c: true }))\n    ",
                true,
                false,
            ),
            (
                "types::types_non_annotated_record_param",
                "\n        func foo(x) {\n            (x.y, x.z)\n        }\n\n        foo({ y: 123, z: 1.23 })\n        foo({ y: 123, z: 123 })\n        ",
                true,
                false,
            ),
            (
                "types::checks_generic_struct_arg",
                "\n        struct Person {\n            func getAge<T>(t: T) -> T { t }\n        }\n\n        Person().getAge(123)\n        Person().getAge(1.23)\n        ",
                true,
                false,
            ),
            (
                "types::types_enum_instance_methods",
                "\n            enum Fizz<T> {\n                case foo(T), bar(T)\n\n                func unwrap() {\n                    match self {\n                        Fizz.foo(t) -> t,\n                        Fizz.bar(t) -> t\n                    }\n                }\n            }\n\n            Fizz.foo(123).unwrap()\n            ",
                true,
                false,
            ),
            (
                "types::record_field_func_generalizes_with_row_forall",
                "\n            func getX(r) { r.x }\n            getX({ x: 1 })\n            ",
                true,
                false,
            ),
            ("types::types_int_literal", "123", true, false),
            ("types::types_int", "let a = 123; a", true, false),
            ("types::types_float", "let a = 1.23; a", true, false),
            (
                "types::types_bool",
                "let a = true; a ; let b = false ; b",
                true,
                false,
            ),
            ("types::types_string", "\"hello\"", true, false),
            (
                "types::types_string_concat",
                "\"hello\" + \"world\"",
                true,
                true,
            ),
            (
                "types::types_string_slice",
                "\"hello\".slice(1, 3)",
                true,
                true,
            ),
            (
                "types::types_string_find",
                "\"hello\".find(\"ll\"); \"hello\".find_from(\"l\", 3)",
                true,
                true,
            ),
            ("types::types_equals_int", "1 == 2; 1 != 2", true, true),
            (
                "types::types_equals_float",
                "1.0 == 2.0; 1.0 != 2.0",
                true,
                true,
            ),
            (
                "types::types_equals_string",
                "\"hello\" == \"world\" ; \"hello\" != \"world\"",
                true,
                true,
            ),
            (
                "types::types_array_literal",
                "[1,2,3]; [1.2, 3.4, 5.6]",
                true,
                true,
            ),
            (
                "types::types_ir_builtin",
                "__IR<Int>(\"add int 1 2\"); __IR<Float>(\"add int 1 2\")",
                true,
                false,
            ),
            (
                "types::types_alloc",
                "// unsafe\nlet x: RawPtr = __IR(\"$? = alloc int 1\"); x",
                true,
                false,
            ),
            ("types::types_array_properties", "[1,2,3].count", true, true),
            (
                "types::types_basic_binary",
                "func a(x) { x + 1 } ; a(123)",
                true,
                true,
            ),
            (
                "types::let_again",
                "\n        let a = 123\n        let a = 1.23\n        a\n    ",
                true,
                false,
            ),
            (
                "types::monomorphic_let_annotation",
                "\n        let a: Int = 123\n        a\n    ",
                true,
                false,
            ),
            (
                "types::monomorphic_let_annotation_mismatch",
                "\n        let a: Bool = 123\n        a\n    ",
                false,
                false,
            ),
            (
                "types::types_identity",
                "\n        func identity(x) { x }\n        identity(123)\n        identity(true)\n        ",
                true,
                false,
            ),
            (
                "types::stores_func_instantiations",
                "\n        func identity(x) { x }\n        identity(123)\n        identity(true)\n        ",
                true,
                false,
            ),
            (
                "types::stores_struct_instantiations",
                "\n        struct Wrapper<T> {\n            let wrapped: T\n        }\n        Wrapper(wrapped: 123)\n        Wrapper(wrapped: true)\n        ",
                true,
                false,
            ),
            (
                "types::types_nested_func",
                "\n        func fizz(x) {\n            func buzz() { x }\n            buzz()\n        }\n\n        fizz(123)\n        ",
                true,
                false,
            ),
            (
                "types::infers_simple_recursion",
                "\n        func rec(x, y, z) {\n            if x == y { x } else { rec(y-z, y, z) }\n        }\n\n        rec(0, 2, 1)\n        rec(0.0, 2.0, 1.0)\n        ",
                true,
                true,
            ),
            (
                "types::explicit_generic_function_instantiates",
                "\n        func id<T>(x: T) -> T { x }\n        id(123)\n        id(true)\n    ",
                true,
                false,
            ),
            (
                "types::explicit_call_args",
                "\n        func id<T>(x) { x }\n        id<Byte>(123)\n    ",
                true,
                false,
            ),
            (
                "types::generic_function_body_must_respect_its_own_type_vars",
                "\n        func bad<T>(x: T) -> T { 0 } // 0 == Int != T\n        bad(true)\n    ",
                false,
                false,
            ),
            (
                "types::types_call_let",
                "\n        func id(x) { x }\n        let a = id(123)\n        let b = id(1.23)\n        a\n        b\n        ",
                true,
                false,
            ),
            (
                "types::types_nested_identity",
                "\n        func identity(x) { x }\n        identity(identity(123))\n        identity(identity(true))\n        ",
                true,
                false,
            ),
            (
                "types::types_multiple_args",
                "\n        func makeTuple(x, y) {\n            (x, y)\n        }\n\n        makeTuple(123, true)\n            ",
                true,
                false,
            ),
            (
                "types::checks_returns_agree",
                "\n            func fizz() {\n                return 123\n                1.23\n            }\n            ",
                false,
                false,
            ),
            (
                "types::types_single_tuple_value",
                "\n        let z = (123)\n        z\n        ",
                true,
                false,
            ),
            (
                "types::types_tuple_value",
                "\n        let z = (123, true)\n        z\n        ",
                true,
                false,
            ),
            (
                "types::types_tuple_assignment",
                "\n        let z = (123, 1.23)\n        let (x, y) = z\n        x\n        y\n        ",
                true,
                false,
            ),
            (
                "types::types_record_assignment",
                "\n        let z = { x: 1, y: 1.23 }\n        let { x, y } = z\n        x\n        y\n        ",
                true,
                false,
            ),
            (
                "types::types_if_expr",
                "\n        let z = if true { 123 } else { 456 }\n        z\n        ",
                true,
                false,
            ),
            (
                "types::requires_if_expr_cond_to_be_bool",
                "\n        let z = if 123 { 123 } else { 456 }\n        z\n        ",
                false,
                false,
            ),
            (
                "types::requires_if_expr_arms_to_match",
                "\n        let z = if true { 123 } else { false }\n        z\n        ",
                false,
                false,
            ),
            (
                "types::requires_if_stmt_cond_to_be_bool",
                "\n        if 123 { 123 }\n        ",
                false,
                false,
            ),
            (
                "types::types_match",
                "\n        match 123 {\n            123 -> true,\n            456 -> false,\n            _ -> true\n        }\n        ",
                true,
                false,
            ),
            (
                "types::types_match_binding",
                "\n        match 123 {\n            a -> a,\n        }\n        ",
                true,
                false,
            ),
            (
                "types::checks_match_pattern_type",
                "\n        match 123 {\n            true -> false,\n        }\n        ",
                false,
                false,
            ),
            (
                "types::checks_or_pattern",
                "\n        match 123 {\n            123 | true -> true,\n            _ -> false\n        }\n        ",
                false,
                false,
            ),
            (
                "types::checks_tuple_match",
                "\n        match (123, true) {\n            (a, b) -> (b, a),\n        }\n        ",
                true,
                false,
            ),
            (
                "types::checks_loop_cond_is_bool",
                "\n        loop 123 {}\n        ",
                false,
                false,
            ),
            (
                "types::checks_assignment",
                "\n        let bool = true\n        bool = 123\n        ",
                false,
                false,
            ),
            (
                "types::call_time_type_args_are_checked",
                "\n        func id<T>(x: T) -> T { x }\n        id<Bool>(123)\n    ",
                false,
                false,
            ),
            (
                "types::match_arms_must_agree_on_result_type",
                "\n        match 123 {\n            123 -> 1,\n            456 -> true,\n        }\n    ",
                false,
                false,
            ),
            (
                "types::param_annotation_is_enforced_at_call",
                "\n        func f(x: Int) -> Int { x }\n        f(true)\n    ",
                false,
                false,
            ),
            (
                "types::return_annotation_is_enforced_in_body",
                "\n        func f(x: Int) -> Int { true }\n        f(1)\n    ",
                false,
                false,
            ),
            (
                "types::types_recursive_func",
                "\n        func fizz(n) {\n            if true {\n                123\n            } else {\n                fizz(n)\n            }\n        }\n\n        fizz(456)\n        ",
                true,
                false,
            ),
            (
                "types::recursion_is_monomorphic_within_binding_group",
                "\n        func g(x) {\n            // Force a shape change on the recursive call to try to “polymorphically” recurse.\n            g( (x, x) )\n        }\n        g(1)\n    ",
                false,
                false,
            ),
            (
                "types::tuple_type_annotation_on_let_is_honored",
                "\n        let z: (Int, Bool) = (123, true)\n        z\n    ",
                true,
                false,
            ),
            (
                "types::concrete_func_type_annotation_works",
                "\n        let first: (Int, Bool) -> Int = func(a, b) { a }\n        first(1, true)\n    ",
                true,
                false,
            ),
            (
                "types::let_generalization_for_value_bindings",
                "\n        let id = func(x) { x }\n        (id(123), id(true))\n    ",
                true,
                false,
            ),
            (
                "types::types_record_literal",
                "\n        let rec = { a: true, b: 123, c: 1.23 }\n        rec\n        ",
                true,
                false,
            ),
            (
                "types::types_record_type_out_of_order",
                "\n        let x: { a: Int, b: Bool } = { b: true, a: 1 }\n        x\n        ",
                true,
                false,
            ),
            (
                "types::types_record_member",
                "\n        let rec = { a: true, b: 123, c: 1.23 }\n        rec.a\n        rec.b\n        rec.c\n        ",
                true,
                false,
            ),
            (
                "types::types_nested_record",
                "\n        let rec = { a: { b: { c: 1.23 } } }\n        rec.a.b.c\n        ",
                true,
                false,
            ),
            (
                "types::types_record_pattern_out_of_order",
                "\n        let rec = { a: 123, b: true }\n        match rec {\n            { b, a } -> (a, b)\n        }\n        ",
                true,
                false,
            ),
            (
                "types::types_record_pattern_with_equalities",
                "\n        let rec = { a: 123, b: true }\n        match rec {\n            { a: 123, b } -> b,\n            _ -> false,\n        }\n        ",
                true,
                false,
            ),
            (
                "types::type_nested_record_pattern",
                "\n        let rec = { a: 123, b: { c: true } }\n        match rec {\n            { a, b: { c } } -> c\n        }\n        ",
                true,
                false,
            ),
            (
                "types::checks_fields_exist",
                "\n        let rec = { a: 123, b: true }\n        match rec {\n            { a, c } -> (a, c)\n        }\n        ",
                false,
                false,
            ),
            (
                "types::checks_field_types",
                "\n        let rec = { a: 123 }\n        match rec {\n            { a: true } -> ()\n        }\n        ",
                false,
                false,
            ),
            (
                "types::row_id_generalizes_and_instantiates",
                "\n        let id = func id(r) { r }\n        // project different fields from differently-shaped records\n        (id({ a: 1 }).a, id({ b: true }).b)\n    ",
                true,
                false,
            ),
            (
                "types::row_env_tail_not_generalized_in_local_let",
                "\n        func outer(r) {\n            let _x = r.a;               // forces r to have field `a`\n            let k  = func() { r };      // returns the *same* env row (no row-generalization)\n            match k() {\n                { c } -> c              // `c` is not known; should produce one error\n            }\n        }\n        outer({ a: 1 })\n    ",
                false,
                false,
            ),
            (
                "types::row_instantiation_stability_across_uses",
                "\n        let id = func id(r) { r }\n        let x  = id({ a: 1, b: true });\n        (x.a, x.b)\n    ",
                true,
                false,
            ),
            (
                "types::row_meta_levels_prevent_leak",
                "\n        func outer(r) {\n            let x = r.a; // creates an internal Row::Var tail for r's row (your ensure_row/projection does this)\n            let k = func() { r } // local let; do NOT generalize the outer row var into a Row::Param\n            match k() {\n                { c } -> c // should be a missing-field error (no 'c' in r)\n            }\n        }\n        outer({ a: 1 })\n    ",
                false,
                false,
            ),
            (
                "types::types_row_type_as_params",
                "\n        func foo(x: { y: Int, z: Bool }) {\n            (x.y, x.z)\n        }\n\n        foo({ y: 123, z: true })\n        ",
                true,
                false,
            ),
            (
                "types::enforces_non_annotated_record",
                "\n        func foo(point) {\n            (point.x, point.y)\n        }\n\n        foo({ x: 123, z: 123 })\n        ",
                false,
                false,
            ),
            (
                "types::enforces_row_type_as_params",
                "\n        func foo(x: { y: Int, z: Bool }) {\n            (x.y, x.z)\n        }\n\n        foo({ y: 123 })\n        ",
                false,
                false,
            ),
            (
                "types::types_struct_constructor",
                "\n        struct Person {\n            let age: Int\n            let height: Float\n        }\n\n        Person(age: 123, height: 1.23)\n        ",
                true,
                false,
            ),
            (
                "types::types_struct_referencing_another_struct",
                "\n        struct A {\n            let count: Int\n        }\n\n        struct B {\n            let a: A\n        }\n\n        B(a: A(count: 1)).a.count\n        ",
                true,
                false,
            ),
            (
                "types::types_struct_member_access",
                "\n        struct Person {\n            let age: Int\n            let height: Float\n        }\n\n        Person(age: 123, height: 1.23).age\n        ",
                true,
                false,
            ),
            (
                "types::type_generic_struct",
                "\n        struct Person<T> {\n            let age: T\n        }\n\n        Person(age: 123).age\n        ",
                true,
                false,
            ),
            (
                "types::checks_struct_init_args",
                "\n        struct Person {\n            let age: Int\n\n            // init(age: Int) {\n            //     self.age = age\n            // }\n        }\n\n        Person(age: 1.23)\n        ",
                false,
                false,
            ),
            (
                "types::types_generic_struct_init",
                "\n        struct Person<T> {\n            let age: T\n\n            init(other: T) {\n                self.age = other\n            }\n        }\n\n        Person(age: 123).age\n        ",
                true,
                false,
            ),
            (
                "types::types_static_struct_methods",
                "\n        struct Person {\n           static func getAge() { 123 }\n        }\n\n        Person.getAge()\n        ",
                true,
                false,
            ),
            (
                "types::type_struct_method",
                "\n        struct Person {\n            let age: Int\n\n            func getAge() {\n                self.age\n            }\n        }\n\n        Person(age: 123).getAge()\n        ",
                true,
                false,
            ),
            (
                "types::types_explicit_type_application",
                "\n          struct Boxy<T> { let value: T }\n\n          // Explicit type application\n          let x: Boxy<Int> = Boxy(value: 42)\n          let y: Boxy<Float> = Boxy(value: 3.14)\n\n          x\n          ",
                true,
                false,
            ),
            (
                "types::checks_struct_method_on_arg",
                "\n        struct Person {\n            let age: Int\n        }\n\n        let person = Person(age: 123)\n        callNonExisting(person)\n\n        func callNonExisting(aged) {\n            aged.getAge()\n        }\n        ",
                false,
                false,
            ),
            (
                "types::types_generic_struct_method",
                "\n        struct Wrapper<T> {\n            let wrapped: T\n\n            consuming func getWrapped() {\n                self.wrapped\n            }\n        }\n\n        Wrapper(wrapped: 123).getWrapped()\n        Wrapper(wrapped: 1.23).getWrapped()\n        ",
                true,
                false,
            ),
            (
                "types::types_nested_generic_struct_method",
                "\n\n        struct Inner<T> {\n            let inner: T\n        }\n        struct Middle<T> {\n            let middle: T\n        }\n        struct Outer<T> {\n            let outer: T\n        }\n\n        let inner = Inner(inner: true)\n        let middle = Middle(middle: inner)\n        let outer = Outer(outer: middle)\n\n        outer.outer.middle.inner\n        inner.inner\n        ",
                true,
                false,
            ),
            (
                "types::types_simple_enum_constructor",
                "\n            enum Fizz {\n                case foo, bar\n            }\n\n            Fizz.foo\n            Fizz.bar\n        ",
                true,
                false,
            ),
            (
                "types::types_enum_constructor_with_values",
                "\n            enum Fizz {\n                case foo(Int, Bool), bar(Float)\n            }\n\n            Fizz.foo(123, true)\n            Fizz.bar(1.23)\n        ",
                true,
                false,
            ),
            (
                "types::types_enum_constructor_with_generic_value",
                "\n            enum Opt<T> {\n                case some(T), none\n            }\n\n            Opt.some(123)\n            Opt.some(1.23)\n            Opt.none\n        ",
                true,
                false,
            ),
            (
                "types::types_simple_enum_match",
                "\n            enum Fizz {\n                case foo, bar\n            }\n\n            match Fizz.foo {\n                Fizz.foo -> 1,\n                Fizz.bar -> 2\n            }\n            ",
                true,
                false,
            ),
            (
                "types::types_nested_enum_match",
                "\n            enum Fizz<T> {\n                case foo(T)\n            }\n\n            match Fizz.foo(Fizz.foo(123)) {\n                Fizz.foo(Fizz.foo(x)) -> x,\n            }\n            ",
                true,
                false,
            ),
            (
                "types::types_unqualified_variant",
                "\n            enum Fizz {\n                case foo(Int), bar(Int)\n            }\n\n            match Fizz.foo(123) {\n                .foo(x) -> x,\n                .bar(y) -> y\n            }\n            ",
                true,
                false,
            ),
            (
                "types::types_unqualified_variant_as_param",
                "\n            enum Fizz {\n                case foo(Int), bar(Int)\n            }\n\n            func buzz(fizz: Fizz) {\n                match fizz {\n                    .foo(x) -> x,\n                    .bar(y) -> y\n                }\n            }\n\n            buzz(fizz: .foo(123))\n            ",
                true,
                false,
            ),
            (
                "types::checks_or_pattern_in_let",
                "\n          enum Result<T, E> {\n              case ok(T)\n              case err(E)\n          }\n\n          let .ok(x) | .err(x) = Result.ok(42)\n          x\n          ",
                true,
                false,
            ),
            (
                "types::checks_nested_or_patterns",
                "\n          enum Outer {\n              case a(Inner)\n              case b(Inner)\n          }\n\n          enum Inner {\n              case x(Int)\n              case y(Int)\n          }\n\n          func extract(o: Outer) -> Int {\n              match o {\n                  .a(.x(n) | .y(n)) | .b(.x(n) | .y(n)) -> n\n              }\n          }\n\n          extract(Outer.a(Inner.x(99)))\n          ",
                true,
                false,
            ),
            (
                "types::rejects_unbounded_associated_type_projection",
                "\n            func bad<T>(x: T) -> T.Item {\n                x\n            }\n            ",
                false,
                false,
            ),
            (
                "types::rejects_unknown_associated_type_projection_on_protocol_bound",
                "\n            protocol Aged {\n                associated T\n            }\n\n            func bad<A: Aged>(x: A) -> A.U {\n                x\n            }\n            ",
                false,
                false,
            ),
            (
                "types::rejects_unknown_nominal_type_member",
                "\n            struct Box {}\n\n            func bad() -> Box.Item {\n                1\n            }\n            ",
                false,
                false,
            ),
            (
                "types::rejects_nested_unknown_nominal_type_member",
                "\n            struct A {\n                typealias B = Int\n            }\n\n            func f() -> A.B.C {\n                1\n            }\n            ",
                false,
                false,
            ),
            (
                "types::types_simple_conformance",
                "\n            protocol Countable {\n                func getCount() -> Int\n            }\n\n            struct Person {}\n\n            extend Person: Countable {\n                func getCount() {\n                    123\n                }\n            }\n            ",
                true,
                false,
            ),
            (
                "types::records_conformance_claim_associated_type_candidates",
                "\n            protocol HasItem {\n                associated Item\n                func getItem() -> Int\n            }\n\n            struct Box {}\n\n            extend Box: HasItem {\n                typealias Item = Int\n                func getItem() { 1 }\n            }\n            ",
                true,
                false,
            ),
            (
                "types::rejects_missing_concrete_conformance_for_generic_bound",
                "\n            protocol Marker {\n                func mark() -> Int\n            }\n\n            struct Foo {}\n\n            func takes<T: Marker>(x: T) {}\n\n            takes(Foo())\n            ",
                false,
                false,
            ),
            (
                "types::rejects_missing_marker_conformance_without_requirements",
                "\n            protocol Marker {}\n\n            struct Foo {}\n\n            func takes<T: Marker>(x: T) {}\n\n            takes(Foo())\n            ",
                false,
                false,
            ),
            (
                "types::generic_constructor_in_extension_block",
                "\n          struct Wrapper<T> {\n              let value: T\n\n              init(value: T) {\n                  self.value = value\n              }\n          }\n\n          struct Box<T> {\n              let inner: T\n          }\n\n          extend Box<T> {\n              consuming func wrap() -> Wrapper<T> {\n                  Wrapper<T>(value: self.inner)\n              }\n          }\n          ",
                true,
                false,
            ),
            (
                "types::generic_constructor_with_explicit_type_arg",
                "\n          struct Container<Element> {\n              let item: Element\n\n              init(item: Element) {\n                  self.item = item\n              }\n          }\n\n          struct MyList<Element> {\n              let first: Element\n          }\n\n          extend MyList<Element> {\n              consuming func boxFirst() -> Container<Element> {\n                  Container<Element>(item: self.first)\n              }\n          }\n          ",
                true,
                false,
            ),
            (
                "types::checks_method_protocol_conformance",
                "\n            protocol Countable {\n                func getCount() -> Int\n            }\n\n            struct Person {}\n\n            extend Person: Countable {\n                func getCount() -> Float {\n                    1.123 // This is wrong\n                }\n            }\n        ",
                false,
                false,
            ),
            (
                "types::checks_protocol_method",
                "\n            protocol Countable {\n                func getCount() -> Int\n                func getOtherCount() {\n                    self.getCount()\n                }\n            }\n\n            struct Person {}\n\n            extend Person: Countable {\n                func getCount() { 123 }\n            }\n\n            Person().getOtherCount()\n        ",
                true,
                false,
            ),
            (
                "types::types_simple_protocol",
                "\n            protocol Countable { func getCount() -> Int }\n            struct Person { let count: Int }\n            extend Person: Countable {\n                func getCount() {\n                    self.count\n                }\n            }\n\n            func getCount<T: Countable>(countable: T) {\n                countable.getCount()\n            }\n\n            let person = Person(count: 1)\n            getCount(person)\n            ",
                true,
                false,
            ),
            (
                "types::tests_infers_associated_types",
                "\n        protocol Aged {\n            associated T\n\n            func getAge() -> T\n        }\n\n        struct Inty {}\n        extend Inty: Aged {\n            func getAge() {\n                123\n            }\n        }\n\n        struct Floaty {}\n        extend Floaty: Aged {\n            func getAge() {\n                1.23\n            }\n        }\n\n        func get<A: Aged>(aged: A) {\n            aged.getAge()\n        }\n\n        get(Inty())\n        get(Floaty())\n        ",
                true,
                false,
            ),
            (
                "types::can_extend_builtins",
                "\n        protocol Foo {\n            func foo() -> Int\n        }\n        extend Int: Foo {\n            func foo() { 123 }\n        }\n        1.foo()\n        ",
                true,
                false,
            ),
            (
                "types::add_protocol_prototype",
                "\n        protocol Addy {\n            associated RHS\n            associated Ret\n            consuming func addy(rhs: RHS) -> Ret\n        }\n\n        extend Int: Addy {\n            consuming func addy(rhs: Int) -> Int {\n                self\n            }\n        }\n\n        1.addy(2)\n        ",
                true,
                false,
            ),
            (
                "types::includes_core_optional",
                "\n        enum Opt<T> {\n            case some(T), none\n        }\n\n        Optional.some(123)\n        Opt.some(1.23)\n        ",
                true,
                true,
            ),
            (
                "types::types_plus",
                "\n        1 + 2\n        1.0 + 2.0\n        ",
                true,
                true,
            ),
            (
                "types::checks_plus",
                "\n        let a: Int = 123\n        let b: Float = 1.23\n        let c = a + b\n        ",
                false,
                true,
            ),
            (
                "types::types_minus",
                "\n        1 - 2\n        1.0 - 2.0\n        ",
                true,
                true,
            ),
            (
                "types::types_multiplication",
                "\n        1 * 2\n        1.0 * 2.0\n        ",
                true,
                true,
            ),
            (
                "types::types_division",
                "\n        1 / 2\n        1.0 / 2.0\n        ",
                true,
                true,
            ),
            (
                "types::types_comparisons",
                "\n        1 == 2\n        1.0 == 2.0\n        1 > 2\n        1 >= 2\n        1 < 2\n        1 <= 2\n        1 < 2 && 2 < 3\n        1 < 2 || 2 < 3\n        ",
                true,
                true,
            ),
            (
                "types::types_custom_add",
                "\n        struct A {}\n        struct B {}\n        struct C {}\n        extend A: Add {\n            func add(rhs: B) -> C {\n                C()\n            }\n        }\n        A() + B()\n        ",
                true,
                true,
            ),
            (
                "types::types_add_method_in_func",
                "func add(x) { x + 1 }\n\n            add(2)\n            ",
                true,
                true,
            ),
            (
                "types::check_as",
                "\n        protocol Fizz {\n            func fizz() -> Int\n            func buzz() -> Int {\n                self.fizz()\n            }\n        }\n\n        struct A {}\n\n        A() as Fizz\n        ",
                false,
                false,
            ),
            (
                "types::checks_basic_conformance",
                "\n        protocol A {\n            func fizz() -> Int\n        }\n\n        struct B {}\n        extend B: A {} \n        ",
                false,
                false,
            ),
            (
                "types::protocols_on_protocols",
                "\n        protocol A {\n            func fizz() -> Int\n        }\n\n        protocol B: A {\n            func buzz() -> Int\n        }\n\n        func get<T: B>(t: T) {\n            t.fizz()\n        }\n        ",
                true,
                false,
            ),
            (
                "types::types_fib",
                "\n        func fib(n) {\n            if n <= 1 { return n }\n\n            return fib(n - 2) + fib(n - 1)\n        }\n\n        fib(3)\n        ",
                true,
                true,
            ),
            (
                "types::tracks_transitive_witnesses",
                "\n            protocol A {\n                func default() { 123 }\n            }\n\n            protocol B: A {\n                func callsDefault() { self.default() }\n            }\n\n            extend Int: B {}\n\n            123.callsDefault()\n        ",
                true,
                false,
            ),
            (
                "types::types_struct_call_regression",
                "\n            struct Person {\n                let firstName: String\n                let lastName: String\n\n                consuming func greet() {\n                    // Strings can be concat'd\n                    print(\"hi i'm \" + self.firstName + \" \" + self.lastName)\n                }\n            }\n\n            Person(firstName: \"Pat\", lastName: \"N\").greet()\n            ",
                true,
                true,
            ),
            (
                "types::types_associated_type_conformances",
                "\n            protocol Named {\n                func name() -> String\n            }\n\n            protocol Animal {\n                associated Food: Named\n\n                // Can call name() on Food because Food: Named\n                func feed(food: Food) {\n                    print(food.name())\n                }\n            }\n            ",
                true,
                true,
            ),
            (
                "types::types_nested_extend_conformance",
                "\n            protocol Counter {\n                func next() -> Int\n            }\n\n            struct MyCounter {\n                let value: Int\n\n                extend Self: Counter {\n                    func next() -> Int {\n                        self.value\n                    }\n                }\n            }\n\n            func useCounter<T: Counter>(c: T) -> Int {\n                c.next()\n            }\n\n            useCounter(MyCounter(value: 42))\n            ",
                true,
                false,
            ),
            (
                "types::nested_self_extend_can_use_protocol_default_method",
                "\n            protocol P {\n                func f() { 1 }\n            }\n\n            struct S {\n                extend Self: P {}\n            }\n\n            func call<T: P>(x: T) -> Int {\n                x.f()\n            }\n\n            call(S())\n            ",
                true,
                false,
            ),
            (
                "types::nested_self_extend_does_not_use_outer_method_as_witness",
                "\n            protocol P {\n                func f() -> Int\n            }\n\n            struct S {\n                func f() -> Int { 1 }\n\n                extend Self: P {}\n            }\n\n            func call<T: P>(x: T) -> Int {\n                x.f()\n            }\n\n            call(S())\n            ",
                false,
                false,
            ),
            (
                "types::types_nested_extend_with_enum_ref",
                "\n            protocol Getter {\n                func get() -> Int\n            }\n\n            enum Result<T> {\n                case ok(T)\n                case err\n            }\n\n            struct MyGetter {\n                let value: Int\n\n                extend Self: Getter {\n                    func get() -> Int {\n                        self.value\n                    }\n                }\n            }\n\n            Result.ok(123)\n            ",
                true,
                false,
            ),
            (
                "types::types_nested_extend_with_member_method_call",
                "\n            struct Inner {\n                let data: Int\n\n                func getData() -> Int {\n                    self.data\n                }\n            }\n\n            protocol Wrapper {\n                func getValue() -> Int\n            }\n\n            struct Outer {\n                let inner: Inner\n\n                extend Self: Wrapper {\n                    func getValue() -> Int {\n                        self.inner.getData()\n                    }\n                }\n            }\n            ",
                true,
                false,
            ),
            (
                "types::yield_is_not_available_as_a_builtin_anymore",
                "\n            yield(42)\n            ",
                false,
                true,
            ),
            (
                "types::types_func_literal_call_arg_with_contextual_param_type",
                "\n            func transform(x: Int, f: (Int) -> Int) -> Int {\n                f(x)\n            }\n            transform(1, func(n) { n })\n            ",
                true,
                false,
            ),
            (
                "types::types_func_literal_call_arg_return_mismatch_returns_error",
                "\n            func apply(f: () -> Int) -> Int {\n                f()\n            }\n            apply(func() { true })\n            ",
                false,
                false,
            ),
            (
                "types::types_trailing_block_as_function_arg",
                "\n            func apply(f: () -> Int) -> Int {\n                f()\n            }\n            apply(){ 123 }\n            ",
                true,
                false,
            ),
            (
                "types::types_trailing_block_with_params",
                "\n            func transform(x: Int, f: (Int) -> Int) -> Int {\n                f(x)\n            }\n            transform(1){ n in n }\n            ",
                true,
                false,
            ),
            (
                "types::finalize_ty_produces_correct_poly_entry",
                "\n            func id(x) { x }\n            id(123)\n            ",
                true,
                false,
            ),
            (
                "types::types_trailing_block_type_mismatch_returns_error",
                "\n            func apply(f: () -> Int) -> Int {\n                f()\n            }\n            apply(){ true }\n            ",
                false,
                false,
            ),
            (
                "types::if_let_binds_variables",
                "\n            enum Opt<T> { case some(T), none }\n            let val = Opt.some(42)\n            let result: Int = if let .some(x) = val { x } else { 0 }\n            ",
                true,
                false,
            ),
            (
                "types::if_let_unifies_arm_types",
                "\n            enum Opt<T> { case some(T), none }\n            let val = Opt.some(42)\n            if let .some(x) = val { x } else { true }\n            ",
                false,
                false,
            ),
            (
                "types::if_let_stmt_no_else",
                "\n            enum Opt<T> { case some(T), none }\n            func use_int(x: Int) {}\n            let val = Opt.some(42)\n            if let .some(x) = val { use_int(x) }\n            ",
                true,
                false,
            ),
            (
                "types::let_else_binds_in_enclosing_scope",
                "\n            enum Opt<T> { case some(T), none }\n            func f(val: Opt<Int>) -> Int {\n                let .some(x) = val else { return 0 }\n                x\n            }\n            ",
                true,
                false,
            ),
            (
                "types::let_else_body_is_typechecked",
                "\n            enum Opt<T> { case some(T), none }\n            func f(val: Opt<Int>) -> Int {\n                let .some(x) = val else { return true }\n                x\n            }\n            ",
                false,
                false,
            ),
            (
                "types::bounded_param_substitution_in_conditional_conformance",
                "\n            func printy<T: Showable>(showable: T) {\n                print_raw(showable.show())\n            }\n            printy([1, 2, 3])\n            ",
                true,
                true,
            ),
            (
                "types::rejects_tuple_annotation_with_extra_elements",
                "\n            let x: (Int, Bool) = (1, true, 1.2)\n            x\n            ",
                false,
                false,
            ),
            (
                "types::rejects_extra_explicit_function_type_args",
                "\n            func id<T>(x: T) -> T { x }\n            id<Int, Bool>(1)\n            ",
                false,
                false,
            ),
            (
                "types::rejects_extra_explicit_nominal_type_args",
                "\n            struct Box<T> { let value: T }\n            let x: Box<Int, Bool> = Box(value: 1)\n            x\n            ",
                false,
                false,
            ),
            (
                "types::substitutes_nested_generic_property_types",
                "\n            struct Box<T> { let xs: Array<T> }\n            let b = Box(xs: [1, 2])\n            b.xs\n            ",
                true,
                true,
            ),
            (
                "types::substitutes_nested_generic_variant_payload_types",
                "\n            enum E<T> { case arr(Array<T>) }\n            E.arr([1])\n            ",
                true,
                true,
            ),
            (
                "types::reports_unresolved_top_level_member_access",
                ".foo",
                false,
                false,
            ),
            (
                "effects::infers_func_with_indirect_effect",
                "\n          effect 'fizz() -> Int\n\n          func fizzes() {\n            'fizz()\n          }\n\n          func callsFizzes() {\n              fizzes()\n          }\n        ",
                true,
                false,
            ),
            (
                "effects::infers_func_with_effect",
                "\n          effect 'fizz() -> Int\n\n          func fizzes() {\n            'fizz()\n          }\n        ",
                true,
                false,
            ),
            (
                "effects::checks_pure_func_has_no_effects",
                "\n          effect 'fizz() -> Int\n\n          func fizzes() '[] {\n            'fizz()\n          }\n        ",
                false,
                false,
            ),
            (
                "effects::checks_pure_func_has_no_indirect_effects",
                "\n          effect 'fizz() -> Int\n\n          func callsFizzes() {\n              'fizz()\n          }\n\n          func fizzes() '[] {\n              callsFizzes()\n          }\n        ",
                false,
                false,
            ),
            (
                "effects::types_handlers",
                "\n            effect 'fizz(x: Int, y: Bool) -> Int\n\n            @handle 'fizz { a, b in\n                continue 0\n            }\n            ",
                true,
                false,
            ),
            (
                "effects::checks_handler_args",
                "\n            effect 'fizz(x: Int, y: Bool) -> Bool\n\n            @handle 'fizz { a in\n                true\n            }\n            ",
                false,
                false,
            ),
            (
                "effects::continue_in_handler_uses_effect_return_type",
                "\n            effect 'fizz() -> Int\n\n            @handle 'fizz {\n                continue 123\n            }\n            ",
                true,
                false,
            ),
            (
                "effects::continue_in_handler_checks_return_type",
                "\n            effect 'fizz() -> Int\n\n            @handle 'fizz {\n                continue true\n            }\n            ",
                false,
                false,
            ),
            (
                "effects::continue_with_value_outside_handler_errors",
                "continue 1",
                false,
                false,
            ),
            (
                "effects::dupe_handlers_warn",
                "\n                effect 'fizz() -> Int\n\n                @handle 'fizz { continue 0 }\n                @handle 'fizz { continue 1 }\n\n                'fizz()\n                ",
                false,
                false,
            ),
            (
                "effects::handler_removes_effect_from_enclosing_func",
                "\n          effect 'fizz() -> Int\n\n          func fizzes() '[] {\n            @handle 'fizz { continue 123 }\n\n            'fizz()\n          }\n        ",
                true,
                false,
            ),
            (
                "effects::generic_effect_declaration",
                "effect 'state<T>(value: T) -> T",
                true,
                false,
            ),
            (
                "effects::generic_effect_call_with_type_arg",
                "\n            effect 'state<T>(value: T) -> T\n            @handle 'state { v in continue v }\n            'state<Int>(42)\n        ",
                true,
                false,
            ),
            (
                "effects::generic_effect_call_inferred",
                "\n            effect 'state<T>(value: T) -> T\n            @handle 'state { v in continue v }\n            'state(42)\n        ",
                true,
                false,
            ),
            (
                "effects::generic_effect_type_mismatch",
                "\n            effect 'state<T>(value: T) -> T\n            @handle 'state { v in continue v }\n            'state<Int>(true)\n        ",
                false,
                false,
            ),
            (
                "effects::generic_effect_multiple_params",
                "\n            effect 'pair<A, B>(first: A, second: B) -> (A, B)\n            @handle 'pair { a, b in continue (a, b) }\n            'pair<Int, Bool>(42, true)\n        ",
                true,
                false,
            ),
            (
                "effects::call_under_handler_discharges_callee_row",
                "\n            effect 'e() -> Never\n\n            func f() {\n                'e()\n            }\n\n            func g() '[] {\n                @handle 'e { () }\n                f()\n            }\n        ",
                true,
                false,
            ),
            (
                "effects::perform_before_handler_escapes",
                "\n            effect 'e() -> Never\n\n            func g() '[] {\n                'e()\n                @handle 'e { () }\n            }\n        ",
                false,
                false,
            ),
            (
                "effects::unhandled_user_effect_at_top_level_errors",
                "\n            effect 'e() -> Never\n            'e()\n        ",
                false,
                false,
            ),
            (
                "effects::unhandled_effect_through_call_errors",
                "\n            effect 'e() -> Never\n\n            func f() {\n                'e()\n            }\n\n            f()\n        ",
                false,
                false,
            ),
            (
                "effects::top_level_call_before_handler_errors",
                "\n            effect 'e() -> Never\n\n            func f() {\n                'e()\n            }\n\n            f()\n            @handle 'e { () }\n        ",
                false,
                false,
            ),
            (
                "effects::top_level_let_before_handler_errors",
                "\n            effect 'e() -> Int\n\n            func f() -> Int {\n                'e()\n            }\n\n            let x = f()\n            @handle 'e { continue 1 }\n            x\n        ",
                false,
                false,
            ),
            (
                "effects::one_handler_covers_two_instantiations",
                "\n            effect 'state<T>(value: T) -> T\n\n            func g() '[] {\n                @handle 'state { v in continue v }\n                'state(1)\n                'state(true)\n                ()\n            }\n        ",
                true,
                false,
            ),
            (
                "effects::inner_handler_absorbs_all_occurrences",
                "\n            effect 'e() -> Never\n\n            func leaf() {\n                'e()\n            }\n\n            func mid() '[] {\n                @handle 'e { () }\n                leaf()\n            }\n\n            func top() '[] {\n                @handle 'e { () }\n                mid()\n            }\n        ",
                true,
                false,
            ),
            (
                "effects::top_level_let_after_handler_is_clean",
                "\n            effect 'e() -> Int\n\n            func f() -> Int {\n                'e()\n            }\n\n            @handle 'e { continue 1 }\n            let x = f()\n            x\n        ",
                true,
                false,
            ),
        ];
        let mut failures = String::new();
        for (name, source, expect_clean, with_core) in cases {
            let source = if *with_core {
                source.to_string()
            } else {
                format!("// no-core\n{source}")
            };
            let driver = if *with_core {
                Driver::new(
                    vec![Source::from(source.as_str())],
                    DriverConfig::new("PreviousSuite"),
                )
            } else {
                Driver::new_bare(
                    vec![Source::from(source.as_str())],
                    DriverConfig::new("PreviousSuite"),
                )
            };
            let typed = driver
                .parse()
                .expect("parse")
                .resolve_names()
                .expect("resolve")
                .type_check();
            let errors: Vec<String> = typed.diagnostics().iter().map(|d| d.to_string()).collect();
            if errors.is_empty() != *expect_clean {
                let detail = errors
                    .first()
                    .cloned()
                    .unwrap_or_else(|| "expected an error, got none".into());
                failures.push_str(&format!("{name}: {detail}\n"));
            }
        }
        assert!(failures.is_empty(), "behaviors diverged:\n{failures}");
    }

    #[test]
    fn type_aliases_are_transparent_in_type_positions() {
        let t = check("// no-core\ntypealias Inty = Int\nlet a: Inty = 123");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "a"), "Int");
    }

    #[test]
    fn type_aliases_can_name_generic_applications() {
        let t = check(
            "// no-core\nstruct Box<T> { let value: T }\ntypealias IntBox = Box<Int>\nlet b: IntBox = Box(value: 1)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "b"), "Box<Int>");
    }

    #[test]
    fn type_aliases_capture_nominal_generics() {
        let t = check(
            "// no-core\nstruct Box<T> {\n  typealias Item = T\n  let value: Item\n}\nfunc get(box: Box<Int>) -> Box<Int>.Item { box.value }",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "get"), "(Box<Int>) -> Int");
    }

    #[test]
    fn type_aliases_can_apply_captured_generics() {
        let t = check(
            "// no-core\nstruct T<U> { let value: U }\nstruct Box<U> {\n  typealias F = T<U>\n  let value: F\n}\nfunc get(box: Box<Int>) -> T<Int> { box.value }",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "get"), "(Box<Int>) -> T<Int>");
    }

    #[test]
    fn local_type_aliases_work_in_block_scopes() {
        let t = check("// no-core\nfunc f() -> Int {\n  typealias I = Int\n  let x: I = 1\n  x\n}");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "f"), "() -> Int");
    }

    #[test]
    fn extend_type_aliases_bind_associated_types() {
        let t = check(
            "// no-core\nprotocol HasItem {\n  associated Item\n  func getItem() -> Item\n}\nstruct Box {}\nextend Box: HasItem {\n  typealias Item = Bool\n  func getItem() -> Int { 1 }\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("expected Bool, found Int")),
            "expected associated type alias to constrain the witness, got {errors:?}"
        );
    }

    #[test]
    fn any_protocol_type_is_first_class_in_annotations() {
        let t = check(
            "// no-core\nprotocol Showable {\n  func show() -> Int\n}\ntypealias AnyShowable = any Showable\nfunc idAny(x: AnyShowable) -> AnyShowable { x }",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "idAny"), "(any Showable) -> any Showable");
    }

    #[test]
    fn expected_any_protocol_implicitly_packs_conforming_values() {
        let t = check(
            "// no-core\nprotocol Showable {\n  consuming func show() -> Int\n}\nextend Int: Showable {\n  consuming func show() -> Int { self }\n}\nlet value: any Showable = 1",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "value"), "any Showable");
        assert_eq!(t.phase.types.existential_packs.len(), 1);
    }

    #[test]
    fn any_protocol_members_use_erased_requirement_signatures() {
        let t = check(
            "// no-core\nprotocol Showable {\n  func show() -> Int\n}\nfunc render(value: any Showable) -> Int { value.show() }",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "render"), "(any Showable) -> Int");
    }

    #[test]
    fn any_protocol_with_associated_binding_substitutes_members() {
        let t = check(
            "// no-core\nprotocol Iterator {\n  associated Element\n  func next() -> Element\n}\nfunc nextInt(it: any Iterator<Element = Int>) -> Int { it.next() }",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "nextInt"), "(any Iterator<Element = Int>) -> Int");
    }

    #[test]
    fn object_safe_any_protocol_satisfies_generic_protocol_bounds() {
        let t = check(
            "// no-core\nprotocol Showable {\n  consuming func show() -> Int\n}\nextend Int: Showable {\n  consuming func show() -> Int { self }\n}\nfunc render<T: Showable>(value: T) -> Int { value.show() }\nlet value: any Showable = 1\nlet rendered = render(value)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "rendered"), "Int");
    }

    #[test]
    fn expected_any_protocol_rejects_existential_upcasts() {
        let t = check(
            "// no-core\nprotocol Readable {\n  func read() -> Int\n}\nprotocol ReadWrite: Readable {\n  func write(value: Int) -> ()\n}\nfunc upcast(value: any ReadWrite) -> any Readable { value }",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| {
                error.contains("Existential upcasting is not supported in v1")
                    && error.contains("any ReadWrite")
                    && error.contains("any Readable")
            }),
            "expected existential upcast error, got {errors:?}"
        );
    }

    #[test]
    fn existential_self_conformance_satisfies_superprotocol_bounds() {
        let t = check(
            "// no-core\nprotocol Readable {\n  consuming func read() -> Int\n}\nprotocol ReadWrite: Readable {\n  func write(value: Int) -> Int\n}\nextend Int: ReadWrite {\n  consuming func read() -> Int { self }\n  func write(value: Int) -> Int { value }\n}\nfunc readIt<T: Readable>(value: T) -> Int { value.read() }\nlet value: any ReadWrite = 1\nlet result = readIt(value)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "result"), "Int");
    }

    #[test]
    fn any_protocol_requires_all_associated_types() {
        let t = check(
            "// no-core\nprotocol Iterator {\n  associated Element\n  func next() -> Element\n}\nfunc use(it: any Iterator) { it }",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error
                    .contains("Missing associated type binding Element for any Iterator")),
            "expected missing associated binding error, got {errors:?}"
        );
    }

    #[test]
    fn any_protocol_accepts_named_associated_type_bindings() {
        let t = check(
            "// no-core\nprotocol Iterator {\n  associated Element\n  func next() -> Element\n}\nfunc use(it: any Iterator<Element = Int>) -> any Iterator<Element = Int> { it }",
        );
        assert_clean(&t);
        assert_eq!(
            ty_of(&t, "use"),
            "(any Iterator<Element = Int>) -> any Iterator<Element = Int>"
        );
    }

    #[test]
    fn any_protocol_rejects_unknown_associated_type_bindings() {
        let t = check(
            "// no-core\nprotocol Iterator {\n  associated Element\n  func next() -> Element\n}\nfunc use(it: any Iterator<Item = Int>) { it }",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(
                |error| error.contains("Unknown associated type binding Item for any Iterator")
            ),
            "expected unknown associated binding error, got {errors:?}"
        );
    }

    #[test]
    fn any_protocol_rejects_self_bearing_requirements() {
        let t = check(
            "// no-core\nprotocol Cloneable {\n  func clone() -> Self\n}\nfunc use(value: any Cloneable) { value }",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| {
                error.contains("Cannot form any Cloneable")
                    && error.contains("mentions Self outside the receiver")
            }),
            "expected non-object-safe existential error, got {errors:?}"
        );
    }

    #[test]
    fn any_protocol_rejects_duplicate_associated_type_bindings() {
        let t = check(
            "// no-core\nprotocol Iterator {\n  associated Element\n  func next() -> Element\n}\nfunc use(it: any Iterator<Element = Int, Element = Bool>) { it }",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Duplicate associated type binding Element")),
            "expected duplicate associated binding error, got {errors:?}"
        );
    }

    #[test]
    fn recursive_type_aliases_are_rejected() {
        let t = check("// no-core\ntypealias A = B\ntypealias B = A\nlet x: A = 1");
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("recursive type alias")),
            "expected a recursive type alias error, got {errors:?}"
        );
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
        let t = check(
            "// no-core\nfunc makeCounter() {\n\tlet i = 0\n\treturn func() { i }\n}\nlet counter = makeCounter()",
        );
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
        assert_eq!(ty_of(&t, "get"), "(&Counter) -> Int");
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
    fn member_on_unknown_generalizes_with_a_constraint() {
        // A field use on an unknown receiver no longer pins the receiver to
        // the one struct owning the label: the constraint rides the scheme
        // (qualified types — Jones 1994) and the call discharges it, so a
        // record argument with the same field would also work.
        let t = check(
            "// no-core\nstruct Box {\n\tlet val: Int\n}\nfunc get(b) { b.val }\nlet r = get(Box(val: 3))",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "get"), "<T0, T1>(T0) -> T1 where T0.val: T1");
        assert_eq!(ty_of(&t, "r"), "Int");
    }

    #[test]
    fn member_owned_by_two_protocols_rides_the_scheme() {
        // Two protocols own `m`: the use cannot pick an owner, so the
        // constraint stays on the scheme and each call site discharges it
        // against its concrete receiver's conformance.
        let t = check(
            "// no-core\nprotocol A {\n\tfunc m() -> Int\n}\nprotocol B {\n\tfunc m() -> Int\n}\nfunc f(x) { x.m() }\nextend Int: A {\n\tfunc m() -> Int { 1 }\n}\nlet r = f(2)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "f"), "<T0, T1>(T0) -> T1 where T0.m: () -> T1");
        assert_eq!(ty_of(&t, "r"), "Int");
    }

    #[test]
    fn ambiguous_member_use_suggests_the_explicit_forms() {
        // Two conformed protocols both provide `m`: picking one silently
        // would make the program's meaning depend on conformance-table
        // order (the overlapping-instances coherence problem — Jones,
        // *Qualified Types*, 1994, §2.4). Error, and name the
        // protocol-static forms that disambiguate.
        let t = check(
            "// no-core\nprotocol Aa {\n\tfunc m() -> Int\n}\nprotocol Bb {\n\tfunc m() -> Int\n}\nextend Int: Aa {\n\tfunc m() -> Int { 1 }\n}\nextend Int: Bb {\n\tfunc m() -> Int { 2 }\n}\nlet n = 5\nlet x = n.m()",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("Aa.m") && errors[0].contains("Bb.m"),
            "the error should suggest both explicit forms: {errors:?}"
        );
    }

    #[test]
    fn ambiguous_member_via_scheme_constraint_errors_at_the_call() {
        // The same ambiguity reached through a scheme-carried constraint:
        // the discharge site (the call) gets the error.
        let t = check(
            "// no-core\nprotocol Aa {\n\tfunc m() -> Int\n}\nprotocol Bb {\n\tfunc m() -> Int\n}\nextend Int: Aa {\n\tfunc m() -> Int { 1 }\n}\nextend Int: Bb {\n\tfunc m() -> Int { 2 }\n}\nfunc f(x) { x.m() }\nlet r = f(2)",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("Aa.m") && errors[0].contains("Bb.m"),
            "the error should suggest both explicit forms: {errors:?}"
        );
    }

    #[test]
    fn protocol_static_call_steers_an_ambiguous_member() {
        // A receiver conforming to two protocols that both provide `m`
        // resolves `x.m()` by conformance-table order; the protocol-static
        // form `P.m(x)` names the owner explicitly (the same shape Rust's
        // fully qualified `<T as Trait>::m(x)` takes). The two requirements
        // return different types, so each binding proves which one won.
        let t = check(
            "// no-core\nprotocol A {\n\tfunc m() -> Int\n}\nprotocol B {\n\tfunc m() -> Bool\n}\nextend Int: A {\n\tfunc m() -> Int { 1 }\n}\nextend Int: B {\n\tfunc m() -> Bool { true }\n}\nlet a = A.m(2)\nlet b = B.m(2)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "a"), "Int");
        assert_eq!(ty_of(&t, "b"), "Bool");
    }

    #[test]
    fn zero_annotation_fib_with_operators() {
        // The milestone-3 capstone: operators desugar to protocol-static
        // calls (Add.add(lhs, rhs)); HasMember/Conforms predicates collect on
        // n, improvement and generalization produce a qualified scheme, and
        // the call site discharges associated-type projection equalities
        // against Int's conformances (Chakravarty/Keller/Peyton Jones,
        // Associated Type Synonyms).
        let t = check(
            "// no-core\nprotocol Add {\n\tassociated RHS\n\tassociated Ret\n\tfunc add(rhs: RHS) -> Ret\n}\nprotocol Subtract {\n\tassociated RHS\n\tassociated Ret\n\tfunc minus(rhs: RHS) -> Ret\n}\nprotocol Comparable {\n\tassociated RHS\n\tfunc lte(rhs: RHS) -> Bool\n}\nextend Int: Add {\n\tfunc add(rhs: Int) -> Int { 0 }\n}\nextend Int: Subtract {\n\tfunc minus(rhs: Int) -> Int { 0 }\n}\nextend Int: Comparable {\n\tfunc lte(rhs: Int) -> Bool { true }\n}\nfunc fib(n) {\n\tif n <= 1 { return n }\n\treturn fib(n - 2) + fib(n - 1)\n}\nlet x = fib(24)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Int");
        assert_eq!(
            ty_of(&t, "fib"),
            "<T0: Add & Comparable & Subtract>(T0) -> T0 where Int == T0.RHS && T0 == T0.RHS && T0 == T0.Ret"
        );
    }

    #[test]
    fn generic_bound_call_at_two_types() {
        // Show.tlk shape (two conforming types through one bounded generic).
        let t = check(
            "// no-core\nprotocol Showy {\n\tfunc show() -> Int\n}\nstruct Fizz {\n\tlet a: Int\n}\nextend Fizz: Showy {\n\tfunc show() { self.a }\n}\nextend Int: Showy {\n\tfunc show() { 0 }\n}\nfunc printy<T: Showy>(s: T) { s.show() }\nprinty(123)\nprinty(Fizz(a: 1))",
        );
        assert_clean(&t);
    }

    #[test]
    fn effect_where_clause_constrains_perform_type_arguments() {
        let t = check(
            "// no-core\nprotocol P {}\nextend Int: P {}\neffect 'choose<T>(value: T) -> T where T: P\n@handle 'choose { v in continue v }\n'choose(true)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("does not conform")),
            "expected effect where predicate error, got {errors:?}"
        );
    }

    #[test]
    fn associated_where_clause_bounds_associated_type() {
        let t = check(
            "// no-core\nprotocol Showy {\n\tfunc show() -> Int\n}\nprotocol Container {\n\tassociated Item where Item: Showy\n\tfunc feed(item: Item) -> Int {\n\t\titem.show()\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn nominal_where_clause_is_well_formedness_context() {
        let t = check(
            "// no-core\nprotocol Showy {\n\tfunc show() -> Int\n}\nextend Int: Showy {\n\tfunc show() -> Int { 1 }\n}\nstruct Box<T> where T: Showy {\n\tlet item: T\n\tfunc itemShow() -> Int {\n\t\tself.item.show()\n\t}\n}\nlet good = Box(item: 1).itemShow()\nlet bad = Box(item: true)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("does not conform")),
            "expected nominal well-formedness error, got {errors:?}"
        );
        assert_eq!(ty_of(&t, "good"), "Int");
    }

    #[test]
    fn associated_where_same_type_is_protocol_refinement() {
        let t = check(
            "// no-core\nprotocol P {\n\tassociated Item where Item == Int\n\tfunc item() -> Item\n}\nfunc f<T: P>(x: T) -> Int {\n\tx.item()\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_requirement_where_is_used_at_dispatch() {
        let t = check(
            "// no-core\nprotocol P {\n\tassociated Item\n\tfunc item() -> Item where Item == Int\n}\nstruct S {}\nextend S: P {\n\tfunc item() -> Int { 1 }\n}\nfunc f<T: P>(x: T) -> Int {\n\tx.item()\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_where_refinement_is_inherited_by_bounds() {
        let t = check(
            "// no-core\nprotocol Iterable {\n\tassociated Element\n\tfunc next() -> Element\n}\nprotocol IntIterable: Iterable where Self.Element == Int {}\nfunc first<T: IntIterable>(x: T) -> Int {\n\tx.next()\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn rejects_global_where_predicates() {
        let t = check(
            "// no-core\nprotocol P {}\nextend Int: P {}\nfunc f() -> Int where Int: P { 1 }",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("must mention")),
            "expected invalid where predicate error, got {errors:?}"
        );
    }

    #[test]
    fn duplicate_where_predicates_warn() {
        let t = check("// no-core\nprotocol P {}\nfunc f<T>(x: T) where T: P && T: P { x }");
        let warnings = type_warnings(&t);
        assert!(
            warnings
                .iter()
                .any(|warning| warning.contains("Duplicate where predicate")),
            "expected duplicate predicate warning, got {warnings:?}"
        );
    }

    #[test]
    fn extend_where_clause_is_conditional_conformance_context() {
        let t = check(
            "// no-core\nprotocol Showy {\n\tfunc show() -> Int\n}\nprotocol BoxShow {\n\tfunc boxShow() -> Int\n}\nextend Int: Showy {\n\tfunc show() -> Int { 1 }\n}\nstruct Box<T> {\n\tlet item: T\n}\nextend Box<T>: BoxShow where T: Showy {\n\tfunc boxShow() -> Int {\n\t\tself.item.show()\n\t}\n}\nlet good = Box(item: 1).boxShow()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "good"), "Int");
    }

    #[test]
    fn extend_where_same_type_is_available_in_witness_body() {
        let t = check(
            "// no-core\nprotocol IntBox {\n\tfunc intItem() -> Int\n}\nstruct Box<T> {\n\tlet item: T\n}\nextend Box<T>: IntBox where T == Int {\n\tfunc intItem() -> Int {\n\t\tself.item\n\t}\n}\nlet good = Box(item: 1).intItem()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "good"), "Int");
    }

    #[test]
    fn declaration_where_conformance_and_same_type_are_scheme_predicates() {
        let t = check(
            "// no-core\nprotocol Boxy {\n\tassociated Item\n\tfunc item() -> Item\n}\nstruct S {}\nextend S: Boxy {\n\tfunc item() -> Int { 1 }\n}\nfunc intItem<T>(x: T) -> Int where T: Boxy && T.Item == Int {\n\tx.item()\n}\nlet y = intItem(S())",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "y"), "Int");
        let scheme = ty_of(&t, "intItem");
        assert!(scheme.contains("where"), "expected predicates in {scheme}");
        assert!(scheme.contains("Boxy"), "expected conformance in {scheme}");
        assert!(
            scheme.contains("Int"),
            "expected same-type predicate in {scheme}"
        );
    }

    #[test]
    fn rejects_ambiguous_predicate_constrained_generic() {
        let t = check("// no-core\nprotocol P {}\nfunc make<T>() -> Int where T: P {\n\t1\n}");
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("not determined")),
            "expected ambiguous type parameter error, got {errors:?}"
        );
    }

    #[test]
    fn borrow_parameters_auto_borrow_owned_arguments() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc len(s: &String) -> Int {\n\ts.length\n}\nlet s = String(length: 4)\nlet y = len(s)\nlet z = s.length",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "len"), "(&String) -> Int");
        assert_eq!(ty_of(&t, "y"), "Int");
        assert_eq!(ty_of(&t, "z"), "Int");
    }

    #[test]
    fn auto_borrow_does_not_overwrite_argument_node_type() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc len(s: &String) -> Int {\n\t0\n}\nlet s = String(length: 4)\nlet y = len(s)",
        );
        assert_clean(&t);
        let borrowed_exprs: Vec<_> = t
            .phase
            .types
            .node_types
            .values()
            .filter(|ty| ty.render_mono() == "&String")
            .collect();
        assert!(
            borrowed_exprs.is_empty(),
            "auto-borrow should not stamp an owned argument expression as &String: {borrowed_exprs:?}"
        );
    }

    #[test]
    fn for_loop_element_can_satisfy_borrow_callback() {
        let t = Driver::new(
            vec![Source::from(
                "enum Entry {\n\tcase doc(String)\n}\nfunc each(entries: Array<Entry>, fn: (&Entry) -> ()) {\n\tfor entry in entries {\n\t\tfn(entry)\n\t}\n}",
            )],
            DriverConfig::new("TypesTest"),
        )
        .parse()
        .expect("parse failed")
        .resolve_names()
        .expect("name resolution failed")
        .type_check();
        assert_clean(&t);
    }

    #[test]
    fn delayed_auto_borrow_defaults_unresolved_argument_to_owned() {
        let t = check(
            "// no-core\nstruct S {}\nfunc take(s: &S) {}\nfunc f(x) -> S {\n\ttake(x)\n\tx\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "f"), "(S) -> S");
    }

    #[test]
    fn borrowed_return_does_not_satisfy_owned_argument() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc id(s: &String) -> &String {\n\ts\n}\nfunc take(s: String) -> Int {\n\ts.length\n}\nlet s = String(length: 4)\nlet y = take(id(s))",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("String") && error.contains("&String")),
            "expected owned/borrowed mismatch, got {errors:?}"
        );
    }

    #[test]
    fn nested_borrow_does_not_satisfy_owned_argument() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nstruct Box<T> {\n\tlet value: T\n}\nfunc id(s: &String) -> &String {\n\ts\n}\nfunc take(b: Box<String>) -> Int {\n\tb.value.length\n}\nlet s = String(length: 4)\nlet b = Box(value: id(s))\nlet y = take(b)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("String") && error.contains("&String")),
            "expected nested owned/borrowed mismatch, got {errors:?}"
        );
    }

    #[test]
    fn function_return_borrow_does_not_satisfy_owned_function_argument() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nlet s = String(length: 4)\nlet f: () -> &String = func() { s }\nfunc take(f: () -> String) -> String {\n\tf()\n}\nlet y = take(f)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("String") && error.contains("&String")),
            "expected function return owned/borrowed mismatch, got {errors:?}"
        );
    }

    #[test]
    fn function_with_mutable_param_does_not_satisfy_shared_param_argument() {
        // `take` will invoke f with only a shared borrow, but `needs_mut` requires &mut.
        // Function parameters are contravariant, so this substitution is unsound.
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc needs_mut(s: &mut String) -> Int {\n\ts.length\n}\nfunc take(f: (&String) -> Int) -> Int {\n\t0\n}\nlet y = take(needs_mut)",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("&String")),
            "expected contravariant param mismatch (&mut required, & supplied), got {errors:?}"
        );
    }

    #[test]
    fn function_with_owned_param_does_not_satisfy_shared_param_argument() {
        // `take` passes a borrow, but `needs_owned` consumes an owned value.
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc needs_owned(s: String) -> Int {\n\ts.length\n}\nfunc take(f: (&String) -> Int) -> Int {\n\t0\n}\nlet y = take(needs_owned)",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("&String")),
            "expected contravariant param mismatch (owned required, & supplied), got {errors:?}"
        );
    }

    #[test]
    fn mutable_borrow_parameters_support_member_access() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc len(s: &mut String) -> Int {\n\ts.length\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "len"), "(&mut String) -> Int");
    }

    #[test]
    fn unknown_member_on_nested_borrow_reports_original_receiver() {
        let t = check(
            "// no-core\nstruct DirectoryEntry {}\nfunc f(entry: & &DirectoryEntry) {\n\tentry.show()\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Unknown member 'show' on &&DirectoryEntry")),
            "expected original nested-borrow receiver in diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn mutable_borrow_return_downgrades_to_shared_return() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc as_shared(s: &mut String) -> &String {\n\ts\n}\nlet f: (&mut String) -> &String = func(s: &mut String) -> &mut String {\n\ts\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "as_shared"), "(&mut String) -> &String");
        assert_eq!(ty_of(&t, "f"), "(&mut String) -> &String");
    }

    #[test]
    fn mutable_borrow_parameter_does_not_satisfy_shared_function_parameter() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nlet f: (&String) -> Int = func(s: &mut String) -> Int {\n\ts.length\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("&String") && error.contains("&mut String")),
            "expected shared/mutable function parameter mismatch, got {errors:?}"
        );
    }

    #[test]
    fn borrowed_enum_expectation_preserves_leading_dot_inference() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nlet x: &Opt<Int> = .some(1)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "&Opt<Int>");
    }

    #[test]
    fn inferred_match_result_is_concrete_within_its_binding_group() {
        // An inferred match joins its non-refining arms eagerly (like `if`),
        // so a later unannotated variant match in the same binding group
        // already knows the enum. With a deferred fresh-var result, `x`
        // stays unresolved and `.red` has no enum to resolve against.
        let t = check(
            "// no-core\nenum Color {\n\tcase red\n\tcase green\n}\nlet x = match 1 {\n\t1 -> Color.red,\n\t_ -> Color.green\n}\nmatch x {\n\t.red -> 1,\n\t.green -> 2\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn mutable_self_can_call_shared_self_method() {
        let t = check(
            "// no-core\nstruct Counter {\n\tlet n: Int\n\tfunc peek() -> Int { self.n }\n\tmut func bump() -> Int { self.peek() }\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "bump"), "(&mut Counter) -> Int");
    }

    #[test]
    fn shared_borrows_do_not_satisfy_mutable_borrow_parameters() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc takes_mut(s: &mut String) -> Int {\n\ts.length\n}\nfunc bad(s: &String) -> Int {\n\ttakes_mut(s)\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("&mut String") && error.contains("&String")),
            "expected shared/mutable borrow mismatch, got {errors:?}"
        );
    }

    #[test]
    fn shared_method_receiver_cannot_assign_self_field() {
        let t = check(
            "// no-core\nstruct Counter {\n\tlet n: Int\n\n\tfunc bump() -> () {\n\t\tself.n = 2\n\t\t()\n\t}\n}",
        );
        let errors: Vec<String> = t.diagnostics().iter().map(|d| d.to_string()).collect();
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot assign through shared borrow 'self'")),
            "expected shared receiver assignment error, got {errors:?}"
        );
    }

    #[test]
    fn mut_method_receiver_can_assign_self_field() {
        let t = check(
            "// no-core\nstruct Counter {\n\tlet n: Int\n\n\tmut func bump() -> () {\n\t\tself.n = 2\n\t\t()\n\t}\n}",
        );
        assert!(t.diagnostics().is_empty(), "{:?}", t.diagnostics());
    }

    // ----- Milestone 5: effects -----------------------------------------

    #[test]
    fn performed_effects_stay_in_the_row_until_a_handler_extent() {
        // Dynamic-extent semantics: a perform always joins the function's
        // latent row; discharge happens where a call meets a handler's
        // extent (here, the prescanned top-level `@handle`), not at the
        // perform site.
        let t = check(
            "// no-core\neffect 'oops(e) -> Never\n@handle 'oops { e in 0 }\nfunc safe() {\n\t'oops(1)\n\t2\n}\nsafe()",
        );
        assert_clean(&t);
        let safe = ty_of(&t, "safe");
        assert!(
            safe.contains("'oops"),
            "safe's row carries the effect it performs: {safe}"
        );
    }

    #[test]
    fn effect_rows_propagate_through_callers_and_payloads_zonk() {
        // The effect propagates through `outer`'s row (it calls `safe`
        // with no handler of its own), and the perform site teaches the
        // unannotated effect parameter its type — read from the finalized
        // catalog signature, which the lowerer builds capability types
        // from.
        let t = check(
            "// no-core\neffect 'oops(e) -> Never\n@handle 'oops { e in 0 }\nfunc safe() {\n\t'oops(1)\n\t2\n}\nfunc outer() {\n\tsafe()\n}\nouter()",
        );
        assert_clean(&t);
        let safe = ty_of(&t, "safe");
        assert!(safe.contains("'oops"), "safe performs 'oops: {safe}");
        let outer = ty_of(&t, "outer");
        assert!(
            outer.contains("'oops"),
            "outer's row inherits the callee's unhandled effect: {outer}"
        );
        let types = &t.phase.types;
        let (_, sig) = types
            .catalog
            .effects
            .iter()
            .next()
            .expect("the declared effect");
        assert!(
            matches!(
                &sig.params[0],
                crate::types::ty::Ty::Nominal(sym, _)
                    if *sym == crate::name_resolution::symbol::Symbol::Int
            ),
            "the perform site teaches the unannotated parameter Int: {:?}",
            sig.params
        );
    }

    #[test]
    fn generic_effect_row_carries_instantiation() {
        // Effect rows carry the instantiation, not just the label
        // (docs/generic-effects-plan.md): a perform of a generic effect
        // puts the concrete arguments in the row entry.
        let t =
            check("// no-core\neffect 'state<T>(value: T) -> T\nfunc f() {\n\t'state(42)\n\t()\n}");
        assert_clean(&t);
        let f = ty_of(&t, "f");
        assert!(
            f.contains("'state<Int>"),
            "the row entry carries the instantiation: {f}"
        );
    }

    #[test]
    fn two_instantiations_coexist_in_a_row() {
        // Duplicate labels at different instantiations coexist (scoped
        // labels): one function may perform 'state<Int> and
        // 'state<Bool> with no handler in scope.
        let t = check(
            "// no-core\neffect 'state<T>(value: T) -> T\nfunc f() {\n\t'state(42)\n\t'state(true)\n\t()\n}",
        );
        assert_clean(&t);
        let f = ty_of(&t, "f");
        assert!(
            f.contains("'state<Bool>") && f.contains("'state<Int>"),
            "both instantiations ride the row: {f}"
        );
    }

    #[test]
    fn dynamic_extent_handler_discharges_at_call_site() {
        // A handler installed in a caller covers a perform in an
        // unannotated callee: the effect stays in the callee's inferred
        // row and is discharged where the call meets the handler's
        // extent, never escaping the caller.
        let t = check(
            "// no-core\neffect 'throw(ret) -> ()\nfunc this_is_fine() {\n\t@handle 'throw { err in () }\n\tthis_is_not_fine()\n}\nfunc this_is_not_fine() {\n\t'throw(1)\n\t()\n}\nthis_is_fine()",
        );
        assert_clean(&t);
        let callee = ty_of(&t, "this_is_not_fine");
        assert!(
            callee.contains("'throw"),
            "the callee's inferred row carries the effect: {callee}"
        );
        let caller = ty_of(&t, "this_is_fine");
        assert!(
            !caller.contains("'throw"),
            "the caller discharges the effect at its handler: {caller}"
        );
    }

    #[test]
    fn let_else_binds_in_the_enclosing_scope() {
        // The pattern's binders are visible after the statement; the else
        // block must diverge (its value joins the match desugaring as
        // Never).
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc f(val: Opt<Int>) -> Int {\n\tlet .some(x) = val else { return 0 }\n\tx\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn let_else_body_is_typechecked() {
        // The else body's return must match the enclosing function.
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc f(val: Opt<Int>) -> Int {\n\tlet .some(x) = val else { return true }\n\tx\n}",
        );
        let errors = type_errors(&t);
        assert!(
            !errors.is_empty(),
            "expected an error for the Bool return in the else body"
        );
    }

    #[test]
    fn let_else_with_a_value_else_acts_as_a_default() {
        // The desugar is a match over [pattern, wildcard→else]: an else
        // that produces a binder-shaped value type-checks and supplies
        // the binding on the miss path (a non-diverging else whose value
        // does NOT match the binders is the type error the desugar
        // reports).
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc f(val: Opt<Int>) -> Int {\n\tlet .some(x) = val else { 0 }\n\tx\n}",
        );
        assert_clean(&t);

        let mismatched = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc f(val: Opt<Int>) -> Int {\n\tlet .some(x) = val else { true }\n\tx\n}",
        );
        assert!(!type_errors(&mismatched).is_empty());
    }

    #[test]
    fn if_let_checks_the_pattern_against_the_scrutinee() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc f(val: Opt<Int>) -> Int {\n\tif let .some(x) = val {\n\t\treturn x\n\t}\n\t0\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn or_patterns_check_in_match_arms() {
        let t = check(
            "// no-core\nenum E {\n\tcase a(Int)\n\tcase b(Int)\n\tcase c\n}\nfunc f(e: E) -> Int {\n\tmatch e {\n\t\t.a(v) | .b(v) -> v,\n\t\t.c -> 0\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn or_patterns_check_in_lets() {
        // Desugared to a single-arm match in the parser; binds in the
        // enclosing scope.
        let t = check(
            "// no-core\nenum E {\n\tcase a(Int)\n\tcase b(Int)\n}\nfunc f(e: E) -> Int {\n\tlet .a(v) | .b(v) = e\n\tv\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn or_pattern_arms_must_agree_on_payload_types() {
        let t = check(
            "// no-core\nenum E {\n\tcase a(Int)\n\tcase b(Bool)\n}\nfunc f(e: E) -> Int {\n\tmatch e {\n\t\t.a(v) | .b(v) -> 1\n\t}\n}",
        );
        assert!(
            !type_errors(&t).is_empty(),
            "Int and Bool binders should clash"
        );
    }

    #[test]
    fn member_constraints_generalize_into_schemes() {
        // The old types_struct_method_on_arg: a function constrained only
        // by a member use generalizes; the call discharges it.
        let t = check(
            "// no-core\nstruct Person {\n\tlet age: Int\n\n\tfunc getAge() {\n\t\tself.age\n\t}\n}\nlet person = Person(age: 123)\nlet r = getAgeOf(person)\nfunc getAgeOf(aged) {\n\taged.getAge()\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn member_constraints_dispatch_per_instantiation() {
        // Two structs own the same method name: the constraint rides the
        // scheme and each call site resolves its own witness.
        let t = check(
            "// no-core\nstruct A {\n\tfunc go() -> Int { 1 }\n}\nstruct B {\n\tfunc go() -> Int { 2 }\n}\nfunc call_go(x) {\n\tx.go()\n}\nlet a = call_go(A())\nlet b = call_go(B())",
        );
        assert_clean(&t);
    }

    #[test]
    fn member_constraints_reject_receivers_without_the_member() {
        let t = check(
            "// no-core\nstruct A {\n\tfunc go() -> Int { 1 }\n}\nstruct C {}\nfunc call_go(x) {\n\tx.go()\n}\ncall_go(C())",
        );
        assert!(
            !type_errors(&t).is_empty(),
            "C has no go(): the discharged constraint must error"
        );
    }

    #[test]
    fn generic_methods_instantiate_per_call() {
        let t = check(
            "// no-core\nstruct Person {\n\tfunc getAge<T>(t: T) -> T { t }\n}\nPerson().getAge(123)\nPerson().getAge(1.23)",
        );
        assert_clean(&t);
    }

    #[test]
    fn enum_methods_dispatch_on_self() {
        let t = check(
            "// no-core\nenum Fizz<T> {\n\tcase foo(T)\n\tcase bar(T)\n\n\tfunc unwrap() -> T {\n\t\tmatch self {\n\t\t\t.foo(t) -> t,\n\t\t\t.bar(t) -> t\n\t\t}\n\t}\n}\nFizz.foo(123).unwrap()",
        );
        assert_clean(&t);
    }

    #[test]
    fn record_projections_generalize_over_rows() {
        // func f(r) { r.a }: nothing pins r nominally, so the member
        // constraint defaults the receiver to an open record row at the
        // solver's fixpoint; the row tail generalizes (Gaster & Jones,
        // POPL 1996 / Leijen, Trends in FP 2005), and each call
        // instantiates it afresh.
        let t =
            check("// no-core\nfunc fstA(r) { r.a }\n(fstA({ a: 1 }), fstA({ a: 2, b: true }))");
        assert_clean(&t);

        let t = check(
            "// no-core\nfunc foo(x) {\n\t(x.y, x.z)\n}\nfoo({ y: 123, z: 1.23 })\nfoo({ y: 123, z: 123 })",
        );
        assert_clean(&t);
    }

    #[test]
    fn generic_effect_declaration() {
        let t = check("// no-core\neffect 'state<T>(value: T) -> T");
        assert_clean(&t);
    }

    #[test]
    fn generic_effect_call_with_type_arg() {
        let t = check(
            "// no-core\neffect 'state<T>(value: T) -> T\n@handle 'state { v in\n\tcontinue v\n}\n'state<Int>(42)",
        );
        assert_clean(&t);
    }

    #[test]
    fn generic_effect_call_inferred() {
        let t = check(
            "// no-core\neffect 'state<T>(value: T) -> T\n@handle 'state { v in\n\tcontinue v\n}\n'state(42)",
        );
        assert_clean(&t);
    }

    #[test]
    fn generic_effect_type_mismatch() {
        let t = check(
            "// no-core\neffect 'state<T>(value: T) -> T\n@handle 'state { v in\n\tcontinue v\n}\n'state<Int>(true)",
        );
        assert!(
            !type_errors(&t).is_empty(),
            "passing a Bool for an Int-instantiated effect must error"
        );
    }

    #[test]
    fn generic_effect_multiple_params() {
        let t = check(
            "// no-core\neffect 'pair<A, B>(first: A, second: B) -> (A, B)\n@handle 'pair { a, b in\n\tcontinue (a, b)\n}\n'pair<Int, Bool>(42, true)",
        );
        assert_clean(&t);
    }

    #[test]
    fn continue_payload_checks_against_the_effect_return() {
        // `continue v` resumes the perform: v must have the effect's
        // declared return type.
        let t = check(
            "// no-core\neffect 'ask(p: Int) -> Int\n@handle 'ask { p in\n\tcontinue true\n}\n'ask(1)",
        );
        let errors = type_errors(&t);
        assert!(
            !errors.is_empty(),
            "expected a type error for continue true"
        );
    }

    #[test]
    fn continue_payload_outside_a_handler_is_rejected() {
        let t = check("// no-core\nfunc f() -> Int {\n\tloop true {\n\t\tcontinue 5\n\t}\n\t0\n}");
        let errors = type_errors(&t);
        assert!(
            !errors.is_empty(),
            "expected an error for continue-with-value outside a handler"
        );
    }

    #[test]
    fn conditionless_loop_without_break_is_never() {
        let t = check("// no-core\nfunc nope() -> Never {\n\tloop {}\n}");
        assert_clean(&t);
    }

    #[test]
    fn conditionless_loop_with_break_completes_as_unit() {
        let t = check("// no-core\nfunc nope() -> Never {\n\tloop {\n\t\tbreak\n\t}\n}");
        let errors = type_errors(&t);
        assert!(
            !errors.is_empty(),
            "a loop with a break can complete normally, so it is not Never"
        );
    }

    #[test]
    fn nested_loop_break_does_not_exit_outer_loop() {
        let t = check(
            "// no-core\nfunc nope() -> Never {\n\tloop {\n\t\tloop {\n\t\t\tbreak\n\t\t}\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn code_after_divergent_loop_is_unreachable() {
        let t = check("// no-core\nfunc nope() -> Int {\n\tloop {}\n\t123\n}");
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("unreachable")),
            "expected an unreachable-code error, got {errors:?}"
        );
    }

    #[test]
    fn continue_payload_in_a_handler_checks_clean() {
        let t = check(
            "// no-core\neffect 'ask(p: Int) -> Int\n@handle 'ask { p in\n\tcontinue p\n}\n'ask(1)",
        );
        assert_clean(&t);
    }

    #[test]
    fn unhandled_effects_grow_the_latent_row() {
        let t = check("// no-core\neffect 'oops(e) -> Never\nfunc risky() {\n\t'oops(1)\n\t2\n}");
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
        let t = check("// no-core\neffect 'a() -> ()\nfunc f() 'a -> () {\n\t'a()\n}");
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

    #[test]
    fn super_protocol_requirements_are_required_by_subprotocol_conformance() {
        let t = check(
            "// no-core\nprotocol A {\n\tfunc a() -> Int\n}\nprotocol B: A {}\nstruct S {}\nextend S: B {}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Missing 'a' required by A")),
            "expected inherited requirement to be missing, got {errors:?}"
        );
    }

    #[test]
    fn subprotocol_conformance_satisfies_superprotocol_bounds() {
        let t = check(
            "// no-core\nprotocol A {\n\tfunc a() -> Int\n}\nprotocol B: A {}\nstruct S {}\nextend S: B {\n\tfunc a() -> Int { 1 }\n}\nfunc useA<T: A>(x: T) -> Int { x.a() }\nlet value = useA(S())",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "value"), "Int");
    }

    #[test]
    fn inherited_associated_types_reduce_through_subprotocol_conformance() {
        let t = check(
            "// no-core\nprotocol A {\n\tassociated Item\n\tfunc get() -> Item\n}\nprotocol B: A {}\nstruct S {}\nextend S: B {\n\tfunc get() -> Int { 1 }\n}\nfunc useA<T: A>(x: T) -> T.Item { x.get() }\nlet value = useA(S())",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "value"), "Int");
    }

    #[test]
    fn subprotocol_conformance_can_rely_on_later_superprotocol_conformance() {
        let t = check(
            "// no-core\nprotocol A {\n\tfunc a() -> Int\n}\nprotocol B: A {}\nstruct S {}\nextend S: B {}\nextend S: A {\n\tfunc a() -> Int { 1 }\n}\nfunc useA<T: A>(x: T) -> Int { x.a() }\nlet genericValue = useA(S())\nlet directValue = S().a()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "genericValue"), "Int");
        assert_eq!(ty_of(&t, "directValue"), "Int");
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
        let int_instantiation = instantiations
            .values()
            .any(|subst| subst.iter().any(|(_, ty)| ty.render_mono() == "Int"));
        assert!(
            int_instantiation,
            "expected an instantiation at Int, got: {instantiations:?}"
        );
    }
    // ----- Match exhaustiveness and reachable arms -----------------------
    // The usefulness analysis of Maranget, *Warnings for pattern matching*
    // (JFP 2007): a match must cover every value of the scrutinee's type
    // (error), and every arm must be reachable (warning).

    #[test]
    fn match_missing_an_enum_variant_errors_and_names_it() {
        let t = check(
            "// no-core\nenum Color {\n\tcase red, green, blue\n}\nlet c = Color.red\nmatch c {\n\tColor.red -> 1,\n\tColor.green -> 2\n}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains(".blue"),
            "the error should name the unhandled case: {errors:?}"
        );
    }

    #[test]
    fn match_covering_every_variant_is_clean() {
        let t = check(
            "// no-core\nenum Color {\n\tcase red, green, blue\n}\nlet c = Color.red\nmatch c {\n\tColor.red -> 1,\n\tColor.green -> 2,\n\tColor.blue -> 3\n}",
        );
        assert_clean(&t);
        assert_eq!(type_warnings(&t), Vec::<String>::new());
    }

    #[test]
    fn wildcard_arm_covers_the_remaining_variants() {
        let t = check(
            "// no-core\nenum Color {\n\tcase red, green, blue\n}\nlet c = Color.red\nmatch c {\n\tColor.red -> 1,\n\t_ -> 2\n}",
        );
        assert_clean(&t);
        assert_eq!(type_warnings(&t), Vec::<String>::new());
    }

    #[test]
    fn or_pattern_arms_count_toward_coverage() {
        let t = check(
            "// no-core\nenum Color {\n\tcase red, green, blue\n}\nlet c = Color.red\nmatch c {\n\tColor.red | Color.green -> 1,\n\tColor.blue -> 2\n}",
        );
        assert_clean(&t);
        assert_eq!(type_warnings(&t), Vec::<String>::new());
    }

    #[test]
    fn bool_match_missing_false_errors() {
        let t = check("// no-core\nmatch true {\n\ttrue -> 1\n}");
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("false"),
            "the error should name the unhandled case: {errors:?}"
        );
    }

    #[test]
    fn int_match_without_a_catch_all_errors() {
        let t = check("// no-core\nmatch 123 {\n\t1 -> 1,\n\t2 -> 2\n}");
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
    }

    #[test]
    fn missing_nested_payload_case_is_reported_with_its_shape() {
        let t = check(
            "// no-core\nenum Maybe<T> {\n\tcase some(T), none\n}\nlet m = Maybe.some(true)\nmatch m {\n\tMaybe.some(true) -> 1,\n\tMaybe.none -> 2\n}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains(".some(false)"),
            "the error should show the unhandled shape: {errors:?}"
        );
    }

    #[test]
    fn tuple_patterns_cover_componentwise() {
        let t = check("// no-core\nmatch (true, 1) {\n\t(true, _) -> 1,\n\t(false, _) -> 2\n}");
        assert_clean(&t);
        assert_eq!(type_warnings(&t), Vec::<String>::new());
    }

    #[test]
    fn arm_after_a_wildcard_warns_as_unreachable() {
        let t = check(
            "// no-core\nenum Color {\n\tcase red, green, blue\n}\nlet c = Color.red\nmatch c {\n\t_ -> 1,\n\tColor.red -> 2\n}",
        );
        assert_clean(&t);
        let warnings = type_warnings(&t);
        assert_eq!(warnings.len(), 1, "{warnings:?}");
        assert!(
            warnings[0].contains("never"),
            "the warning should say the arm never runs: {warnings:?}"
        );
    }

    #[test]
    fn duplicate_arm_warns_as_unreachable() {
        let t = check("// no-core\nmatch true {\n\ttrue -> 1,\n\tfalse -> 2,\n\ttrue -> 3\n}");
        assert_clean(&t);
        let warnings = type_warnings(&t);
        assert_eq!(warnings.len(), 1, "{warnings:?}");
    }

    #[test]
    fn binder_arm_is_exhaustive_and_later_arms_warn() {
        let t = check("// no-core\nmatch 123 {\n\ta -> a,\n\t1 -> 1\n}");
        assert_clean(&t);
        let warnings = type_warnings(&t);
        assert_eq!(warnings.len(), 1, "{warnings:?}");
    }

    #[test]
    fn record_patterns_cover_by_field() {
        let t = check(
            "// no-core\nlet r = { on: true }\nmatch r {\n\t{ on: true } -> 1,\n\t{ on: false } -> 2\n}",
        );
        assert_clean(&t);
        assert_eq!(type_warnings(&t), Vec::<String>::new());
    }

    #[test]
    fn record_match_missing_a_field_case_errors() {
        let t = check("// no-core\nlet r = { on: true }\nmatch r {\n\t{ on: true } -> 1\n}");
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("false"),
            "the error should show the unhandled shape: {errors:?}"
        );
    }

    #[test]
    fn generic_enum_method_match_on_self_is_checked() {
        // `match self` inside an enum method: the scrutinee is the enum
        // applied to its own parameters, so coverage still checks.
        let t = check(
            "// no-core\nenum Fizz<T> {\n\tcase foo(T), bar(T)\n\n\tfunc partial() {\n\t\tmatch self {\n\t\t\tFizz.foo(t) -> t\n\t\t}\n\t}\n}\nFizz.foo(123).partial()",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains(".bar"), "{errors:?}");
    }

    #[test]
    fn gadt_variant_constructor_schemes_are_lowered() {
        let typed = check(
            "
            protocol P {}
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case pair<A, B>(Expr<A>, Expr<B>) -> Expr<(A, B)>
                case boxed<A: P>(A) -> Expr<A>
            }
            ",
        );
        assert_clean(&typed);
        let resolved = &typed.phase.resolved_names;
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let expr = resolved
            .symbol_names
            .iter()
            .find(|(sym, name)| {
                name.as_str() == "Expr" && typed.phase.types.catalog.enums.contains_key(sym)
            })
            .map(|(sym, _)| *sym)
            .expect("Expr enum");
        let info = &typed.phase.types.catalog.enums[&expr];
        assert_eq!(
            info.variants["int"].constructor_scheme.render(),
            "(Int) -> Expr<Int>"
        );
        assert_eq!(
            info.variants["pair"].constructor_scheme.render(),
            "<T0, T1>(Expr<T0>, Expr<T1>) -> Expr<(T0, T1)>"
        );
        assert_eq!(
            info.variants["boxed"].constructor_scheme.render(),
            "<T0: P>(T0) -> Expr<T0>"
        );
    }

    #[test]
    fn gadt_variant_generic_shadowing_is_rejected() {
        let typed = check(
            "
            enum Expr<T> {
                case bad<T>(T) -> Expr<T>
            }
            ",
        );
        let errors = type_errors(&typed);
        assert!(
            errors.iter().any(|error| error.contains("shadows")),
            "{errors:?}"
        );
    }

    #[test]
    fn redundant_variant_result_warns() {
        let typed = check(
            "
            enum Color {
                case red -> Color
            }
            ",
        );
        let warnings = type_warnings(&typed);
        assert!(
            warnings.iter().any(|warning| warning.contains("redundant")),
            "{warnings:?}"
        );
    }

    #[test]
    fn invalid_variant_result_head_is_rejected() {
        let typed = check(
            "
            struct Other {}
            enum E {
                case bad -> Other
            }
            ",
        );
        let errors = type_errors(&typed);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("must be the enclosing enum")),
            "{errors:?}"
        );
    }

    #[test]
    fn gadt_match_refines_arm_result_types() {
        let typed = check(
            "// no-core
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case bool(Bool) -> Expr<Bool>
            }

            func eval<T>(expr: Expr<T>) -> T {
                match expr {
                    .int(n) -> n,
                    .bool(b) -> b
                }
            }

            let i: Int = eval(Expr.int(1))
            let b: Bool = eval(Expr.bool(true))
            ",
        );
        assert_clean(&typed);
    }

    #[test]
    fn gadt_match_rejects_escaping_existential_payloads() {
        let typed = check(
            "// no-core
            enum Hidden<T> {
                case hidden<A>(A) -> Hidden<T>
            }

            func leak<T>(value: Hidden<T>) -> T {
                match value {
                    .hidden(x) -> x
                }
            }
            ",
        );
        let errors = type_errors(&typed);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("escapes this pattern arm")),
            "{errors:?}"
        );
    }

    #[test]
    fn inferred_gadt_match_result_works_when_arms_agree() {
        let typed = check(
            "// no-core
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case bool(Bool) -> Expr<Bool>
            }

            func tag<T>(expr: Expr<T>) {
                match expr {
                    .int(_) -> 0,
                    .bool(_) -> 1
                }
            }

            let i: Int = tag(Expr.int(1))
            let j: Int = tag(Expr.bool(true))
            ",
        );
        assert_clean(&typed);
    }

    #[test]
    fn inferred_gadt_match_result_can_use_local_refinements() {
        let typed = check(
            "// no-core
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case bool(Bool) -> Expr<Bool>
            }

            func to_int<T>(expr: Expr<T>, value: T) {
                match expr {
                    .int(_) -> value,
                    .bool(_) -> if value { 1 } else { 0 }
                }
            }

            let i: Int = to_int(Expr.int(1), 41)
            let j: Int = to_int(Expr.bool(true), false)
            ",
        );
        assert_clean(&typed);
    }

    #[test]
    fn inferred_gadt_match_result_errors_when_arms_depend_on_different_refinements() {
        let typed = check(
            "// no-core
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case bool(Bool) -> Expr<Bool>
            }

            func eval<T>(expr: Expr<T>) {
                match expr {
                    .int(n) -> n,
                    .bool(b) -> b
                }
            }
            ",
        );
        let errors = type_errors(&typed);
        assert!(
            errors.iter().any(|error| error.contains("Type mismatch")),
            "{errors:?}"
        );
    }

    #[test]
    fn gadt_leading_dot_construction_checks_result_type() {
        let typed = check(
            "// no-core
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case bool(Bool) -> Expr<Bool>
            }

            let bad: Expr<Int> = .bool(true)
            ",
        );
        let errors = type_errors(&typed);
        assert!(
            errors.iter().any(|error| error.contains("Bool")),
            "{errors:?}"
        );
    }

    #[test]
    fn gadt_type_member_construction_checks_result_well_formedness() {
        let typed = check(
            "// no-core
            protocol P {}
            extend Int: P {}
            enum Box<T> where T: P {
                case int(Int) -> Box<Int>
            }

            Box.int(1)
            ",
        );
        assert_clean(&typed);
    }

    #[test]
    fn gadt_constructor_bounds_are_wanteds_at_construction() {
        let typed = check(
            "// no-core
            protocol P {}
            enum Box<T> {
                case boxed<A: P>(A) -> Box<A>
            }

            Box.boxed(1)
            ",
        );
        let errors = type_errors(&typed);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("does not conform to P")),
            "{errors:?}"
        );
    }

    #[test]
    fn gadt_constructor_bounds_are_givens_in_patterns() {
        let typed = check(
            "// no-core
            protocol P {
                func p() -> Int
            }
            struct S {}
            extend S: P {
                func p() -> Int { 1 }
            }
            enum Box<T> {
                case boxed<A: P>(A) -> Box<A>
            }

            func read<T>(box: Box<T>) -> Int {
                match box {
                    .boxed(x) -> x.p()
                }
            }

            read(Box.boxed(S()))
            ",
        );
        assert_clean(&typed);
    }

    #[test]
    fn gadt_exhaustiveness_ignores_impossible_variants() {
        let typed = check(
            "// no-core
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case bool(Bool) -> Expr<Bool>
            }

            func only_int(expr: Expr<Int>) -> Int {
                match expr {
                    .int(n) -> n
                }
            }
            ",
        );
        assert_clean(&typed);
    }

    #[test]
    fn gadt_exhaustiveness_uses_result_substitutions_for_payloads() {
        let typed = check(
            "// no-core
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case bool(Bool) -> Expr<Bool>
                case pair<A, B>(Expr<A>, Expr<B>) -> Expr<(A, B)>
            }

            func only_int_bool_pair(expr: Expr<(Int, Bool)>) -> Int {
                match expr {
                    .pair(.int(n), .bool(_)) -> n
                }
            }
            ",
        );
        assert_clean(&typed);
    }

    #[test]
    fn gadt_impossible_variant_arm_warns_unreachable() {
        let typed = check(
            "// no-core
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case bool(Bool) -> Expr<Bool>
            }

            func only_int(expr: Expr<Int>) -> Int {
                match expr {
                    .bool(b) -> 0,
                    .int(n) -> n
                }
            }
            ",
        );
        let warnings = type_warnings(&typed);
        assert!(
            warnings
                .iter()
                .any(|warning| warning.contains("never runs")),
            "{warnings:?}"
        );
    }

    #[test]
    fn gadt_hidden_payload_can_be_returned_as_existential() {
        let typed = check(
            "// no-core\nprotocol Showable {\n  consuming func show() -> Int\n}\nextend Int: Showable {\n  consuming func show() -> Int { self }\n}\nenum GBox<T> {\n  case hidden<A: Showable>(A) -> GBox<Bool>\n}\nfunc erase(box: GBox<Bool>) -> any Showable {\n  match box {\n    .hidden(value) -> value\n  }\n}",
        );
        assert_clean(&typed);
        assert_eq!(ty_of(&typed, "erase"), "(GBox<Bool>) -> any Showable");
    }

    #[test]
    fn gadt_derived_showable_ignores_impossible_payloads() {
        let typed = check(
            "// no-core
            protocol Showable {
                func show() -> Int
            }
            extend Int: Showable {
                func show() -> Int { 1 }
            }
            enum GBox<T> {
                case int(Int) -> GBox<Int>
                case hidden<A>(A) -> GBox<Bool>
            }

            func render<T: Showable>(value: T) -> Int {
                value.show()
            }

            render(GBox.int(1))
            ",
        );
        assert_clean(&typed);
    }

    #[test]
    fn gadt_or_pattern_accepts_alpha_equivalent_refinements() {
        let typed = check(
            "// no-core
            enum E<T> {
                case a<X>(X) -> E<X>
                case b<Y>(Y) -> E<Y>
            }

            func f<T>(e: E<T>) -> Int {
                match e {
                    .a(x) | .b(x) -> 0
                }
            }
            ",
        );
        assert_clean(&typed);
    }

    #[test]
    fn gadt_or_pattern_with_different_refinements_is_rejected() {
        let typed = check(
            "// no-core
            enum Expr<T> {
                case int(Int) -> Expr<Int>
                case bool(Bool) -> Expr<Bool>
            }

            func bad<T>(expr: Expr<T>) -> T {
                match expr {
                    .int(x) | .bool(x) -> x
                }
            }
            ",
        );
        let errors = type_errors(&typed);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Or-pattern alternatives")),
            "{errors:?}"
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
        let driver_b = Driver::new(
            vec![Source::from(
                "use { make } from A\nlet v = make(3).x\nlet bad: Int = make(3)",
            )],
            config,
        );
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
    fn public_type_aliases_cross_module_boundary() {
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let driver_a = Driver::new(
            vec![Source::from(
                "public typealias UserId = Int\npublic func make() -> UserId { 1 }",
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
        let driver_b = Driver::new(
            vec![Source::from(
                "use { UserId, make } from A\nlet id: UserId = make()",
            )],
            config,
        );
        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
        let resolved = &typed.phase.resolved_names;
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let symbol = resolved
            .symbol_names
            .iter()
            .find(|(sym, n)| n.as_str() == "id" && typed.phase.types.schemes.contains_key(sym))
            .map(|(sym, _)| *sym)
            .expect("id scheme");
        assert_eq!(typed.phase.types.schemes[&symbol].render(), "Int");
    }

    #[test]
    fn fib_against_core_is_int() {
        let typed = check_with_core(Source::from(
            "let x = fib(24)\nfunc fib(n) {\n\tif n <= 1 { return n }\n\treturn fib(n - 2) + fib(n - 1)\n}",
        ));
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

    // === Grades: Copy / Affine / Linear (substructural core) ===
    // These check against the real core prelude, where the Copy / CheapClone /
    // Deinit marker protocols live.

    fn assert_no_errors(driver: &Driver<Typed>) {
        let errors = type_errors(driver);
        assert!(errors.is_empty(), "expected no type errors: {errors:?}");
    }

    #[test]
    fn copy_conformance_requires_all_fields_copy() {
        let t = check_with_core(Source::from(
            "struct Point {\n\tlet x: Int\n\tlet y: Int\n}\nextend Point: Copy {}",
        ));
        assert_no_errors(&t);
    }

    #[test]
    fn copy_conformance_rejects_non_copy_field() {
        let t = check_with_core(Source::from(
            "struct Name {\n\tlet value: String\n}\nextend Name: Copy {}",
        ));
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("Copy")),
            "expected a non-Copy-field error, got {errors:?}"
        );
    }

    #[test]
    fn linear_struct_rejects_deinit_conformance() {
        // A linear value must be consumed explicitly; an automatic destructor
        // would defeat the point of declaring it linear.
        let t = check_with_core(Source::from(
            "struct FileHandle 'linear {\n\tlet fd: Int\n}\nextend FileHandle: Deinit {\n\tfunc deinit() {}\n}",
        ));
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("linear")),
            "expected a linear/Deinit conflict error, got {errors:?}"
        );
    }

    #[test]
    fn linear_struct_rejects_copy_conformance() {
        let t = check_with_core(Source::from(
            "struct Token 'linear {\n\tlet id: Int\n}\nextend Token: Copy {}",
        ));
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("linear")),
            "expected a linear/Copy conflict error, got {errors:?}"
        );
    }

    #[test]
    fn aborting_handler_body_must_match_the_scope_value_type() {
        // A handler that completes without `continue` aborts the handled
        // scope with its value: an Int-valued handler over a ()-valued
        // scope must be a type error, not a lowering panic.
        let t = check_with_core(Source::from(
            "effect 'oops(e) -> Never\n@handle 'oops { e in\n\t42\n}\nfunc boom() 'oops -> () {\n\t'oops(\"x\")\n}\nboom()",
        ));
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.to_lowercase().contains("mismatch")),
            "expected a handler/scope type mismatch, got {errors:?}"
        );
    }

    #[test]
    fn aborting_handler_body_must_match_the_function_return_type() {
        let t = check_with_core(Source::from(
            "effect 'oops(e) -> Never\nfunc f() -> Int {\n\t@handle 'oops { e in\n\t\t\"nope\"\n\t}\n\t'oops(\"x\")\n\t42\n}\nf()",
        ));
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.to_lowercase().contains("mismatch")),
            "expected a handler/return type mismatch, got {errors:?}"
        );
    }

    #[test]
    fn matching_and_resuming_handler_bodies_stay_clean() {
        // An aborting handler whose value matches the scope, and an
        // always-resuming handler (Never body), both check clean.
        let t = check_with_core(Source::from(
            "effect 'oops(e) -> Never\neffect 'ask(q) -> Int\n@handle 'oops { e in\n\t0\n}\n@handle 'ask { q in\n\tcontinue 1\n}\nfunc go() '[oops, ask] -> Int {\n\t'ask(\"?\")\n}\ngo()",
        ));
        assert_no_errors(&t);
    }

    #[test]
    fn unique_annotation_parses_and_renders() {
        let t = check_with_core(Source::from("func pass(x: *String) -> *String {\n\tx\n}"));
        assert_no_errors(&t);
        let resolved = &t.phase.resolved_names;
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let symbol = resolved
            .symbol_names
            .iter()
            .find(|(sym, n)| n.as_str() == "pass" && t.phase.types.schemes.contains_key(sym))
            .map(|(sym, _)| *sym)
            .expect("pass scheme");
        assert_eq!(
            t.phase.types.schemes[&symbol].render(),
            "(*String) -> *String"
        );
    }

    #[test]
    fn grades_derive_from_declarations() {
        use crate::name_resolution::symbol::Symbol;
        use crate::types::catalog::Grade;
        let t = check_with_core(Source::from(
            "struct FileHandle 'linear {\n\tlet fd: Int\n}\nstruct Plain {\n\tlet x: Int\n}\nextend Plain: Copy {}\nstruct Holder {\n\tlet name: String\n}",
        ));
        assert_no_errors(&t);
        let resolved = &t.phase.resolved_names;
        let symbol_named = |name: &str| -> Symbol {
            resolved
                .symbol_names
                .iter()
                .find(|(sym, n)| {
                    n.as_str() == name && matches!(sym, Symbol::Struct(_) | Symbol::Enum(_))
                })
                .map(|(sym, _)| *sym)
                .unwrap_or_else(|| panic!("no struct symbol named {name}"))
        };
        let catalog = &t.phase.types.catalog;
        assert_eq!(catalog.grade_of(symbol_named("FileHandle")), Grade::Linear);
        assert_eq!(catalog.grade_of(symbol_named("Plain")), Grade::Copy);
        assert_eq!(catalog.grade_of(symbol_named("Holder")), Grade::Affine);
        assert_eq!(catalog.grade_of(Symbol::Int), Grade::Copy);
        assert_eq!(catalog.grade_of(Symbol::String), Grade::Affine);
    }
}
