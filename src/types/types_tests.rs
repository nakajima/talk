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

    /// Compile a library module under an explicit module id (absolute
    /// identity, ADR 0038) against `deps`, returning its exported module.
    /// Register the result with `import_compiled(module, id)`.
    pub fn compile_library(
        name: &str,
        id: crate::compiling::module::ModuleId,
        source: &'static str,
        deps: crate::compiling::module::ModuleEnvironment,
    ) -> crate::compiling::module::Module {
        let mut config = DriverConfig::new(name);
        config.module_id = id;
        config.mode = crate::compiling::driver::CompilationMode::Library;
        config.modules = std::rc::Rc::new(deps);
        let typed = Driver::new(vec![Source::from(source)], config)
            .parse()
            .expect("parse failed")
            .resolve_names()
            .expect("name resolution failed")
            .type_check();
        assert_eq!(type_errors(&typed), Vec::<String>::new());
        typed.module(name)
    }

    /// Render the scheme of a named top-level binding. Nominal heads display
    /// with their source names via the symbol-name context.
    pub fn ty_of(driver: &Driver<Typed>, name: &str) -> String {
        let resolved = &driver.phase.program.resolved_names();
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let mut candidates: Vec<_> = resolved
            .symbol_names
            .iter()
            .filter(|(sym, n)| {
                n.as_str() == name && driver.phase.program.types().schemes.contains_key(sym)
            })
            .map(|(sym, _)| *sym)
            .collect();
        candidates.sort();
        let Some(symbol) = candidates.first() else {
            panic!(
                "no scheme found for {name:?}; schemes: {:?}",
                driver
                    .phase
                    .program
                    .types()
                    .schemes
                    .keys()
                    .map(|k| resolved.symbol_names.get(k))
                    .collect::<Vec<_>>()
            );
        };
        driver.phase.program.types().schemes[symbol].render()
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

    /// LIT-01: every integer literal must fit the signed 64-bit range, with
    /// recovery instead of a panic (`docs/backend-parity-ledger.md`).
    #[test]
    fn rejects_an_integer_literal_above_the_signed_64_bit_range() {
        let t = check("// no-core\nlet a = 9_223_372_036_854_775_808");
        assert_eq!(
            type_errors(&t),
            ["Integer literal 9_223_372_036_854_775_808 is outside the signed 64-bit range"]
        );
    }

    #[test]
    fn accepts_the_signed_64_bit_integer_boundaries() {
        let t = check(
            "// no-core\nlet lo = -9_223_372_036_854_775_808\nlet hi = 9_223_372_036_854_775_807",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "lo"), "Int");
        assert_eq!(ty_of(&t, "hi"), "Int");
    }

    #[test]
    fn rejects_an_out_of_range_integer_pattern() {
        let t = check(
            "// no-core\nfunc f(x: Int) -> Int {\n\tmatch x {\n\t\t9_223_372_036_854_775_808 -> 1,\n\t\t_ -> 0\n\t}\n}",
        );
        assert_eq!(
            type_errors(&t),
            ["Integer literal 9_223_372_036_854_775_808 is outside the signed 64-bit range"]
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
                "\n        func fstA(r) { r.a }\n        (fstA(r: { a: 1 }), fstA(r: { a: 2, b: true }))\n    ",
                true,
                false,
            ),
            (
                "types::row_presence_constraint_is_polymorphic",
                "\n        func useA(r) { r.a } // imposes HasField(row_var, \"a\", Int)\n        (useA(r: { a: 1 }), useA(r: { a: 2, c: true }))\n    ",
                true,
                false,
            ),
            (
                "types::types_non_annotated_record_param",
                "\n        func foo(x) {\n            (x.y, x.z)\n        }\n\n        foo(x: { y: 123, z: 1.23 })\n        foo(x: { y: 123, z: 123 })\n        ",
                true,
                false,
            ),
            (
                "types::checks_generic_struct_arg",
                "\n        struct Person {\n            func getAge<T>(consume t: T) -> T { t }\n        }\n\n        Person().getAge(t: 123)\n        Person().getAge(t: 1.23)\n        ",
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
                "\n            func getX(r) { r.x }\n            getX(r: { x: 1 })\n            ",
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
                "\"hello\".utf8().slice(start: 1, byte_count: 3)",
                true,
                true,
            ),
            (
                "types::types_string_find",
                "\"hello\".find(needle: \"ll\"); \"hello\".find_from(needle: \"l\", start: 3)",
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
                "@unsafe { let x: RawPtr = __IR(\"$? = alloc int 1\"); x; () }",
                true,
                false,
            ),
            ("types::types_array_properties", "[1,2,3].count", true, true),
            (
                "types::types_basic_binary",
                "func a(x) { x + 1 } ; a(x: 123)",
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
                "\n        func identity(x) { x }\n        identity(x: 123)\n        identity(x: true)\n        ",
                true,
                false,
            ),
            (
                "types::stores_func_instantiations",
                "\n        func identity(x) { x }\n        identity(x: 123)\n        identity(x: true)\n        ",
                true,
                false,
            ),
            (
                "types::stores_struct_instantiations",
                "\n        struct Wrapper<T> {\n            let wrapped: T\n        }\n        Wrapper(wrapped: 123)\n        Wrapper(wrapped: true)\n        ",
                true,
                false,
            ),
            // types::types_nested_func moved to docs/parity-test-audit.md's
            // deliberate-design-changes list: inferred params are borrows
            // (ownership plan 3.3(b)), and implicit closure captures of
            // borrowed params are rejected until a capture mode is explicit
            // — exactly like the annotated twin `func fizz<T>(x: T)`.
            (
                "types::infers_simple_recursion",
                "\n        func rec(x, y, z) {\n            if x == y { x } else { rec(x: y-z, y: y, z: z) }\n        }\n\n        rec(x: 0, y: 2, z: 1)\n        rec(x: 0.0, y: 2.0, z: 1.0)\n        ",
                true,
                true,
            ),
            (
                "types::explicit_generic_function_instantiates",
                "\n        func id<T>(consume x: T) -> T { x }\n        id(x: 123)\n        id(x: true)\n    ",
                true,
                false,
            ),
            (
                "types::explicit_call_args",
                "\n        func id<T>(x) { x }\n        id<Byte>(x: 123)\n    ",
                true,
                false,
            ),
            (
                "types::generic_function_body_must_respect_its_own_type_vars",
                "\n        func bad<T>(x: T) -> T { 0 } // 0 == Int != T\n        bad(x: true)\n    ",
                false,
                false,
            ),
            (
                "types::types_call_let",
                "\n        func id(x) { x }\n        let a = id(x: 123)\n        let b = id(x: 1.23)\n        a\n        b\n        ",
                true,
                false,
            ),
            (
                "types::types_nested_identity",
                "\n        func identity(x) { x }\n        identity(x: identity(x: 123))\n        identity(x: identity(x: true))\n        ",
                true,
                false,
            ),
            (
                "types::types_multiple_args",
                "\n        func makeTuple(x, y) {\n            (x, y)\n        }\n\n        makeTuple(x: 123, y: true)\n            ",
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
                "\n        func id<T>(x: T) -> T { x }\n        id<Bool>(x: 123)\n    ",
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
                "\n        func f(x: Int) -> Int { x }\n        f(x: true)\n    ",
                false,
                false,
            ),
            (
                "types::return_annotation_is_enforced_in_body",
                "\n        func f(x: Int) -> Int { true }\n        f(x: 1)\n    ",
                false,
                false,
            ),
            (
                "types::types_recursive_func",
                "\n        func fizz(n) {\n            if true {\n                123\n            } else {\n                fizz(n: n)\n            }\n        }\n\n        fizz(n: 456)\n        ",
                true,
                false,
            ),
            (
                "types::recursion_is_monomorphic_within_binding_group",
                "\n        func g(x) {\n            // Force a shape change on the recursive call to try to “polymorphically” recurse.\n            g( x: (x, x) )\n        }\n        g(x: 1)\n    ",
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
                "types::types_struct_pattern_in_match",
                "\n        struct Point {\n            let x: Int\n            let y: Int\n            init(x: Int, y: Int) {\n                self.x = x\n                self.y = y\n                self\n            }\n        }\n        match Point(x: 1, y: 2) {\n            Point { x, y } -> (x, y)\n        }\n        ",
                true,
                false,
            ),
            (
                "types::types_struct_pattern_in_let",
                "\n        struct Point {\n            let x: Int\n            let y: Int\n            init(x: Int, y: Int) {\n                self.x = x\n                self.y = y\n                self\n            }\n        }\n        let Point { x, y } = Point(x: 1, y: 2)\n        (x, y)\n        ",
                true,
                false,
            ),
            (
                "types::struct_pattern_rest_omits_fields",
                "\n        struct Point {\n            let x: Int\n            let y: Int\n            init(x: Int, y: Int) {\n                self.x = x\n                self.y = y\n                self\n            }\n        }\n        let Point { x, .. } = Point(x: 1, y: 2)\n        x\n        ",
                true,
                false,
            ),
            (
                "types::struct_pattern_checks_field_types",
                "\n        struct Point {\n            let x: Int\n            let y: Int\n            init(x: Int, y: Int) {\n                self.x = x\n                self.y = y\n                self\n            }\n        }\n        match Point(x: 1, y: 2) {\n            Point { x: true, .. } -> ()\n        }\n        ",
                false,
                false,
            ),
            (
                "types::struct_pattern_rejects_unknown_fields",
                "\n        struct Point {\n            let x: Int\n            let y: Int\n            init(x: Int, y: Int) {\n                self.x = x\n                self.y = y\n                self\n            }\n        }\n        match Point(x: 1, y: 2) {\n            Point { z, .. } -> z\n        }\n        ",
                false,
                false,
            ),
            (
                "types::struct_pattern_requires_all_fields_without_rest",
                "\n        struct Point {\n            let x: Int\n            let y: Int\n            init(x: Int, y: Int) {\n                self.x = x\n                self.y = y\n                self\n            }\n        }\n        match Point(x: 1, y: 2) {\n            Point { x } -> x\n        }\n        ",
                false,
                false,
            ),
            (
                "types::struct_pattern_with_refutable_field_is_not_exhaustive",
                "\n        struct Point {\n            let x: Int\n            let y: Int\n            init(x: Int, y: Int) {\n                self.x = x\n                self.y = y\n                self\n            }\n        }\n        match Point(x: 1, y: 2) {\n            Point { x: 0, .. } -> 1\n        }\n        ",
                false,
                false,
            ),
            (
                "types::struct_pattern_instantiates_generic_fields",
                "\n        struct Box<T> {\n            let value: T\n            init(value: T) {\n                self.value = value\n                self\n            }\n        }\n        match Box(value: 41) {\n            Box { value } -> (value, true)\n        }\n        ",
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
                "\n        func outer(r) {\n            let _x = r.a;               // forces r to have field `a`\n            let k  = func() { r };      // returns the *same* env row (no row-generalization)\n            match k() {\n                { c } -> c              // `c` is not known; should produce one error\n            }\n        }\n        outer(r: { a: 1 })\n    ",
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
                "\n        func outer(r) {\n            let x = r.a; // creates an internal Row::Var tail for r's row (your ensure_row/projection does this)\n            let k = func() { r } // local let; do NOT generalize the outer row var into a Row::Param\n            match k() {\n                { c } -> c // should be a missing-field error (no 'c' in r)\n            }\n        }\n        outer(r: { a: 1 })\n    ",
                false,
                false,
            ),
            (
                "types::types_row_type_as_params",
                "\n        func foo(x: { y: Int, z: Bool }) {\n            (x.y, x.z)\n        }\n\n        foo(x: { y: 123, z: true })\n        ",
                true,
                false,
            ),
            (
                "types::enforces_non_annotated_record",
                "\n        func foo(point) {\n            (point.x, point.y)\n        }\n\n        foo(point: { x: 123, z: 123 })\n        ",
                false,
                false,
            ),
            (
                "types::enforces_row_type_as_params",
                "\n        func foo(x: { y: Int, z: Bool }) {\n            (x.y, x.z)\n        }\n\n        foo(x: { y: 123 })\n        ",
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
                "\n        struct Person<T> {\n            let age: T\n\n            init(other: T) {\n                self.age = other\n            }\n        }\n\n        Person(other: 123).age\n        ",
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
                "\n        struct Person {\n            let age: Int\n        }\n\n        let person = Person(age: 123)\n        callNonExisting(aged: person)\n\n        func callNonExisting(aged) {\n            aged.getAge()\n        }\n        ",
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
                "\n          enum Outer {\n              case a(Inner)\n              case b(Inner)\n          }\n\n          enum Inner {\n              case x(Int)\n              case y(Int)\n          }\n\n          func extract(o: Outer) -> Int {\n              match o {\n                  .a(.x(n) | .y(n)) | .b(.x(n) | .y(n)) -> n\n              }\n          }\n\n          extract(o: Outer.a(Inner.x(99)))\n          ",
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
                "\n            protocol Marker {\n                func mark() -> Int\n            }\n\n            struct Foo {}\n\n            func takes<T: Marker>(x: T) {}\n\n            takes(x: Foo())\n            ",
                false,
                false,
            ),
            (
                "types::rejects_missing_marker_conformance_without_requirements",
                "\n            protocol Marker {}\n\n            struct Foo {}\n\n            func takes<T: Marker>(x: T) {}\n\n            takes(x: Foo())\n            ",
                false,
                false,
            ),
            (
                "types::generic_constructor_in_extension_block",
                "\n          struct Wrapper<T> {\n              let value: T\n\n              init(value: T) {\n                  self.value = value\n              }\n          }\n\n          struct Box<T> {\n              let inner: T\n          }\n\n          extend<T> Box<T> {\n              consuming func wrap() -> Wrapper<T> {\n                  Wrapper<T>(value: self.inner)\n              }\n          }\n          ",
                true,
                false,
            ),
            (
                "types::generic_constructor_with_explicit_type_arg",
                "\n          struct Container<Element> {\n              let item: Element\n\n              init(item: Element) {\n                  self.item = item\n              }\n          }\n\n          struct MyList<Element> {\n              let first: Element\n          }\n\n          extend<Element> MyList<Element> {\n              consuming func boxFirst() -> Container<Element> {\n                  Container<Element>(item: self.first)\n              }\n          }\n          ",
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
                "\n            protocol Countable { func getCount() -> Int }\n            struct Person { let count: Int }\n            extend Person: Countable {\n                func getCount() {\n                    self.count\n                }\n            }\n\n            func getCount<T: Countable>(countable: T) {\n                countable.getCount()\n            }\n\n            let person = Person(count: 1)\n            getCount(countable: person)\n            ",
                true,
                false,
            ),
            (
                "types::tests_infers_associated_types",
                "\n        protocol Aged {\n            associated T\n\n            func getAge() -> T\n        }\n\n        struct Inty {}\n        extend Inty: Aged {\n            func getAge() {\n                123\n            }\n        }\n\n        struct Floaty {}\n        extend Floaty: Aged {\n            func getAge() {\n                1.23\n            }\n        }\n\n        func get<A: Aged>(aged: A) {\n            aged.getAge()\n        }\n\n        get(aged: Inty())\n        get(aged: Floaty())\n        ",
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
                "\n        protocol Addy {\n            associated RHS\n            associated Ret\n            consuming func addy(rhs: RHS) -> Ret\n        }\n\n        extend Int: Addy {\n            consuming func addy(rhs: Int) -> Int {\n                self\n            }\n        }\n\n        1.addy(rhs: 2)\n        ",
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
                "\n        struct A {}\n        struct B {}\n        struct C {}\n        extend A: Add<B> {\n            func add(_ rhs: B) -> C {\n                C()\n            }\n        }\n        A() + B()\n        ",
                true,
                true,
            ),
            (
                "types::types_add_method_in_func",
                "func add(x) { x + 1 }\n\n            add(x: 2)\n            ",
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
                "\n        func fib(n) {\n            if n <= 1 { return n }\n\n            return fib(n: n - 2) + fib(n: n - 1)\n        }\n\n        fib(n: 3)\n        ",
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
                "\n            protocol Counter {\n                func next() -> Int\n            }\n\n            struct MyCounter {\n                let value: Int\n\n                extend Self: Counter {\n                    func next() -> Int {\n                        self.value\n                    }\n                }\n            }\n\n            func useCounter<T: Counter>(c: T) -> Int {\n                c.next()\n            }\n\n            useCounter(c: MyCounter(value: 42))\n            ",
                true,
                false,
            ),
            (
                "types::nested_self_extend_can_use_protocol_default_method",
                "\n            protocol P {\n                func f() { 1 }\n            }\n\n            struct S {\n                extend Self: P {}\n            }\n\n            func call<T: P>(x: T) -> Int {\n                x.f()\n            }\n\n            call(x: S())\n            ",
                true,
                false,
            ),
            (
                "types::nested_self_extend_does_not_use_outer_method_as_witness",
                "\n            protocol P {\n                func f() -> Int\n            }\n\n            struct S {\n                func f() -> Int { 1 }\n\n                extend Self: P {}\n            }\n\n            func call<T: P>(x: T) -> Int {\n                x.f()\n            }\n\n            call(x: S())\n            ",
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
                "\n            func transform(x: Int, f: (Int) -> Int) -> Int {\n                f(x)\n            }\n            transform(x: 1, f: func(n) { n })\n            ",
                true,
                false,
            ),
            (
                "types::types_func_literal_call_arg_return_mismatch_returns_error",
                "\n            func apply(f: () -> Int) -> Int {\n                f()\n            }\n            apply(f: func() { true })\n            ",
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
                "\n            func transform(x: Int, f: (Int) -> Int) -> Int {\n                f(x)\n            }\n            transform(x: 1){ n in n }\n            ",
                true,
                false,
            ),
            (
                "types::finalize_ty_produces_correct_poly_entry",
                "\n            func id(x) { x }\n            id(x: 123)\n            ",
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
                "\n            enum Opt<T> { case some(T), none }\n            func use_int(x: Int) {}\n            let val = Opt.some(42)\n            if let .some(x) = val { use_int(x: x) }\n            ",
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
                "\n            func printy<T: Showable>(showable: T) {\n                print_raw(showable.show())\n            }\n            printy(showable: [1, 2, 3])\n            ",
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
                "\n            func id<T>(x: T) -> T { x }\n            id<Int, Bool>(x: 1)\n            ",
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
                "\n            effect 'fizz(x: Int, y: Bool) -> Int\n\n            @handle 'fizz { a, b in\n                'continue 0\n            }\n            ",
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
                "effects::bare_continue_checks_unit_against_effect_return_type",
                "\n            effect 'fizz() -> Int\n\n            @handle 'fizz {\n                'continue\n            }\n            ",
                false,
                false,
            ),
            (
                "effects::bare_continue_in_unit_handler_checks_clean",
                "\n            effect 'fizz() -> ()\n\n            @handle 'fizz {\n                'continue\n            }\n            ",
                true,
                false,
            ),
            (
                "effects::continue_in_handler_uses_effect_return_type",
                "\n            effect 'fizz() -> Int\n\n            @handle 'fizz {\n                'continue 123\n            }\n            ",
                true,
                false,
            ),
            (
                "effects::continue_in_handler_checks_return_type",
                "\n            effect 'fizz() -> Int\n\n            @handle 'fizz {\n                'continue true\n            }\n            ",
                false,
                false,
            ),
            (
                "effects::continue_with_value_outside_handler_errors",
                "'continue 1",
                false,
                false,
            ),
            (
                "effects::dupe_handlers_warn",
                "\n                effect 'fizz() -> Int\n\n                @handle 'fizz { 'continue 0 }\n                @handle 'fizz { 'continue 1 }\n\n                'fizz()\n                ",
                false,
                false,
            ),
            (
                "effects::handler_removes_effect_from_enclosing_func",
                "\n          effect 'fizz() -> Int\n\n          func fizzes() '[] {\n            @handle 'fizz { 'continue 123 }\n\n            'fizz()\n          }\n        ",
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
                "\n            effect 'state<T>(value: T) -> T\n            @handle 'state { v in 'continue v }\n            'state<Int>(value: 42)\n        ",
                true,
                false,
            ),
            (
                "effects::generic_effect_call_inferred",
                "\n            effect 'state<T>(value: T) -> T\n            @handle 'state { v in 'continue v }\n            'state(value: 42)\n        ",
                true,
                false,
            ),
            (
                "effects::generic_effect_type_mismatch",
                "\n            effect 'state<T>(value: T) -> T\n            @handle 'state { v in 'continue v }\n            'state<Int>(value: true)\n        ",
                false,
                false,
            ),
            (
                "effects::generic_effect_multiple_params",
                "\n            effect 'pair<A, B>(first: A, second: B) -> (A, B)\n            @handle 'pair { a, b in 'continue (a, b) }\n            'pair<Int, Bool>(first: 42, second: true)\n        ",
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
                "\n            effect 'e() -> Int\n\n            func f() -> Int {\n                'e()\n            }\n\n            let x = f()\n            @handle 'e { 'continue 1 }\n            x\n        ",
                false,
                false,
            ),
            (
                "effects::one_handler_covers_two_instantiations",
                "\n            effect 'state<T>(value: T) -> T\n\n            func g() '[] {\n                @handle 'state { v in 'continue v }\n                'state(value: 1)\n                'state(value: true)\n                ()\n            }\n        ",
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
                "\n            effect 'e() -> Int\n\n            func f() -> Int {\n                'e()\n            }\n\n            @handle 'e { 'continue 1 }\n            let x = f()\n            x\n        ",
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
        assert_eq!(ty_of(&t, "get"), "(&Box<Int>) -> Int");
    }

    #[test]
    fn type_aliases_can_apply_captured_generics() {
        let t = check(
            "// no-core\nstruct T<U> { let value: U }\nstruct Box<U> {\n  typealias F = T<U>\n  let value: F\n}\nfunc get(consume box: Box<Int>) -> T<Int> { box.value }",
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
            errors.iter().any(|error| error
                .contains("the annotation requires Bool, but the expression has type Int")),
            "expected associated type alias to constrain the witness, got {errors:?}"
        );
    }

    #[test]
    fn any_protocol_type_is_first_class_in_annotations() {
        let t = check(
            "// no-core\nprotocol Showable {\n  func show() -> Int\n}\ntypealias AnyShowable = any Showable\nfunc idAny(consume x: AnyShowable) -> AnyShowable { x }",
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
        assert_eq!(t.phase.program.types().existential_packs.len(), 1);
    }

    #[test]
    fn any_protocol_members_use_erased_requirement_signatures() {
        let t = check(
            "// no-core\nprotocol Showable {\n  func show() -> Int\n}\nfunc render(value: any Showable) -> Int { value.show() }",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "render"), "(&any Showable) -> Int");
    }

    #[test]
    fn any_protocol_with_associated_binding_substitutes_members() {
        let t = check(
            "// no-core\nprotocol Iterator {\n  associated Element\n  func next() -> Element\n}\nfunc nextInt(it: any Iterator<Element = Int>) -> Int { it.next() }",
        );
        assert_clean(&t);
        assert_eq!(
            ty_of(&t, "nextInt"),
            "(&any Iterator<Element = Int>) -> Int"
        );
    }

    #[test]
    fn object_safe_any_protocol_satisfies_generic_protocol_bounds() {
        let t = check(
            "// no-core\nprotocol Showable {\n  consuming func show() -> Int\n}\nextend Int: Showable {\n  consuming func show() -> Int { self }\n}\nfunc render<T: Showable>(consume value: T) -> Int { value.show() }\nlet value: any Showable = 1\nlet rendered = render(value: value)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "rendered"), "Int");
    }

    #[test]
    fn expected_any_protocol_rejects_existential_upcasts() {
        let t = check(
            "// no-core\nprotocol Readable {\n  func read() -> Int\n}\nprotocol ReadWrite: Readable {\n  func write(value: Int) -> ()\n}\nfunc upcast(consume value: any ReadWrite) -> any Readable { value }",
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

    /// B4: an implicit existential pack must not launder a borrow into an
    /// owned `any P`. A borrow-by-default parameter of a `'linear` type
    /// packing into an owned existential would escape linearity — the value
    /// stays consumable at the call site while the pack owns it too.
    #[test]
    fn implicit_pack_rejects_borrowed_linear_payload() {
        let t = check(
            "// no-core\nprotocol Fd {\n  func fd_value() -> Int\n}\nstruct Socket 'linear {\n\tlet fd: Int\n}\nextend Socket: Fd {\n  func fd_value() -> Int { self.fd }\n}\nfunc pack(s: Socket) -> any Fd {\n\ts\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Socket") && error.contains("&Socket")),
            "expected borrowed linear payload to be rejected by the implicit pack, got {errors:?}"
        );
    }

    /// B4 guard: an owned (consumed) payload still packs implicitly.
    #[test]
    fn implicit_pack_accepts_owned_consumed_payload() {
        let t = check(
            "// no-core\nprotocol Fd {\n  func fd_value() -> Int\n}\nstruct Socket 'linear {\n\tlet fd: Int\n}\nextend Socket: Fd {\n  func fd_value() -> Int { self.fd }\n}\nfunc pack(consume s: Socket) -> any Fd {\n\ts\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "pack"), "(Socket) -> any Fd");
    }

    /// B4: packing from a borrowed CheapClone payload compiles by retaining
    /// (the same tier-2 coercion an owned argument slot gets), recorded for
    /// lowering at the pack node. Core `String` is CheapClone.
    #[test]
    fn implicit_pack_of_borrowed_cheap_clone_payload_records_a_clone() {
        let t = Driver::new(
            vec![Source::from(
                "protocol Sized {\n  func size() -> Int\n}\nextend String: Sized {\n  func size() -> Int { self.byte_count }\n}\nfunc pack(s: String) -> any Sized {\n\ts\n}",
            )],
            DriverConfig::new("TypesTest"),
        )
        .parse()
        .expect("parse failed")
        .resolve_names()
        .expect("name resolution failed")
        .type_check();
        assert_clean(&t);
        assert!(
            !t.phase.program.types().coerce_clones.is_empty(),
            "expected the borrowed CheapClone payload to record a retain for lowering"
        );
    }

    #[test]
    fn existential_self_conformance_satisfies_superprotocol_bounds() {
        let t = check(
            "// no-core\nprotocol Readable {\n  consuming func read() -> Int\n}\nprotocol ReadWrite: Readable {\n  func write(value: Int) -> Int\n}\nextend Int: ReadWrite {\n  consuming func read() -> Int { self }\n  func write(value: Int) -> Int { value }\n}\nfunc readIt<T: Readable>(consume value: T) -> Int { value.read() }\nlet value: any ReadWrite = 1\nlet result = readIt(value: value)",
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
            "// no-core\nprotocol Iterator {\n  associated Element\n  func next() -> Element\n}\nfunc use(consume it: any Iterator<Element = Int>) -> any Iterator<Element = Int> { it }",
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
        assert_eq!(
            errors[0],
            "Type mismatch in annotated expression: the annotation requires Int, but the expression has type Float"
        );
    }

    #[test]
    fn identity_generalizes() {
        // Damas-Milner generalization at the top-level binding group:
        // identity gets a polymorphic scheme, each call site instantiates
        // fresh. The param is a borrow (ADR 0018 borrow-by-default applies
        // to inferred params too — plan 3.3(b)), so identity returns a
        // borrow of its argument; Copy instantiations erase the wrap.
        let t = check(
            "// no-core\nfunc identity(x) { x }\nlet a = identity(x: 123)\nlet b = identity(x: 1.5)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "identity"), "<T0>(&T0) -> &T0");
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
        assert_eq!(
            type_errors(&t),
            [
                "Type mismatch between branches: one branch has type Float, but another has type Int; all branches must have the same type"
            ]
        );
    }

    #[test]
    fn block_values_are_last_expression() {
        let t = check("// no-core\nlet a = if true { let b = 1\n b } else { 2 }");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "a"), "Int");
    }

    #[test]
    fn blank_line_allows_unqualified_enum_implicit_return_after_call() {
        let t = check(
            "// no-core\nenum Fizz { case foo, bar }\nfunc side() -> () { () }\nfunc buzz() -> Fizz {\n\tside()\n\n\t.foo\n}",
        );
        assert_clean(&t);
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
        let t = check("// no-core\nfunc f(n) { f(n: n) }");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "f"), "<T0, T1>(&T0) -> T1");
    }

    #[test]
    fn effect_polymorphic_apply() {
        // The effect row of `f` unifies with apply's ambient row; both
        // generalize together (display elides pure/quantified-tail rows).
        let t = check("// no-core\nfunc apply(f) { f() }");
        assert_clean(&t);
        // The function-typed param is itself borrowed (calling through the
        // borrow is a read), matching `func apply<T>(f: () -> T)`.
        assert_eq!(ty_of(&t, "apply"), "<T0>(&() -> T0) -> T0");
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
        assert_eq!(ty_of(&t, "f"), "<T0>(&T0) -> &T0");
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
        assert_eq!(
            type_errors(&t),
            [
                "Type mismatch in assignment: the target requires Int, but the assigned value has type Float"
            ]
        );
    }

    #[test]
    fn argument_mismatch_explains_parameter_and_argument_types() {
        let t = check("// no-core\nfunc f(value: Int) { value }\nf(value: true)");
        assert_eq!(
            type_errors(&t),
            [
                "Type mismatch in function argument: the parameter requires Int, but the argument has type Bool"
            ]
        );
    }

    #[test]
    fn return_mismatch_explains_declared_and_returned_types() {
        let t = check("// no-core\nfunc f() -> Int { return true }");
        assert_eq!(
            type_errors(&t),
            [
                "Type mismatch in return value: the function requires Int, but the returned expression has type Bool"
            ]
        );
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
            !t.phase.program.types().node_types.is_empty(),
            "expected node types to be recorded"
        );
    }

    /// One authority per type question (ownership-soundness 7.4): binder
    /// types live in `local_tys` (read via `binder_ty`), and binder NODES
    /// never get a `node_types` entry — so a per-node fallback for a
    /// binder can only ever miss, and consumers must not reach for one.
    #[test]
    fn binder_types_live_in_local_tys_not_node_types() {
        use derive_visitor::{Drive, Visitor};

        #[derive(Default)]
        struct Binders {
            found: Vec<(
                crate::node_id::NodeID,
                crate::name_resolution::symbol::Symbol,
            )>,
        }
        impl Visitor for Binders {
            fn visit(&mut self, item: &dyn std::any::Any, event: derive_visitor::Event) {
                if matches!(event, derive_visitor::Event::Enter)
                    && let Some(pattern) = item.downcast_ref::<crate::typed_ast::Pattern>()
                {
                    self.found.extend(pattern.collect_binders());
                }
            }
        }

        let t = check(
            "// no-core\nenum Maybe<T> {\n\tcase definitely(T)\n\tcase nope\n}\nlet maybe = Maybe.definitely(1234)\nlet result = match maybe {\n\t.definitely(x) -> x,\n\t.nope -> 0\n}",
        );
        assert_clean(&t);
        let types = t.phase.program.types();
        let mut binders = Binders::default();
        for file in t.phase.program.files().values() {
            for root in &file.roots {
                root.drive(&mut binders);
            }
        }
        assert!(!binders.found.is_empty(), "expected pattern binders");
        for (id, symbol) in binders.found {
            assert!(
                !types.node_types.contains_key(&id),
                "binder node {id:?} unexpectedly has a node_types entry"
            );
            // Local binders resolve through `binder_ty`; top-level binders
            // through `schemes`.
            assert!(
                types.binder_ty(symbol).is_some() || types.schemes.contains_key(&symbol),
                "binder {symbol:?} resolves through neither binder_ty nor schemes"
            );
        }
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
    fn labeled_enum_payloads_construct_and_match() {
        let t = check(
            "// no-core\nenum Foo {\n\tcase bar(fizz: Int, buzz: Int)\n\tcase ok(Int)\n}\nlet foo = Foo.bar(fizz: 123, buzz: 456)\nlet result = match foo {\n\t.bar(fizz: _, buzz: value) -> value,\n\t.ok(value) -> value\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "foo"), "Foo");
        assert_eq!(ty_of(&t, "result"), "Int");
    }

    #[test]
    fn labeled_leading_dot_payloads_resolve_after_inference() {
        let t = check(
            "// no-core\nenum Foo {\n\tcase bar(fizz: Int, buzz: Int)\n}\nfunc id<T>(consume value: T) -> T { value }\nlet foo: Foo = id(value: .bar(fizz: 123, buzz: 456))",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "foo"), "Foo");
    }

    #[test]
    fn labeled_enum_payloads_require_declared_labels_in_order() {
        let t = check(
            "// no-core\nenum Foo {\n\tcase bar(fizz: Int, buzz: Int)\n}\nFoo.bar(buzz: 1, fizz: 2)",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("Payload labels"), "{errors:?}");
    }

    #[test]
    fn labeled_enum_patterns_require_declared_labels_in_order() {
        let t = check(
            "// no-core\nenum Foo {\n\tcase bar(fizz: Int, buzz: Int)\n}\nmatch Foo.bar(fizz: 1, buzz: 2) {\n\t.bar(buzz: _, fizz: _) -> 1\n}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("Payload labels"), "{errors:?}");
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
            "// no-core\nprotocol Foo {\n\tfunc foo() -> Int\n}\nstruct Thing {}\nextend Thing: Foo {\n\tfunc foo() { 123 }\n}\nfunc fizz<T: Foo>(t: T) { t.foo() }\nlet r = fizz(t: Thing())",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "fizz"), "<T0: Foo>(&T0) -> Int");
        assert_eq!(ty_of(&t, "r"), "Int");
    }

    #[test]
    fn conformance_violation_errors() {
        let t = check(
            "// no-core\nprotocol Foo {\n\tfunc foo() -> Int\n}\nfunc fizz<T: Foo>(t: T) { t.foo() }\nfizz(t: 123)",
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
    fn init_requirement_satisfied_by_explicit_init() {
        let t = check(
            "// no-core\nprotocol FromPair {\n\tinit(lower: Int, upper: Int)\n}\nstruct Pair {\n\tlet lower: Int\n\tlet upper: Int\n\tinit(lower: Int, upper: Int) {\n\t\tself.lower = lower\n\t\tself.upper = upper\n\t}\n}\nextend Pair: FromPair {}",
        );
        assert_clean(&t);
    }

    #[test]
    fn init_requirement_satisfied_by_memberwise_init() {
        let t = check(
            "// no-core\nprotocol FromPair {\n\tinit(lower: Int, upper: Int)\n}\nstruct Pair {\n\tlet lower: Int\n\tlet upper: Int\n}\nextend Pair: FromPair {}",
        );
        assert_clean(&t);
    }

    #[test]
    fn init_requirement_arity_mismatch_errors() {
        let t = check(
            "// no-core\nprotocol FromPair {\n\tinit(lower: Int, upper: Int)\n}\nstruct Solo {\n\tlet x: Int\n}\nextend Solo: FromPair {}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("init"), "{errors:?}");
    }

    #[test]
    fn protocol_init_constructs_concrete_self() {
        let t = check(
            "// no-core\nprotocol FromPair {\n\tinit(lower: Int, upper: Int)\n}\nstruct Pair {\n\tlet lower: Int\n\tlet upper: Int\n}\nextend Pair: FromPair {}\nlet p: Pair = FromPair(lower: 1, upper: 2)\nlet l = p.lower",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "p"), "Pair");
        assert_eq!(ty_of(&t, "l"), "Int");
    }

    #[test]
    fn generic_protocol_init_constructs_concrete_self() {
        let t = check(
            "// no-core\nprotocol FromPair<T> {\n\tinit(lower: T, upper: T)\n}\nstruct Pair<T> {\n\tlet lower: T\n\tlet upper: T\n}\nextend Pair<T>: FromPair<T> {}\nlet p: Pair<Int> = FromPair(lower: 1, upper: 2)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "p"), "Pair<Int>");
    }

    #[test]
    fn protocol_construction_without_init_requirement_errors() {
        let t = check("// no-core\nprotocol Foo {\n\tfunc foo() -> Int\n}\nlet x = Foo()");
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("init requirement"), "{errors:?}");
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
        assert_eq!(ty_of(&t, "showit"), "<T0: Show>(&T0) -> Int");
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
        assert_eq!(ty_of(&t, "get"), "<T0, T1>(&T0) -> T1 where &T0.val: T1");
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
        assert_eq!(ty_of(&t, "f"), "<T0, T1>(&T0) -> T1 where &T0.m: () -> T1");
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
            "// no-core\nprotocol Aa {\n\tfunc m() -> Int\n}\nprotocol Bb {\n\tfunc m() -> Int\n}\nextend Int: Aa {\n\tfunc m() -> Int { 1 }\n}\nextend Int: Bb {\n\tfunc m() -> Int { 2 }\n}\nfunc f(x) { x.m() }\nlet r = f(x: 2)",
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
            "// no-core\nprotocol Add<RHS> {\n\tassociated Ret\n\tfunc add(rhs: RHS) -> Ret\n}\nprotocol Subtract<RHS> {\n\tassociated Ret\n\tfunc minus(rhs: RHS) -> Ret\n}\nprotocol Comparable<RHS> {\n\tfunc lte(rhs: RHS) -> Bool\n}\nextend Int: Add<Int> {\n\tfunc add(rhs: Int) -> Int { 0 }\n}\nextend Int: Subtract<Int> {\n\tfunc minus(rhs: Int) -> Int { 0 }\n}\nextend Int: Comparable<Int> {\n\tfunc lte(rhs: Int) -> Bool { true }\n}\nfunc fib(n) {\n\tif n <= 1 { return n }\n\treturn fib(n: n - 2) + fib(n: n - 1)\n}\nlet x = fib(n: 24)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Int");
        // Borrow-by-default params (plan 3.3(b)): `n` is `&T0` and
        // `return n` makes the result a borrow, so Add's Ret must equal
        // `&T0`, while Subtract's Ret (fed back into the borrowed param at
        // the Apply boundary, where the borrow peels) must equal bare
        // `T0`. Both discharge at Int, where the borrow erases.
        assert_eq!(
            ty_of(&t, "fib"),
            "<T0: Add<T0> & Comparable<Int> & Subtract<Int>>(&T0) -> &T0 where &T0 == T0.Ret && T0 == T0.Ret"
        );
    }

    #[test]
    fn generic_bound_call_at_two_types() {
        // Show.tlk shape (two conforming types through one bounded generic).
        let t = check(
            "// no-core\nprotocol Showy {\n\tfunc show() -> Int\n}\nstruct Fizz {\n\tlet a: Int\n}\nextend Fizz: Showy {\n\tfunc show() { self.a }\n}\nextend Int: Showy {\n\tfunc show() { 0 }\n}\nfunc printy<T: Showy>(s: T) { s.show() }\nprinty(s: 123)\nprinty(s: Fizz(a: 1))",
        );
        assert_clean(&t);
    }

    #[test]
    fn effect_where_clause_constrains_perform_type_arguments() {
        let t = check(
            "// no-core\nprotocol P {}\nextend Int: P {}\neffect 'choose<T>(value: T) -> T where T: P\n@handle 'choose { v in 'continue v }\n'choose(value: true)",
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
            "// no-core\nprotocol Showy {\n\tfunc show() -> Int\n}\nprotocol BoxShow {\n\tfunc boxShow() -> Int\n}\nextend Int: Showy {\n\tfunc show() -> Int { 1 }\n}\nstruct Box<T> {\n\tlet item: T\n}\nextend<T> Box<T>: BoxShow where T: Showy {\n\tfunc boxShow() -> Int {\n\t\tself.item.show()\n\t}\n}\nlet good = Box(item: 1).boxShow()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "good"), "Int");
    }

    #[test]
    fn extend_where_same_type_is_available_in_witness_body() {
        let t = check(
            "// no-core\nprotocol IntBox {\n\tfunc intItem() -> Int\n}\nstruct Box<T> {\n\tlet item: T\n}\nextend<T> Box<T>: IntBox where T == Int {\n\tfunc intItem() -> Int {\n\t\tself.item\n\t}\n}\nlet good = Box(item: 1).intItem()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "good"), "Int");
    }

    #[test]
    fn concrete_extension_head_uses_a_concrete_nominal_argument() {
        let t = check(
            "// no-core\nprotocol P { func get() -> Int }\nstruct Box<Element> { let value: Element }\nextend Box<Int>: P { func get() -> Int { self.value } }\nlet value = Box(value: 1).get()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "value"), "Int");
    }

    #[test]
    fn disjoint_conformance_calls_publish_distinct_row_evidence() {
        let t = check(
            "// no-core\nprotocol P { func get() -> Int }\nstruct Box<Element> { let value: Element }\nextend Box<Int>: P { func get() -> Int { 1 } }\nextend Box<Bool>: P { func get() -> Int { 2 } }\nlet intValue = Box(value: 1).get()\nlet boolValue = Box(value: true).get()",
        );
        assert_clean(&t);
        let evidence = t
            .phase
            .program
            .types()
            .member_resolutions
            .values()
            .filter_map(|resolution| match resolution {
                crate::types::output::MemberResolution::ViaConformance { row, witness, .. } => {
                    Some((*row, *witness))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(evidence.len(), 2, "expected two concrete evidence records");
        assert_ne!(evidence[0].0, evidence[1].0, "rows must remain distinct");
        assert_ne!(
            evidence[0].1, evidence[1].1,
            "each row must publish its own witness"
        );
        assert!(
            t.phase
                .program
                .types()
                .member_resolutions
                .values()
                .all(|resolution| !matches!(
                    resolution,
                    crate::types::output::MemberResolution::ViaRequirement { .. }
                ))
        );
    }

    #[test]
    fn self_parameter_equality_refines_the_instance_head() {
        let t = check(
            "// no-core\nprotocol P { func get() -> Int }\nstruct Box<Element> { let value: Element }\nextend Box: P where Self.Element == Int { func get() -> Int { self.value } }\nlet value = Box(value: 1).get()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "value"), "Int");
    }

    #[test]
    fn concrete_inherent_extension_is_not_visible_on_other_arguments() {
        let t = check(
            "// no-core\nstruct Box<Element> { let value: Element }\nextend Box<Int> { func intValue() -> Int { self.value } }\nlet value = Box(value: true).intValue()",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("Unknown member")),
            "expected an unavailable-member error, got {errors:?}"
        );
    }

    #[test]
    fn disjoint_inherent_extensions_coexist() {
        let t = check(
            "// no-core\nstruct Box<Element> { let value: Element }\nextend Box<Int> { func get() -> Int { 1 } }\nextend Box<Bool> { func get() -> Int { 2 } }\nlet a = Box(value: 1).get()\nlet b = Box(value: true).get()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "a"), "Int");
        assert_eq!(ty_of(&t, "b"), "Int");
    }

    #[test]
    fn overlapping_inherent_members_are_rejected() {
        let t = check(
            "// no-core\nstruct Box<Element> { let value: Element }\nextend<T> Box<T> { func get() -> Int { 1 } }\nextend Box<Int> { func get() -> Int { 2 } }\nlet a = Box(value: 1).get()",
        );
        let errors = type_errors(&t);
        assert!(
            !errors.is_empty(),
            "overlapping inherent definitions of one label must be rejected"
        );
    }

    #[test]
    fn contradictory_head_refinement_is_rejected() {
        let t = check(
            "// no-core\nprotocol P {}\nstruct Box<Element> { let value: Element }\nextend Box: P where Self.Element == Int && Self.Element == Bool {}",
        );
        let errors = type_errors(&t);
        assert!(
            !errors.is_empty(),
            "contradictory head refinement must be rejected"
        );
    }

    #[test]
    fn chained_head_equalities_unify_transitively() {
        // `Self.A == Self.B && Self.A == Int` solves to A = B = Int; the
        // shared solution is not a contradiction, in either predicate order.
        let t = check(
            "// no-core\nprotocol P { func get() -> Int }\nstruct Pair<A, B> { let a: A\n\tlet b: B }\nextend Pair: P where Self.A == Self.B && Self.A == Int { func get() -> Int { self.a } }\nlet value = Pair(a: 1, b: 2).get()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "value"), "Int");

        let flipped = check(
            "// no-core\nprotocol P { func get() -> Int }\nstruct Pair<A, B> { let a: A\n\tlet b: B }\nextend Pair: P where Self.A == Int && Self.A == Self.B { func get() -> Int { self.a } }\nlet value = Pair(a: 1, b: 2).get()",
        );
        assert_clean(&flipped);
        assert_eq!(ty_of(&flipped, "value"), "Int");
    }

    #[test]
    fn omitted_head_arguments_must_be_a_defaulted_suffix() {
        // `Weird<A = Int, B>`: omitting the SUFFIX means omitting required
        // B, which no default fills — an arity error, not an unusable row.
        let t = check(
            "// no-core\nprotocol P {}\nstruct Weird<A = Int, B> { let a: A\n\tlet b: B }\nextend Weird<Bool>: P {}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("arity") || e.contains("argument")),
            "omitting a non-defaulted suffix parameter must be an arity error, got {errors:?}"
        );
    }

    #[test]
    fn underapplied_extension_head_is_an_arity_error() {
        let t = check(
            "// no-core\nprotocol P {}\nstruct Pair<A, B> { let a: A\n\tlet b: B }\nextend<T> Pair<T>: P {}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("arity") || e.contains("argument")),
            "underapplied head must be an arity error, got {errors:?}"
        );
    }

    #[test]
    fn overapplied_extension_head_is_an_arity_error() {
        let t = check(
            "// no-core\nprotocol P {}\nstruct Pair<A, B> { let a: A\n\tlet b: B }\nextend Pair<Int, Bool, Int>: P {}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("arity") || e.contains("argument")),
            "overapplied head must be an arity error, got {errors:?}"
        );
    }

    #[test]
    fn declaration_where_conformance_and_same_type_are_scheme_predicates() {
        let t = check(
            "// no-core\nprotocol Boxy {\n\tassociated Item\n\tfunc item() -> Item\n}\nstruct S {}\nextend S: Boxy {\n\tfunc item() -> Int { 1 }\n}\nfunc intItem<T>(x: T) -> Int where T: Boxy && T.Item == Int {\n\tx.item()\n}\nlet y = intItem(x: S())",
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
    fn extension_method_parameters_borrow_by_default() {
        let t = check(
            "// no-core\nstruct Wrap {\n\tlet value: Int\n}\nstruct Token {}\nextend Wrap {\n\tfunc poke(borrow t: Token) -> Int {\n\t\tself.value\n\t}\n}\nfunc caller(w: Wrap, t: Token) -> Int {\n\tw.poke(t: t)\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn unadorned_parameters_borrow_by_default() {
        let t = check(
            "// no-core\nstruct Counter {\n\tlet count: Int\n}\nfunc read(c: Counter) -> Int {\n\tc.count\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "read"), "(&Counter) -> Int");
    }

    #[test]
    fn unadorned_init_parameters_consume_by_default() {
        // An explicit init that stores its argument: legal without `consume`
        // because init params default to consuming (ADR 0018).
        let t = check(
            "// no-core\nstruct Name {}\nstruct User {\n\tlet name: Name\n\n\tinit(name: Name) {\n\t\tself.name = name\n\t}\n}\nlet u = User(name: Name())",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "u"), "User");
    }

    #[test]
    fn unadorned_function_type_parameters_borrow_by_default() {
        let t = check(
            "// no-core\nstruct Entry {}\nfunc walk(fn: (Entry) -> ()) {}\nfunc visit(entry: Entry) {}\nwalk(fn: visit)",
        );
        assert_clean(&t);
        // The `fn` parameter is itself unadorned, so it is a borrowed
        // function value; its own parameters borrow too.
        assert_eq!(ty_of(&t, "walk"), "(&(&Entry) -> ()) -> ()");
    }

    #[test]
    fn callback_result_donates_owned_from_borrowed_param() {
        // Implicit sharing: the callback's borrowed parameter satisfies
        // the owned result slot by donating a retain.
        let t = check(
            "// no-core\nstruct Character {}\nfunc apply(transform: (Character) -> Character) {}\napply { ch in ch }",
        );
        assert_clean(&t);
    }

    #[test]
    fn borrowed_function_values_are_callable() {
        // A borrowed parameter of function type can be called: invoking a
        // function value is a read.
        let t =
            check("// no-core\nstruct Entry {}\nfunc walk(fn: (Entry) -> ()) {\n\tfn(Entry())\n}");
        assert_clean(&t);
    }

    #[test]
    fn explicit_parameter_modes_lower_to_borrow_types() {
        let t = check(
            "// no-core\nstruct Counter {\n\tlet count: Int\n}\nfunc read(borrow c: Counter) -> Int {\n\tc.count\n}\nfunc write(mut c: Counter) -> Int {\n\tc.count\n}\nfunc take(consume c: Counter) -> Counter {\n\tc\n}\nfunc take_mut(consume mut c: Counter) -> Counter {\n\tc\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "read"), "(&Counter) -> Int");
        assert_eq!(ty_of(&t, "write"), "(&mut Counter) -> Int");
        assert_eq!(ty_of(&t, "take"), "(Counter) -> Counter");
        assert_eq!(ty_of(&t, "take_mut"), "(Counter) -> Counter");
    }

    #[test]
    fn explicit_parameter_modes_apply_in_protocol_requirements() {
        let t = check(
            "// no-core\npublic protocol Levelled {\n\tfunc level(borrow rhs: Self) -> Self\n\tfunc absorb(consume rhs: Self) -> Self\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn mut_mode_on_borrow_annotation_is_a_declaration_site_conflict() {
        // `func bump(mut c: &Counter)` used to silently drop the `mut`,
        // leaving the user with contradictory downstream diagnostics.
        let t = check(
            "// no-core\nstruct Counter {\n\tlet count: Int\n}\nfunc bump(mut c: &Counter) {\n\tc.count\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("mut") && e.contains("already a borrow")),
            "expected a declaration-site mode/borrow conflict, got: {errors:?}"
        );
    }

    #[test]
    fn consume_mode_on_borrow_annotation_is_a_declaration_site_conflict() {
        let t = check(
            "// no-core\nstruct Counter {\n\tlet count: Int\n}\nfunc eat(consume c: &Counter) {\n\tc.count\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("consume") && e.contains("already a borrow")),
            "expected a declaration-site mode/borrow conflict, got: {errors:?}"
        );
    }

    #[test]
    fn modeless_borrow_annotation_stays_legal() {
        // A bare `&T` annotation is the explicit spelling of the borrow
        // default — no mode keyword, no conflict.
        let t = check(
            "// no-core\nstruct Counter {\n\tlet count: Int\n}\nfunc read(c: &Counter) -> Int {\n\tc.count\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "read"), "(&Counter) -> Int");
    }

    #[test]
    fn inferred_parameters_borrow_by_default() {
        // Ownership plan 3.3(b): an unannotated param's solved type honors
        // its stamped `Borrow` mode — `func peek(x)` with `x` solving to
        // Counter is `func peek(x: Counter)`'s twin (a shared borrow), so
        // the caller keeps ownership and can reuse the argument.
        let t = check(
            "// no-core\nstruct Counter {\n\tlet count: Int\n}\nfunc peek(x) -> Int {\n\tx.count\n}\nlet c = Counter(count: 3)\nlet n = peek(c)\nlet m = peek(c)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "n"), "Int");
        assert_eq!(ty_of(&t, "m"), "Int");
    }

    #[test]
    fn inferred_param_scheme_matches_annotated_generic_twin() {
        // The coherence anchor: `func id(x) { x }` must end up semantically
        // identical to `func id<T>(x: T) { x }` under borrow-by-default —
        // borrow in, borrow-derived value out.
        let inferred = check("// no-core\nfunc id(x) { x }");
        assert_clean(&inferred);
        let annotated = check("// no-core\nfunc idg<T>(x: T) { x }");
        assert_clean(&annotated);
        assert_eq!(ty_of(&inferred, "id"), "<T0>(&T0) -> &T0");
        assert_eq!(ty_of(&annotated, "idg"), "<T0>(&T0) -> &T0");
    }

    #[test]
    fn inferred_consume_param_stays_owned() {
        // The stamped mode is the authority: an explicit `consume` on an
        // unannotated param keeps today's owned-parameter typing.
        let t = check(
            "// no-core\nstruct S {}\nfunc eat(consume x) -> Int {\n\t0\n}\nlet s = S()\nlet n = eat(x: s)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "eat"), "<T0>(T0) -> Int");
    }

    #[test]
    fn arithmetic_on_inferred_params_solves_at_int() {
        // Copy erasure must stay decidable for inferred borrow params:
        // `&?a` meeting Int erases to Int (the annotated twin's param never
        // wraps a Copy head at all).
        let t = check("func add(a, b) {\n\ta + b\n}\nlet r: Int = add(a: 1, b: 2)");
        assert_clean(&t);
    }

    #[test]
    fn inferred_param_returned_owned_donates_and_stays_borrowed() {
        // Implicit sharing: a borrowed parameter returned as an owned
        // value donates a retain at the return — and the donation happens
        // at the boundary, so the param's inferred type stays a borrow
        // rather than defaulting to owned.
        let t = check(
            "// no-core\nstruct Str {}\nfunc steal(x) -> Str {\n\tx\n}\nlet s = Str()\nlet y = steal(x: s)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "steal"), "(&Str) -> Str");
    }

    #[test]
    fn inferred_param_member_access_defaults_like_annotated() {
        // With no caller constraining `x`, the member predicate rides the
        // scheme and the final solve resolves it exactly as the owned
        // inference used to — but through a borrowed receiver.
        let t = check(
            "// no-core\nstruct Counter {\n\tlet count: Int\n}\nfunc peek(x) -> Int {\n\tx.count\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn legacy_borrow_annotation_in_init_position_stays_legal() {
        // `init` params are stamped `consume` by desugaring; a modeless
        // legacy `&T` annotation there means "borrow" (ADR 0018 migration
        // table) and must not report a conflict the user never wrote.
        let t = check(
            "// no-core\nstruct Counter {\n\tlet count: Int\n}\nstruct Reader {\n\tlet total: Int\n\tinit(c: &Counter) {\n\t\tself.total = c.count\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn borrow_parameters_auto_borrow_owned_arguments() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc len(s: &String) -> Int {\n\ts.length\n}\nlet s = String(length: 4)\nlet y = len(s: s)\nlet z = s.length",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "len"), "(&String) -> Int");
        assert_eq!(ty_of(&t, "y"), "Int");
        assert_eq!(ty_of(&t, "z"), "Int");
    }

    #[test]
    fn auto_borrow_does_not_overwrite_argument_node_type() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc len(s: &String) -> Int {\n\t0\n}\nlet s = String(length: 4)\nlet y = len(s: s)",
        );
        assert_clean(&t);
        let borrowed_exprs: Vec<_> = t
            .phase
            .program
            .types()
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
    fn delayed_auto_borrow_keeps_inferred_param_borrowed() {
        // Plan 3.3(b) redefinition of the old owned-default: an inferred
        // param is a borrow, so feeding it to a borrow slot solves its
        // payload without any owned defaulting — `f` borrows exactly like
        // its annotated twin `func f(x: S)`.
        let t = check("// no-core\nstruct S {}\nfunc take(s: &S) {}\nfunc f(x) {\n\ttake(s: x)\n}");
        assert_clean(&t);
        assert_eq!(ty_of(&t, "f"), "(&S) -> ()");
        // And the old test program — which then returns `x` as an owned
        // `S` — donates at the return while the param stays borrowed,
        // exactly like its annotated twin would.
        let t = check(
            "// no-core\nstruct S {}\nfunc take(s: &S) {}\nfunc f(x) -> S {\n\ttake(s: x)\n\tx\n}",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "f"), "(&S) -> S");
    }

    #[test]
    fn borrowed_return_donates_into_owned_argument() {
        // Implicit sharing: a borrowed call result fills a consume
        // parameter by donating a retain; the owner keeps its value.
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc id(s: &String) -> &String {\n\ts\n}\nfunc take(consume s: String) -> Int {\n\ts.length\n}\nlet s = String(length: 4)\nlet y = take(s: id(s: s))",
        );
        assert_clean(&t);
    }

    /// S4: a borrow annotation is not an application — an owned rvalue temp
    /// (a call result) must not satisfy `let x: &T = ...`; the temp would be
    /// dropped at statement end while the alias lives on.
    #[test]
    fn borrow_annotation_rejects_owned_call_rvalue() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc mk() -> String {\n\tString(length: 4)\n}\nfunc use_it() -> Int {\n\tlet x: &String = mk()\n\tx.length\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("String") && error.contains("&String")),
            "expected owned rvalue to be rejected by a borrow annotation, got {errors:?}"
        );
    }

    /// S4, with the core prelude: `String` is CheapClone, but a borrow
    /// annotation still demands a genuine borrow — CheapClone coercion is an
    /// application-site (`Apply`) rule only.
    #[test]
    fn borrow_annotation_rejects_owned_call_rvalue_with_core_string() {
        let t = Driver::new(
            vec![Source::from(
                "func mk() -> String {\n\t\"temp\" + \" heap string\"\n}\nfunc use_it() -> Int {\n\tlet x: &String = mk()\n\tx.byte_count\n}\nuse_it()",
            )],
            DriverConfig::new("TypesTest"),
        )
        .parse()
        .expect("parse failed")
        .resolve_names()
        .expect("name resolution failed")
        .type_check();
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("String") && error.contains("&String")),
            "expected owned rvalue to be rejected by a borrow annotation, got {errors:?}"
        );
    }

    /// S4 guard: annotating a borrow of a local place is the legitimate
    /// borrow-introduction form and stays accepted.
    #[test]
    fn borrow_annotation_still_borrows_local_place() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc use_it() -> Int {\n\tlet s = String(length: 4)\n\tlet x: &String = s\n\tx.length\n}",
        );
        assert_clean(&t);
    }

    /// S4 guard: a field of a local place is a place too.
    #[test]
    fn borrow_annotation_still_borrows_field_place() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nstruct Box {\n\tlet value: String\n}\nfunc use_it() -> Int {\n\tlet b = Box(value: String(length: 4))\n\tlet x: &String = b.value\n\tx.length\n}",
        );
        assert_clean(&t);
    }

    /// S4 guard: a borrow-returning call still satisfies a borrow annotation
    /// (the found type is a genuine borrow; no peel involved).
    #[test]
    fn borrow_annotation_accepts_borrow_returning_call() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc id(s: &String) -> &String {\n\ts\n}\nfunc use_it() -> Int {\n\tlet s = String(length: 4)\n\tlet x: &String = id(s: s)\n\tx.length\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn nested_borrow_donates_into_owned_field() {
        // Implicit sharing: a borrowed value stored into an owning field
        // donates a retain at the construction boundary (MIR's stored
        // slots already consume with donation).
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nstruct Box<T> {\n\tlet value: T\n}\nfunc id(s: &String) -> &String {\n\ts\n}\nfunc take(b: Box<String>) -> Int {\n\tb.value.length\n}\nlet s = String(length: 4)\nlet b = Box(value: id(s: s))\nlet y = take(b: b)",
        );
        assert_clean(&t);
    }

    #[test]
    fn function_return_borrow_does_not_satisfy_owned_function_argument() {
        let t = check(
            "// no-core\nstruct String {\n\tlet length: Int\n}\nlet s = String(length: 4)\nlet f: () -> &String = func() { s }\nfunc take(f: () -> String) -> String {\n\tf()\n}\nlet y = take(f: f)",
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
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc needs_mut(s: &mut String) -> Int {\n\ts.length\n}\nfunc take(f: (&String) -> Int) -> Int {\n\t0\n}\nlet y = take(f: needs_mut)",
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
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc needs_owned(consume s: String) -> Int {\n\ts.length\n}\nfunc take(f: (&String) -> Int) -> Int {\n\t0\n}\nlet y = take(f: needs_owned)",
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
    fn unknown_member_on_nested_borrow_reports_collapsed_receiver() {
        // & of & is & (ADR 0015 addendum): a nested borrow annotation IS
        // a single borrow, and diagnostics render the canonical type.
        let t = check(
            "// no-core\nstruct DirectoryEntry {}\nfunc f(entry: & &DirectoryEntry) {\n\tentry.show()\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Unknown member 'show' on &DirectoryEntry")),
            "expected the collapsed borrow receiver in the diagnostic, got {errors:?}"
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
    fn leading_dot_borrow_payload_defers_associated_type_projection() {
        let t = check(
            "struct Node {\n\tlet value: Int\n}\nstruct Ast {\n\tlet roots: [Node]\n}\nenum ParseError {}\nfunc parse() -> Result<&Node, ParseError> {\n\tlet ast = Ast(roots: [])\n\tlet first = ast.roots[0]\n\t.ok(first)\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn leading_dot_resolves_in_inference_position() {
        // The callee's parameter type is a fresh variable when the argument
        // is checked, so the leading dot cannot resolve eagerly — the enum
        // arrives later, through the result unification.
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc id<T>(consume x: T) -> T { x }\nlet y: Opt<Int> = id(x: .some(1))",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "y"), "Opt<Int>");
    }

    #[test]
    fn bare_leading_dot_resolves_in_inference_position() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc id<T>(consume x: T) -> T { x }\nlet y: Opt<Int> = id(x: .none)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "y"), "Opt<Int>");
    }

    #[test]
    fn bare_variant_name_is_rejected_before_lowering() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n\n\tfunc fallback() -> Self {\n\t\tmatch self {\n\t\t\t.some(_) -> .none,\n\t\t\t.none -> none\n\t\t}\n\t}\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| {
                error.contains("Enum case `none` cannot be used as a bare name")
                    && error.contains("`.none`")
            }),
            "expected an actionable bare-variant diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn bare_payload_variant_call_is_rejected_before_lowering() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\n\tfunc wrap(value: T) -> Self { some(value) }\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Enum case `some` cannot be used as a bare name")),
            "expected an actionable bare-variant diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn nested_leading_dots_resolve_in_inference_position() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc id<T>(consume x: T) -> T { x }\nlet y: Opt<Opt<Int>> = id(x: .some(.some(1)))",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "y"), "Opt<Opt<Int>>");
    }

    #[test]
    fn inferred_leading_dot_unknown_variant_errors() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc id<T>(consume x: T) -> T { x }\nlet y: Opt<Int> = id(x: .nope)",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("nope")),
            "expected unknown-variant error, got {errors:?}"
        );
    }

    #[test]
    fn inferred_leading_dot_arity_mismatch_errors() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc id<T>(consume x: T) -> T { x }\nlet y: Opt<Int> = id(x: .some(1, 2))",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Wrong number of arguments")),
            "expected arity mismatch error, got {errors:?}"
        );
    }

    #[test]
    fn leading_dot_without_context_errors() {
        // Nothing ever determines the enum: the program is ambiguous.
        let t = check("// no-core\nenum Color {\n\tcase red\n\tcase green\n}\nlet x = .red");
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("red")),
            "expected an unresolved leading-dot error naming the variant, got {errors:?}"
        );
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
            "// no-core\nstruct String {\n\tlet length: Int\n}\nfunc takes_mut(s: &mut String) -> Int {\n\ts.length\n}\nfunc bad(s: &String) -> Int {\n\ttakes_mut(s: s)\n}",
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
    fn mut_method_receiver_can_assign_self_field() {
        let t = check(
            "// no-core\nstruct Counter {\n\tlet n: Int\n\n\tmut func bump() -> () {\n\t\tself.n = 2\n\t\t()\n\t}\n}",
        );
        assert!(t.diagnostics().is_empty(), "{:?}", t.diagnostics());
    }

    // ----- Milestone 5: effects -----------------------------------------

    #[test]
    fn inline_ir_arithmetic_on_an_unsupported_scalar_is_rejected() {
        let t = check(
            "// no-core\nfunc bad() -> Bool {\n\t@unsafe { @_ir { %? = add Bool true false } }\n}",
        );
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("inline IR arithmetic on")),
            "expected the checker to reject non-numeric IR arithmetic: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn inline_ir_comparison_on_an_unsupported_scalar_is_rejected() {
        let t = check(
            "// no-core\nstruct S {\n\tlet n: Int\n}\nfunc bad() -> Bool {\n\t@unsafe { @_ir { %? = cmp S 1 < 2 } }\n}",
        );
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("inline IR comparisons on")),
            "expected the checker to reject the comparison scalar: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn inline_ir_infers_the_intrinsic_unsafe_effect() {
        let t = check("// no-core\nfunc raw() -> Int {\n\t@_ir { %? = add Int 1 2 }\n}");
        assert_clean(&t);
        let raw = ty_of(&t, "raw");
        assert!(
            raw.contains("'unsafe"),
            "inline IR should add the intrinsic effect: {raw}"
        );
    }

    #[test]
    fn unsafe_block_masks_the_intrinsic_effect() {
        let t = check(
            "// no-core\nfunc safe() -> Int {\n\t@unsafe { @_ir { %? = add Int 1 2 } }\n}\nlet value = safe()",
        );
        assert_clean(&t);
        let safe = ty_of(&t, "safe");
        assert!(
            !safe.contains("'unsafe"),
            "the lexical boundary should discharge the effect: {safe}"
        );
    }

    #[test]
    fn unsafe_file_comment_no_longer_grants_authority() {
        let t =
            check("// no-core\n// unsafe\nlet pointer: RawPtr = __IR(\"$? = alloc int 1\")\n()");
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("No handler for 'unsafe")),
            "the legacy file comment must not bypass the effect: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn raw_pointer_escaping_an_unsafe_block_needs_outer_authority() {
        // The wrapper's own type is checked in the outer context: a RawPtr
        // cannot escape merely by being the block's result.
        let t =
            check("// no-core\nlet pointer: RawPtr = @unsafe { __IR(\"$? = alloc int 1\") }\n()");
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("No handler for 'unsafe")),
            "a RawPtr result must not escape the unsafe block: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn nested_func_does_not_inherit_lexical_unsafe_authority() {
        // The mask covers calls made inside the block, not the bodies of
        // nested function literals: their `'unsafe` stays in the scheme, so
        // an escaped function still demands authority at its call site.
        let t = check(
            "// no-core\nlet f = @unsafe {\n\tfunc inner() -> Int {\n\t\t@_ir { %? = add Int 1 2 }\n\t}\n\tinner\n}\nlet n = f()\n()",
        );
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("No handler for 'unsafe")),
            "calling the escaped function outside the block must fail: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn intrinsic_unsafe_cannot_be_performed_or_handled() {
        let performed = check("// no-core\nfunc bad() { 'unsafe() }");
        assert!(
            type_errors(&performed)
                .iter()
                .any(|error| error.contains("cannot be performed")),
            "expected an intrinsic-effect diagnostic: {:?}",
            type_errors(&performed)
        );

        let handled = check("// no-core\n@handle 'unsafe { () }");
        assert!(
            type_errors(&handled)
                .iter()
                .any(|error| error.contains("cannot be handled")),
            "expected an intrinsic-effect diagnostic: {:?}",
            type_errors(&handled)
        );
    }

    #[test]
    fn performed_effects_stay_in_the_row_until_a_handler_extent() {
        // Dynamic-extent semantics: a perform always joins the function's
        // latent row; discharge happens where a call meets a handler's
        // extent (here, the prescanned top-level `@handle`), not at the
        // perform site.
        let t = check(
            "// no-core\neffect 'oops(e) -> Never\n@handle 'oops { e in 0 }\nfunc safe() {\n\t'oops(e: 1)\n\t2\n}\nsafe()",
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
            "// no-core\neffect 'oops(e) -> Never\n@handle 'oops { e in 0 }\nfunc safe() {\n\t'oops(e: 1)\n\t2\n}\nfunc outer() {\n\tsafe()\n}\nouter()",
        );
        assert_clean(&t);
        let safe = ty_of(&t, "safe");
        assert!(safe.contains("'oops"), "safe performs 'oops: {safe}");
        let outer = ty_of(&t, "outer");
        assert!(
            outer.contains("'oops"),
            "outer's row inherits the callee's unhandled effect: {outer}"
        );
        let types = &t.phase.program.types();
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
        let t = check(
            "// no-core\neffect 'state<T>(value: T) -> T\nfunc f() {\n\t'state(value: 42)\n\t()\n}",
        );
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
            "// no-core\neffect 'state<T>(value: T) -> T\nfunc f() {\n\t'state(value: 42)\n\t'state(value: true)\n\t()\n}",
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
            "// no-core\neffect 'throw(ret) -> ()\nfunc this_is_fine() {\n\t@handle 'throw { err in () }\n\tthis_is_not_fine()\n}\nfunc this_is_not_fine() {\n\t'throw(ret: 1)\n\t()\n}\nthis_is_fine()",
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
    fn compound_if_conditions_scope_pattern_binders_left_to_right() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc next(x: Int) -> Opt<Int> { .some(x) }\nfunc allowed(x: Int) -> Bool { true }\nfunc f(first: Opt<Int>) -> Int {\n\tif let .some(x) = first, let .some(y) = next(x: x), allowed(x: y) {\n\t\treturn y\n\t}\n\t0\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn compound_if_expression_checks_all_branches() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc allowed(x: Int) -> Bool { true }\nfunc f(value: Opt<Int>) -> Int {\n\tif let .some(x) = value, allowed(x: x) { x } else { 0 }\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn compound_if_requires_boolean_expression_clauses() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc f(value: Opt<Int>) {\n\tif let .some(x) = value, x { () }\n}",
        );
        assert!(!type_errors(&t).is_empty());
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
            "// no-core\nstruct A {\n\tfunc go() -> Int { 1 }\n}\nstruct C {}\nfunc call_go(x) {\n\tx.go()\n}\ncall_go(x: C())",
        );
        assert!(
            !type_errors(&t).is_empty(),
            "C has no go(): the discharged constraint must error"
        );
    }

    #[test]
    fn generic_methods_instantiate_per_call() {
        let t = check(
            "// no-core\nstruct Person {\n\tfunc getAge<T>(consume t: T) -> T { t }\n}\nPerson().getAge(t: 123)\nPerson().getAge(t: 1.23)",
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
        let t = check(
            "// no-core\nfunc fstA(r) { r.a }\n(fstA(r: { a: 1 }), fstA(r: { a: 2, b: true }))",
        );
        assert_clean(&t);

        let t = check(
            "// no-core\nfunc foo(x) {\n\t(x.y, x.z)\n}\nfoo(x: { y: 123, z: 1.23 })\nfoo(x: { y: 123, z: 123 })",
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
            "// no-core\neffect 'state<T>(value: T) -> T\n@handle 'state { v in\n\t'continue v\n}\n'state<Int>(value: 42)",
        );
        assert_clean(&t);
    }

    #[test]
    fn generic_effect_call_inferred() {
        let t = check(
            "// no-core\neffect 'state<T>(value: T) -> T\n@handle 'state { v in\n\t'continue v\n}\n'state(value: 42)",
        );
        assert_clean(&t);
    }

    #[test]
    fn generic_effect_type_mismatch() {
        let t = check(
            "// no-core\neffect 'state<T>(value: T) -> T\n@handle 'state { v in\n\t'continue v\n}\n'state<Int>(value: true)",
        );
        assert!(
            !type_errors(&t).is_empty(),
            "passing a Bool for an Int-instantiated effect must error"
        );
    }

    #[test]
    fn generic_effect_multiple_params() {
        let t = check(
            "// no-core\neffect 'pair<A, B>(first: A, second: B) -> (A, B)\n@handle 'pair { a, b in\n\t'continue (a, b)\n}\n'pair<Int, Bool>(first: 42, second: true)",
        );
        assert_clean(&t);
    }

    #[test]
    fn continue_payload_checks_against_the_effect_return() {
        // `'continue v` resumes the perform: v must have the effect's
        // declared return type.
        let t = check(
            "// no-core\neffect 'ask(p: Int) -> Int\n@handle 'ask { p in\n\t'continue true\n}\n'ask(p: 1)",
        );
        let errors = type_errors(&t);
        assert!(
            !errors.is_empty(),
            "expected a type error for 'continue true"
        );
    }

    #[test]
    fn continue_payload_outside_a_handler_is_rejected() {
        let t = check("// no-core\nfunc f() -> Int {\n\tloop true {\n\t\t'continue 5\n\t}\n\t0\n}");
        let errors = type_errors(&t);
        assert!(
            !errors.is_empty(),
            "expected an error for continue-with-value outside a handler"
        );
    }

    #[test]
    fn protocol_head_deinit_conformances_are_rejected() {
        // Deinit commits per family head (ADR 0038): drop sites
        // dereference the head's published rows, so a hook reaching a
        // family only through a protocol has no home. Core is needed —
        // `Deinit`'s identity is the well-known core protocol.
        let t = Driver::new(
            vec![Source::from(
                "protocol Marker {}\nextend Marker: Deinit {\n\tconsuming func deinit() -> Void { () }\n}",
            )],
            DriverConfig::new("TypesTest"),
        )
        .parse()
        .expect("parse failed")
        .resolve_names()
        .expect("name resolution failed")
        .type_check();
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("`Deinit` conformances on a protocol head")),
            "expected the protocol-head Deinit row to be rejected: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn conformance_rows_commit_ordered_dictionaries() {
        // Row completion (ADR 0038): every conformance row carries one
        // committed entry per protocol requirement, in declaration
        // order — the declared witness, or the protocol's default body.
        // Lowering dereferences entries; it never selects by name.
        use crate::name_resolution::symbol::Symbol;
        use crate::types::catalog::DictionaryEntry;
        let t = check(
            "// no-core\nprotocol Greet {\n\tfunc hello() -> Int\n\tfunc again() -> Int {\n\t\tself.hello()\n\t}\n}\nextend Int: Greet {\n\tfunc hello() -> Int { 1 }\n}",
        );
        assert_clean(&t);
        let catalog = &t.phase.program.types().catalog;
        let row = catalog
            .conformances
            .values()
            .find(|row| row.head == Symbol::Int)
            .expect("the Int: Greet row exists");
        let hello = *row
            .witnesses
            .get("hello")
            .expect("the declared witness is recorded");
        let info = catalog
            .protocols
            .values()
            .next()
            .expect("the protocol is collected");
        let again = info
            .requirements
            .get("again")
            .and_then(|set| set.first())
            .expect("the defaulted requirement is registered")
            .symbol;
        assert_eq!(
            row.dictionary,
            vec![
                DictionaryEntry::Implementation {
                    symbol: hello,
                    writeback_width: 0,
                },
                DictionaryEntry::Implementation {
                    symbol: again,
                    writeback_width: 0,
                },
            ]
        );
    }

    #[test]
    fn committed_dictionary_entries_carry_writeback_widths() {
        // A `mut func` requirement's receiver is an exclusive borrow, so
        // every implementation returns `(result, final self)`; the
        // committed entry carries that declared width so lowering never
        // rescans schemes for it.
        use crate::name_resolution::symbol::Symbol;
        use crate::types::catalog::DictionaryEntry;
        let t = check(
            "// no-core\nprotocol Bump {\n\tmut func bump() -> Void\n}\nextend Int: Bump {\n\tmut func bump() -> Void { () }\n}",
        );
        assert_clean(&t);
        let catalog = &t.phase.program.types().catalog;
        let row = catalog
            .conformances
            .values()
            .find(|row| row.head == Symbol::Int)
            .expect("the Int: Bump row exists");
        let bump = *row
            .witnesses
            .get("bump")
            .expect("the declared witness is recorded");
        assert_eq!(
            row.dictionary,
            vec![DictionaryEntry::Implementation {
                symbol: bump,
                writeback_width: 1,
            }]
        );
        // The declared receiver mode is a committed requirement fact
        // too — lowering reads it, never rescans schemes.
        let info = catalog
            .protocols
            .values()
            .next()
            .expect("the protocol is collected");
        assert!(info.requirements["bump"][0].mut_receiver);
    }

    #[test]
    fn derived_conformances_are_synthesized_rows_with_recipe_dictionaries() {
        // Derivation materializes an ordinary conformance row per
        // derivable protocol (the derive-generates-an-impl model); its
        // committed dictionary carries the structural recipe for bodyless
        // requirements and the default body for defaulted ones.
        use crate::name_resolution::symbol::Symbol;
        use crate::types::catalog::{DerivedRecipe, DictionaryEntry};
        let t = Driver::new(
            vec![Source::from("struct Point {\n\tlet x: Int\n}\n")],
            DriverConfig::new("TypesTest"),
        )
        .parse()
        .expect("parse failed")
        .resolve_names()
        .expect("name resolution failed")
        .type_check();
        assert_clean(&t);
        let catalog = &t.phase.program.types().catalog;
        let point = catalog
            .structs
            .keys()
            .copied()
            .find(|symbol| {
                t.phase
                    .program
                    .resolved_names()
                    .symbol_names
                    .get(symbol)
                    .is_some_and(|name| name == "Point")
            })
            .expect("Point registered");
        let row_for = |protocol: Symbol| {
            catalog
                .conformances_for_head(point)
                .map(|(_, row)| row)
                .find(|row| row.protocol.protocol == protocol)
                .expect("synthesized row exists")
        };
        let show = row_for(Symbol::Showable);
        assert!(show.synthesized);
        assert_eq!(
            show.dictionary,
            vec![DictionaryEntry::Derived(DerivedRecipe::Show)]
        );
        let equatable = row_for(Symbol::Equatable);
        assert!(equatable.synthesized);
        assert_eq!(
            equatable.dictionary[0],
            DictionaryEntry::Derived(DerivedRecipe::Equality)
        );
        assert!(
            matches!(
                equatable.dictionary[1],
                DictionaryEntry::Implementation {
                    writeback_width: 0,
                    ..
                }
            ),
            "notEquals uses its default body: {:?}",
            equatable.dictionary
        );
        assert_eq!(equatable.dictionary.len(), 2);
    }

    #[test]
    fn catalog_commits_callable_owner_bindings() {
        // The owner-binding index (ADR 0038): check-mode compilation
        // binds a member body's owner parameters from a committed
        // symbol-keyed index, never by scanning every catalog's
        // structs/enums/extends/protocols per query.
        use crate::types::catalog::OwnerBinding;
        let t = check(
            "// no-core\nstruct Holder<T> {\n\tlet v: T\n\tfunc get() -> T { self.v }\n}\nenum Flag {\n\tcase up\n\tfunc tag() -> Int { 0 }\n}\nextend<X> Holder<X> {\n\tfunc peek() -> X { self.get() }\n}\nprotocol P {\n\tfunc p() -> Int\n\tfunc q() -> Int { self.p() }\n}",
        );
        assert_clean(&t);
        let catalog = &t.phase.program.types().catalog;

        let (_, holder) = catalog.structs.iter().next().expect("Holder collected");
        let holder_params: Vec<_> = holder.params.iter().map(|param| param.symbol).collect();
        let get = holder.methods["get"][0];
        assert_eq!(
            catalog.callable_owners.get(&get),
            Some(&OwnerBinding::Nominal {
                params: holder_params
            })
        );

        let (_, flag) = catalog.enums.iter().next().expect("Flag collected");
        let tag = flag.methods["tag"][0];
        assert_eq!(
            catalog.callable_owners.get(&tag),
            Some(&OwnerBinding::Nominal { params: vec![] })
        );

        let row = catalog
            .extend_members
            .values()
            .flat_map(|members| members.get("peek"))
            .flatten()
            .next()
            .expect("inherent extend member collected");
        assert_eq!(
            catalog.callable_owners.get(&row.symbol),
            Some(&OwnerBinding::Nominal {
                params: row.params.clone()
            })
        );
        assert!(!row.params.is_empty(), "the extend row binds its own X");

        let (protocol, info) = catalog.protocols.iter().next().expect("P collected");
        let q = info.requirements["q"][0].symbol;
        assert_eq!(
            catalog.callable_owners.get(&q),
            Some(&OwnerBinding::Protocol(*protocol))
        );
    }

    #[test]
    fn typed_funcs_carry_receiver_and_binding_facts() {
        // Callable contract facts are baked on the typed Func node
        // (ADR 0038): the declared receiver mode, and the binding symbol
        // the top-level `let f = <func>` desugar aliases — lowering
        // reads them, it never re-recognizes declaration shapes.
        use crate::typed_ast::{DeclKind, ExprKind, Node, PatternKind};
        let t = check(
            "// no-core\nstruct S {\n\tlet v: Int\n\tmut func bump() -> Void { () }\n}\nfunc top() -> Int { 1 }",
        );
        assert_clean(&t);
        let (_, file) = t
            .phase
            .program
            .files()
            .iter()
            .next()
            .expect("one typed file");
        let mut saw_method = false;
        let mut saw_bound = false;
        for root in &file.roots {
            let Node::Decl(decl) = root else { continue };
            match &decl.kind {
                DeclKind::Struct { body, .. } => {
                    for member in &body.decls {
                        if let DeclKind::Method { func, .. } = &member.kind {
                            assert_eq!(func.receiver, crate::node_kinds::decl::ReceiverMode::Ref);
                            saw_method = true;
                        }
                    }
                }
                DeclKind::Let {
                    lhs,
                    rhs: Some(rhs),
                    ..
                } => {
                    let PatternKind::Bind(name) = &lhs.kind else {
                        continue;
                    };
                    let ExprKind::Func(func) = &rhs.kind else {
                        continue;
                    };
                    assert_eq!(func.bound_as, name.symbol().ok());
                    assert!(func.bound_as.is_some());
                    saw_bound = true;
                }
                _ => {}
            }
        }
        assert!(saw_method, "the struct method was built");
        assert!(saw_bound, "the top-level func desugar was built");
    }

    #[test]
    fn typed_program_files_come_in_initialization_order() {
        // LINK-02: a file's local imports initialize before it. Program
        // assembly publishes the order — `files()` iterates
        // dependency-first — so the backend never re-derives the import
        // graph from path stems.
        let t = Driver::new(
            vec![
                Source::in_memory(
                    "App.tlk".into(),
                    "use package::Lib::{ helper }\nlet a = helper()\n()",
                ),
                Source::in_memory("Lib.tlk".into(), "public func helper() -> Int { 1 }\n"),
            ],
            DriverConfig::new("TypesTest"),
        )
        .parse()
        .expect("parse failed")
        .resolve_names()
        .expect("name resolution failed")
        .type_check();
        assert_clean(&t);
        let order: Vec<String> = t
            .phase
            .program
            .files()
            .keys()
            .map(|source| source.path().to_string())
            .collect();
        assert_eq!(order, vec!["Lib.tlk".to_string(), "App.tlk".to_string()]);
    }

    #[test]
    fn copy_marker_requires_copy_or_cheap_clone_evidence() {
        // The `copy` marker is a checked clone: it demands Copy or
        // CheapClone evidence, not merely a value that happens to need no
        // runtime cleanup.
        let t = check(
            "// no-core\nstruct Sock {\n\tlet fd: Int\n}\nfunc eat(consume s: Sock) -> Int { 0 }\nlet s = Sock(fd: 1)\neat(s: copy s)\n()",
        );
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("Copy or CheapClone")),
            "expected missing copy evidence to be rejected: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn mut_marker_requires_an_exclusive_borrow_parameter() {
        let t = check(
            "// no-core\nfunc eat(consume n: Int) -> Int { n }\nlet x = 1\neat(n: mut x)\n()",
        );
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("`mut` marker requires a `mut` parameter")),
            "expected a marker/parameter mismatch: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn borrow_marker_requires_a_borrowing_parameter() {
        let t = check(
            "// no-core\nfunc eat(consume n: Int) -> Int { n }\nlet x = 1\neat(n: borrow x)\n()",
        );
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("`borrow` marker requires a borrowing parameter")),
            "expected a marker/parameter mismatch: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn mut_marker_on_a_mut_parameter_is_clean() {
        let t = check(
            "// no-core\nfunc set(mut n: Int) -> () {\n\tn = 2\n}\nlet x = 1\nset(n: mut x)\n()",
        );
        assert_clean(&t);
    }

    #[test]
    fn copy_marker_with_copy_evidence_is_clean() {
        let t = check(
            "// no-core\nfunc eat(consume n: Int) -> Int { n }\nlet n = 1\neat(n: copy n)\n()",
        );
        assert_clean(&t);
    }

    #[test]
    fn break_outside_a_loop_is_rejected() {
        let t = check("// no-core\nfunc f() -> () {\n\tbreak\n}");
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("`break` outside a loop")),
            "expected an error for break outside a loop: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn continue_outside_a_loop_is_rejected() {
        let t = check("// no-core\nfunc f() -> () {\n\tcontinue\n}");
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("`continue` outside a loop")),
            "expected an error for continue outside a loop: {:?}",
            type_errors(&t)
        );
    }

    #[test]
    fn break_in_a_nested_func_does_not_see_the_outer_loop() {
        // A function boundary resets loop context: the nested body cannot
        // break the loop it is lexically inside.
        let t = check(
            "// no-core\nfunc f() -> () {\n\tloop true {\n\t\tlet g = func() -> () {\n\t\t\tbreak\n\t\t}\n\t\tg()\n\t}\n}",
        );
        assert!(
            type_errors(&t)
                .iter()
                .any(|error| error.contains("`break` outside a loop")),
            "expected an error for break inside a nested function: {:?}",
            type_errors(&t)
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
    fn unreachable_is_a_never_valued_panic_effect() {
        let t = Driver::new(
            vec![Source::from("func impossible() -> Int {\n\tunreachable\n}")],
            DriverConfig::new("UnreachableEffect"),
        )
        .parse()
        .expect("parse failed")
        .resolve_names()
        .expect("name resolution failed")
        .type_check();
        assert_clean(&t);
        let types = t.phase.program.types();
        let resolved = t.phase.program.resolved_names();
        let impossible = resolved
            .symbol_names
            .iter()
            .find_map(|(symbol, name)| (name == "impossible").then_some(*symbol))
            .expect("impossible symbol");
        let _names = crate::name_resolution::symbol::set_symbol_names(types.display_names.clone());
        assert_eq!(types.schemes[&impossible].render(), "() -> Int ! <'panic>");
    }

    #[test]
    fn panic_can_be_handled_as_an_abortive_effect() {
        let t = Driver::new(
            vec![Source::from(
                "func recovered() -> Int {\n\t@handle 'panic { message in 42 }\n\tunreachable\n}",
            )],
            DriverConfig::new("HandledPanic"),
        )
        .parse()
        .expect("parse failed")
        .resolve_names()
        .expect("name resolution failed")
        .type_check();
        assert_clean(&t);
        assert_eq!(ty_of(&t, "recovered"), "() -> Int");
    }

    #[test]
    fn continue_payload_in_a_handler_checks_clean() {
        let t = check(
            "// no-core\neffect 'ask(p: Int) -> Int\n@handle 'ask { p in\n\t'continue p\n}\n'ask(p: 1)",
        );
        assert_clean(&t);
    }

    #[test]
    fn unhandled_effects_grow_the_latent_row() {
        let t =
            check("// no-core\neffect 'oops(e) -> Never\nfunc risky() {\n\t'oops(e: 1)\n\t2\n}");
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
    fn rejects_param_construction_without_an_init_bound() {
        let t = check("// no-core\nprotocol Marker {}\nfunc make<T: Marker>() -> T {\n\tT()\n}");
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("init requirement"), "{errors:?}");
    }

    #[test]
    fn param_construction_resolves_through_the_bound_requirement() {
        let t = check(
            "// no-core\nprotocol Makeable {\n\tinit(x: Int)\n}\nstruct Box {\n\tlet x: Int\n\tinit(x: Int) {\n\t\tself.x = x\n\t\tself\n\t}\n}\nextend Box: Makeable {}\nfunc make<T: Makeable>() -> T {\n\tT(x: 1)\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn closed_effect_annotation_accepts_declared_effects() {
        let t = check("// no-core\neffect 'a() -> ()\nfunc f() 'a -> () {\n\t'a()\n}");
        assert_clean(&t);
    }

    #[test]
    fn explicit_effect_annotation_is_the_published_contract() {
        let t = check("// no-core\neffect 'a() -> ()\nfunc f() 'a -> () {\n\t()\n}");
        assert_clean(&t);
        assert!(ty_of(&t, "f").contains("'a"), "{}", ty_of(&t, "f"));
    }

    #[test]
    fn effectful_function_type_annotation_accepts_declared_effects() {
        let t = check("// no-core\neffect 'a() -> ()\nlet f: () 'a -> () = func() {\n\t'a()\n}");
        assert_clean(&t);
    }

    #[test]
    fn effectful_function_type_annotation_rejects_extra_effects() {
        let t = check(
            "// no-core\neffect 'a() -> ()\neffect 'b() -> ()\nlet f: () 'a -> () = func() {\n\t'b()\n}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("'b"), "{errors:?}");
    }

    #[test]
    fn handler_parameters_infer_from_perform_sites() {
        // `effect 'oops(e)` has no annotation: the perform's argument and the
        // handler's parameter meet in the effect signature's shared
        // placeholder, so both get Int here.
        let t = check(
            "// no-core\neffect 'oops(e) -> Never\nfunc wants(i: Int) { i }\n@handle 'oops { e in wants(i: e) }\n'oops(e: 123)",
        );
        assert_clean(&t);
    }

    #[test]
    fn handler_parameter_type_conflicts_error() {
        let t = check(
            "// no-core\neffect 'oops(e) -> Never\nfunc wants(i: Int) { i }\n@handle 'oops { e in wants(i: e) }\n'oops(e: 1.5)",
        );
        assert_eq!(type_errors(&t).len(), 1, "{:?}", type_errors(&t));
    }

    // ----- Projection types (associated type synonyms) ------------------

    #[test]
    fn projections_reduce_at_concrete_instantiation() {
        // mk's return is the projection T.D (Chakravarty et al., ICFP 2005);
        // instantiating T at Int normalizes it through Int's conformance.
        let t = check(
            "// no-core\nprotocol Defaulted {\n\tassociated D\n\tfunc make() -> D\n}\nextend Int: Defaulted {\n\tfunc make() -> Bool { true }\n}\nfunc mk<T: Defaulted>(t: T) { t.make() }\nlet v = mk(t: 123)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "mk"), "<T0: Defaulted>(&T0) -> T0.D");
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
    fn protocol_argument_defaults_use_self_in_conformances_and_bounds() {
        let t = check(
            "// no-core\nprotocol Eq<RHS = Self> {\n\tfunc same(rhs: &RHS) -> Bool\n}\nextend Int: Eq {\n\tfunc same(rhs: &Int) -> Bool { true }\n}\nfunc uses<T: Eq>(x: T, y: &T) -> Bool {\n\tx.same(rhs: y)\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn overlapping_generic_protocol_argument_conformance_is_rejected() {
        let t = check(
            "// no-core\nstruct String {}\nstruct Name {}\nprotocol Into<Target> {\n\tfunc into() -> Target\n}\nprotocol Add<RHS> {\n\tassociated Ret\n\tfunc add(rhs: RHS) -> Ret\n}\nextend Name: Into<String> {\n\tfunc into() -> String { String() }\n}\nextend<T: Into<String>> String: Add<T> {\n\tfunc add(rhs other: T) -> String { other.into() }\n}\nextend String: Add<Name> {\n\tfunc add(other: Name) -> String { other.into() }\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Overlapping conformance")),
            "{errors:?}"
        );
    }

    #[test]
    fn generic_protocol_argument_conformance_uses_prefix_extend_generics() {
        let t = check(
            "// no-core\nstruct String {}\nstruct Name {}\nprotocol Into<Target> {\n\tfunc into() -> Target\n}\nprotocol Add<RHS> {\n\tassociated Ret\n\tfunc add(rhs: RHS) -> Ret\n}\nextend Name: Into<String> {\n\tfunc into() -> String { String() }\n}\nextend<T: Into<String>> String: Add<T> {\n\tfunc add(rhs other: T) -> String { other.into() }\n}\nlet result = String() + Name()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "result"), "String");
    }

    #[test]
    fn protocol_argument_keys_allow_same_self_protocol_with_different_args() {
        let t = check(
            "// no-core\nstruct String {}\nstruct Character {}\nprotocol Add<RHS> {\n\tassociated Ret\n\tfunc add(rhs: RHS) -> Ret\n}\nextend String: Add<String> {\n\tfunc add(rhs: String) -> Int { 1 }\n}\nextend String: Add<Character> {\n\tfunc add(rhs: Character) -> Int { 2 }\n}\nlet bothStrings = String() + String()\nlet stringAndCharacter = String() + Character()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "bothStrings"), "Int");
        assert_eq!(ty_of(&t, "stringAndCharacter"), "Int");
    }

    #[test]
    fn projections_reject_unprovable_equalities_on_rigid_params() {
        // `a + 1` inside `<T: Add<Bool>>` needs `T: Add<Int>`, which no bound
        // states; protocol arguments are conformance-key inputs, so this
        // must error rather than silently selecting a different application.
        let t = check(
            "// no-core\nprotocol Add<RHS> {\n\tassociated Ret\n\tfunc add(rhs: RHS) -> Ret\n}\nfunc bad<T: Add<Bool>>(a: T) { a + 1 }",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("the parameter requires Int, but the argument has type Bool"),
            "{errors:?}"
        );
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
            "// no-core\nprotocol A {\n\tfunc a() -> Int\n}\nprotocol B: A {}\nstruct S {}\nextend S: B {\n\tfunc a() -> Int { 1 }\n}\nfunc useA<T: A>(x: T) -> Int { x.a() }\nlet value = useA(x: S())",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "value"), "Int");
    }

    #[test]
    fn inherited_associated_types_reduce_through_subprotocol_conformance() {
        let t = check(
            "// no-core\nprotocol A {\n\tassociated Item\n\tfunc get() -> Item\n}\nprotocol B: A {}\nstruct S {}\nextend S: B {\n\tfunc get() -> Int { 1 }\n}\nfunc useA<T: A>(x: T) -> T.Item { x.get() }\nlet value = useA(x: S())",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "value"), "Int");
    }

    #[test]
    fn subprotocol_conformance_can_rely_on_later_superprotocol_conformance() {
        let t = check(
            "// no-core\nprotocol A {\n\tfunc a() -> Int\n}\nprotocol B: A {}\nstruct S {}\nextend S: B {}\nextend S: A {\n\tfunc a() -> Int { 1 }\n}\nfunc useA<T: A>(x: T) -> Int { x.a() }\nlet genericValue = useA(x: S())\nlet directValue = S().a()",
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
    fn exported_catalog_carries_no_unification_variables() {
        // Catalog types cross module boundaries, where this module's
        // store ids mean nothing: a leaked var reads foreign slots on the
        // importing side (silent mis-unification, or the "effect var
        // bound to non-effect value" panic).
        fn ty_has_vars(ty: &crate::types::ty::Ty) -> bool {
            use crate::types::ty::{EffTail, RowTail, Ty};
            match ty {
                Ty::Var(_) => true,
                Ty::Nominal(_, args) | Ty::Tuple(args) => args.iter().any(ty_has_vars),
                Ty::Borrow(_, inner) | Ty::Unique(inner) => ty_has_vars(inner),
                Ty::Func(params, ret, eff) => {
                    params.iter().any(ty_has_vars)
                        || ty_has_vars(ret)
                        || matches!(eff.tail, Some(EffTail::Var(_)))
                        || eff
                            .effects
                            .iter()
                            .any(|entry| entry.args.iter().any(ty_has_vars))
                }
                Ty::Record(row) => {
                    row.fields.iter().any(|(_, t)| ty_has_vars(t))
                        || matches!(row.tail, Some(RowTail::Var(_)))
                }
                Ty::Any { assoc, .. } => assoc.iter().any(|(_, t)| ty_has_vars(t)),
                Ty::Eff(eff) => {
                    matches!(eff.tail, Some(EffTail::Var(_)))
                        || eff
                            .effects
                            .iter()
                            .any(|entry| entry.args.iter().any(ty_has_vars))
                }
                Ty::Proj(base, ..) => ty_has_vars(base),
                Ty::Static(crate::types::ty::StaticValue::Int(int)) => int
                    .terms
                    .iter()
                    .any(|(atom, _)| matches!(atom, crate::types::ty::StaticAtom::Var(_))),
                Ty::Static(_) => false,
                Ty::Param(_) | Ty::Error => false,
            }
        }

        let t = check(
            "// no-core\nstruct Holder {\n\tlet f: (Int) -> Int\n}\nprotocol P {\n\tfunc run(fn: (Int) -> Int) -> Int\n}\neffect 'act(fn: (Int) -> Int) -> Int\nenum Cmd {\n\tcase go((Int) -> Int)\n}",
        );
        let module = t.module("VarFree");
        let catalog = &module.types.catalog;
        for (symbol, info) in &catalog.structs {
            for (label, (_, field_ty)) in &info.fields {
                assert!(
                    !ty_has_vars(field_ty),
                    "field {symbol}.{label} leaks vars: {field_ty:?}"
                );
            }
        }
        // Requirement and extend-member signatures are ordinary schemes
        // now; the exported schemes map is asserted below.
        for (symbol, scheme) in &module.types.schemes {
            assert!(
                !ty_has_vars(&scheme.ty),
                "exported scheme {symbol} leaks vars: {:?}",
                scheme.ty
            );
        }
        for (symbol, sig) in &catalog.effects {
            for ty in sig.params.iter().chain(std::iter::once(&sig.ret)) {
                assert!(!ty_has_vars(ty), "effect {symbol} leaks vars: {ty:?}");
            }
        }
        for (symbol, info) in &catalog.enums {
            for (label, variant) in &info.variants {
                assert!(
                    !ty_has_vars(&variant.constructor_scheme.ty),
                    "variant {symbol}.{label} leaks vars: {:?}",
                    variant.constructor_scheme.ty
                );
            }
        }
        for conformance in catalog.conformances.values() {
            for (assoc, ty) in &conformance.assoc {
                assert!(
                    !ty_has_vars(ty),
                    "conformance ({}, {}) assoc {assoc} leaks vars: {ty:?}",
                    conformance.head,
                    conformance.protocol
                );
            }
        }
    }

    #[test]
    fn self_qualified_associated_type_matches_bare_in_protocol_body() {
        // `Self.A` inside the protocol's own context names the assoc
        // param directly — it must unify with what `self.get()` returns.
        let t = check(
            "// no-core\nprotocol Q {\n\tassociated A\n\tfunc get() -> A\n\tfunc also() -> Self.A {\n\t\tself.get()\n\t}\n}",
        );
        assert_clean(&t);
    }

    // ----- Protocol extensions -------------------------------------------
    // `extend P { ... }` methods join P as defaulted requirements: checked
    // generically over Self like in-body defaults, witnessable by
    // conforming extends.

    #[test]
    fn protocol_extension_defaults_are_checked() {
        let t = check(
            "// no-core\nprotocol P {\n\tfunc base() -> Int\n}\nextend P {\n\tfunc doubled() -> Int {\n\t\tself.base()\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_extension_default_type_errors_are_reported() {
        let t = check(
            "// no-core\nprotocol P {\n\tfunc base() -> Int\n}\nextend P {\n\tfunc doubled() -> Int {\n\t\t1.5\n\t}\n}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
    }

    #[test]
    fn protocol_extension_methods_callable_on_conforming_types() {
        let t = check(
            "// no-core\nprotocol P {\n\tfunc base() -> Int\n}\nextend P {\n\tfunc doubled() -> Int {\n\t\tself.base()\n\t}\n}\nstruct S {}\nextend S: P {\n\tfunc base() -> Int { 1 }\n}\nfunc useP<T: P>(x: T) -> Int { x.doubled() }\nlet genericValue = useP(x: S())\nlet directValue = S().doubled()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "genericValue"), "Int");
        assert_eq!(ty_of(&t, "directValue"), "Int");
    }

    #[test]
    fn protocol_extension_registers_regardless_of_decl_order() {
        // The conforming extend appears before the protocol extension:
        // the extension's requirements must still be visible to it.
        let t = check(
            "// no-core\nprotocol P {\n\tfunc base() -> Int\n}\nstruct S {}\nextend S: P {\n\tfunc base() -> Int { 1 }\n}\nextend P {\n\tfunc doubled() -> Int {\n\t\tself.base()\n\t}\n}\nlet v = S().doubled()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "v"), "Int");
    }

    #[test]
    fn protocol_extension_uses_self_associated_types() {
        let t = check(
            "// no-core\nprotocol Q {\n\tassociated A\n\tfunc get() -> A\n}\nextend Q {\n\tfunc also() -> Self.A {\n\t\tself.get()\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_extension_mut_method_calls_mut_requirement() {
        let t = check(
            "// no-core\nprotocol I {\n\tassociated E\n\tmut func next() -> E\n}\nextend I {\n\tmut func twice() -> Self.E {\n\t\tself.next()\n\t\tself.next()\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_extension_method_with_where_clause() {
        let t = check(
            "// no-core\nprotocol Eq2 {\n\tfunc same(rhs: &Self) -> Bool\n}\nprotocol I {\n\tassociated E\n\tmut func next() -> E\n}\nextend I {\n\tmut func matches(needle: &Self.E) -> Bool where E: Eq2 {\n\t\tself.next().same(rhs: needle)\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_extension_where_clause_binds_associated_types() {
        // `E: Eq3<E>` adds a TypeEq given (E.R = E) that the default
        // body's `same` call needs to typecheck.
        let t = check(
            "// no-core\nprotocol Eq3 {\n\tassociated R\n\tfunc same(rhs: R) -> Bool\n}\nprotocol I {\n\tassociated E\n\tmut func next() -> E\n}\nextend I {\n\tmut func found(needle: E) -> Bool where E: Eq3<E> {\n\t\tneedle.same(rhs: self.next())\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_extension_conformance_solves_wanted_conformance() {
        let t = check(
            "// no-core\nprotocol P {\n\tfunc base() -> Int\n}\nprotocol R {\n\tfunc r() -> Int\n}\nextend P: R {\n\tfunc r() -> Int { self.base() }\n}\nfunc takeR<T: R>(x: T) {}\nfunc useP<T: P>(x: T) { takeR(x: x) }",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_extension_conformance_binds_head_associated_type_for_concrete_receiver() {
        let t = check(
            "// no-core\nstruct Sink<T> {}\nprotocol Iterator {\n\tassociated Element\n\tfunc current() -> Element\n}\nprotocol Into<Target> {\n\tconsuming func into() -> Target\n}\nextend Iterator: Into<Sink<Element>> {\n\tconsuming func into() -> Sink<Element> { Sink<Element>() }\n}\nstruct IntIter {}\nextend IntIter: Iterator<Int> {\n\tfunc current() -> Int { 1 }\n}\nlet sink: Sink<Int> = IntIter().into()",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "sink"), "Sink<Int>");
    }

    #[test]
    fn protocol_extension_conformance_binds_head_associated_type_for_generic_receiver() {
        let t = check(
            "// no-core\nstruct Sink<T> {}\nprotocol Iterator {\n\tassociated Element\n\tfunc current() -> Element\n}\nprotocol Into<Target> {\n\tconsuming func into() -> Target\n}\nextend Iterator: Into<Sink<Element>> {\n\tconsuming func into() -> Sink<Element> { Sink<Element>() }\n}\nfunc collect<T: Iterator<Int>>(consume x: T) -> Sink<Int> { x.into() }",
        );
        assert_clean(&t);
        assert_eq!(
            ty_of(&t, "collect"),
            "<T0: Iterator>(T0) -> Sink<Int> where Int == T0.Element"
        );
    }

    #[test]
    fn protocol_extension_conformance_binds_head_associated_type_for_existential_receiver() {
        let t = check(
            "// no-core\nstruct Sink<T> {}\nprotocol Iterator {\n\tassociated Element\n\tfunc current() -> Element\n}\nprotocol Into<Target> {\n\tconsuming func into() -> Target\n}\nextend Iterator: Into<Sink<Element>> {\n\tconsuming func into() -> Sink<Element> { Sink<Element>() }\n}\nfunc collect(consume x: any Iterator<Element = Int>) -> Sink<Int> { x.into() }",
        );
        assert_clean(&t);
    }

    #[test]
    fn overlapping_protocol_head_axiom_is_reported_at_use_site() {
        let t = check(
            "// no-core\nprotocol P {}\nprotocol R {\n\tfunc r() -> Int\n}\nstruct S {}\nextend S: P {}\nextend P: R {\n\tfunc r() -> Int { 1 }\n}\nextend S: R {\n\tfunc r() -> Int { 2 }\n}\nlet value = S().r()",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Overlapping conformance")),
            "{errors:?}"
        );
    }

    #[test]
    fn recursive_protocol_head_axiom_reports_cycle() {
        let t = check(
            "// no-core\nprotocol P {\n\tfunc p() -> Int\n}\nprotocol R {\n\tfunc r() -> Int\n}\nextend P: R where Self: R {\n\tfunc r() -> Int { self.p() }\n}\nfunc takeR<T: R>(x: T) {}\nfunc use<T: P>(x: T) { takeR(x: x) }",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Recursive protocol conformance")),
            "{errors:?}"
        );
    }

    #[test]
    fn protocol_extension_redeclaring_requirement_is_unsupported() {
        let t = check(
            "// no-core\nprotocol P {\n\tfunc base() -> Int\n}\nextend P {\n\tfunc base() -> Int { 1 }\n}",
        );
        let errors = type_errors(&t);
        assert_eq!(errors.len(), 1, "{errors:?}");
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
        let t = check("// no-core\nfunc identity(x) { x }\nlet a = identity(x: 123)");
        assert_clean(&t);
        let instantiations = &t.phase.program.types().instantiations;
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
    fn tuple_patterns_view_through_borrowed_elements() {
        let t = check(
            "// no-core\nenum Maybe<T> {\n\tcase some(T), none\n}\nfunc pick(lhs: Maybe<Int>, rhs: Maybe<Int>) -> Int {\n\tmatch (lhs, rhs) {\n\t\t(.some(a), .some(_)) -> a,\n\t\t(.none, .none) -> 0,\n\t\t_ -> 1\n\t}\n}",
        );
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
        let resolved = &typed.phase.program.resolved_names();
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let expr = resolved
            .symbol_names
            .iter()
            .find(|(sym, name)| {
                name.as_str() == "Expr"
                    && typed.phase.program.types().catalog.enums.contains_key(sym)
            })
            .map(|(sym, _)| *sym)
            .expect("Expr enum");
        let info = &typed.phase.program.types().catalog.enums[&expr];
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

            let i: Int = eval(expr: Expr.int(1))
            let b: Bool = eval(expr: Expr.bool(true))
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

            let i: Int = tag(expr: Expr.int(1))
            let j: Int = tag(expr: Expr.bool(true))
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

            let i: Int = to_int(expr: Expr.int(1), value: 41)
            let j: Int = to_int(expr: Expr.bool(true), value: false)
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

            read(box: Box.boxed(S()))
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
            "// no-core\nprotocol Showable {\n  consuming func show() -> Int\n}\nextend Int: Showable {\n  consuming func show() -> Int { self }\n}\nenum GBox<T> {\n  case hidden<A: Showable>(A) -> GBox<Bool>\n}\nfunc erase(consume box: GBox<Bool>) -> any Showable {\n  match box {\n    .hidden(value) -> value\n  }\n}",
        );
        assert_clean(&typed);
        assert_eq!(ty_of(&typed, "erase"), "(GBox<Bool>) -> any Showable");
    }

    #[test]
    fn gadt_derived_showable_ignores_impossible_payloads() {
        // Derivation is keyed by the well-known core protocol identity,
        // so this pin runs against core's Showable: GBox<Int>'s derived
        // row must ignore the `hidden` variant its result refinement
        // rules out.
        let typed = Driver::new(
            vec![Source::from(
                "enum GBox<T> {\n\tcase int(Int) -> GBox<Int>\n\tcase hidden<A>(A) -> GBox<Bool>\n}\n\nfunc render<T: Showable>(value: T) -> String {\n\tvalue.show()\n}\n\nrender(value: GBox.int(1))\n()\n",
            )],
            DriverConfig::new("TypesTest"),
        )
        .parse()
        .expect("parse failed")
        .resolve_names()
        .expect("name resolution failed")
        .type_check();
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
    use super::tests::compile_library;
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
    fn host_effects_admit_handlers() {
        // Every host-list effect routes through the ordinary handler
        // stack (ADR 0039): user handlers may intercept 'io, 'alloc, and
        // 'async alike; unhandled performs reach the host fallback.
        for source in [
            "@handle 'io { request in\n\t'continue 0\n}\n1",
            "@handle 'alloc { allocation in\n\t'continue\n}\n1",
            "@handle 'async {\n\t'continue\n}\n'async()\n1",
        ] {
            let t = check_with_core(Source::from(source));
            let errors = type_errors(&t);
            assert!(errors.is_empty(), "{source}: {errors:?}");
        }
    }

    #[test]
    fn range_literals_construct_core_range_types() {
        // `1..3` and `1..<3` desugar to direct ClosedRange/Range
        // constructions (imported core symbols render by id here, so
        // assert shape: distinct nominal heads applied at Int, no
        // leftover variables). The inclusive/half-open semantics mapping
        // is pinned by core/Range.test.tlk and the runtime tests.
        let t = check_with_core(Source::from("let c = 1..3\nlet r = 1..<3"));
        assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
        let c = super::tests::ty_of(&t, "c");
        let r = super::tests::ty_of(&t, "r");
        assert!(c.ends_with("<Int>"), "{c}");
        assert!(r.ends_with("<Int>"), "{r}");
        assert_ne!(c, r);
    }

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
    fn struct_eff_params_cross_the_module_boundary() {
        // A struct with closure fields exports its implicit effect params
        // (quantified field tails, no leaked variables); the importing
        // module constructs and reads with per-construction rows, and the
        // stored effect still demands a handler — nothing is laundered by
        // the module boundary.
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let id_a = ModuleId::External(0);
        let module_a = compile_library(
            "A",
            id_a,
            "public struct Wrapper {\n\tlet f: () -> Int\n}",
            ModuleEnvironment::default(),
        );

        let mut modules = ModuleEnvironment::default();
        modules.import_compiled(module_a, id_a).unwrap();
        let config = crate::compiling::driver::DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(modules),
            mode: crate::compiling::driver::CompilationMode::Library,
            module_name: "B".to_string(),
            parse_mode: crate::compiling::driver::ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        };
        let driver_b = Driver::new(
            vec![Source::from(
                "use A::{ Wrapper }\neffect 'ping() -> Void\nfunc pure_use() -> Int {\n\tlet w = Wrapper(f: func() { 1 })\n\tw.f()\n}\nfunc pingy_use() -> Int {\n\tlet w = Wrapper(f: func() {\n\t\t'ping()\n\t\t1\n\t})\n\tw.f()\n}\npure_use()\npingy_use()",
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
        // pure_use is clean; pingy_use's stored 'ping reaches the top
        // level unhandled — the row traveled through the imported struct.
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("No handler for 'ping"), "{errors:?}");
    }

    #[test]
    fn overlapping_imported_inherent_rows_are_ambiguous_at_use() {
        // Sibling modules A and B each extend S's Box<Int> with `tag`
        // without importing each other; a consumer importing both must get
        // an ambiguity diagnostic at the use site, never import-order
        // dispatch.
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let (id_s, id_a, id_b) = (
            ModuleId::External(0),
            ModuleId::External(1),
            ModuleId::External(2),
        );
        let module_s = compile_library(
            "S",
            id_s,
            "public struct Box<T> {\n\tlet value: T\n}",
            ModuleEnvironment::default(),
        );

        let sibling = |name: &str, id: ModuleId, body: &'static str| {
            let mut modules = ModuleEnvironment::default();
            modules.import_compiled(module_s.clone(), id_s).unwrap();
            compile_library(name, id, body, modules)
        };
        let module_a = sibling(
            "A",
            id_a,
            "use S::{ Box }\nextend Box<Int> {\n\tpublic func tag() -> Int { 1 }\n}",
        );
        let module_b = sibling(
            "B",
            id_b,
            "use S::{ Box }\nextend Box<Int> {\n\tpublic func tag() -> Int { 2 }\n}",
        );

        let mut modules = ModuleEnvironment::default();
        modules.import_compiled(module_s, id_s).unwrap();
        modules.import_compiled(module_a, id_a).unwrap();
        modules.import_compiled(module_b, id_b).unwrap();
        let config = crate::compiling::driver::DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(modules),
            mode: crate::compiling::driver::CompilationMode::Library,
            module_name: "C".to_string(),
            parse_mode: crate::compiling::driver::ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        };
        let typed = Driver::new(
            vec![Source::from(
                "use S::{ Box }\nuse A\nuse B\nlet t = Box(value: 1).tag()",
            )],
            config,
        )
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .type_check();
        let errors = type_errors(&typed);
        assert!(
            errors.iter().any(|e| e.contains("Ambiguous")),
            "overlapping imported rows must be ambiguous at use, got {errors:?}"
        );
    }

    #[test]
    fn external_module_types_cross_the_boundary() {
        // Compile module A, import it into module B as an external module:
        // A's schemes and catalog must arrive with symbols remapped to B's
        // view of A (milestone 6).
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let id_a = ModuleId::External(0);
        let module_a = compile_library(
            "A",
            id_a,
            "public struct Hello {\n\tlet x: Int\n}\npublic func make(v: Int) -> Hello { Hello(x: v) }",
            ModuleEnvironment::default(),
        );

        let mut modules = ModuleEnvironment::default();
        modules.import_compiled(module_a, id_a).unwrap();
        let config = crate::compiling::driver::DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(modules),
            mode: crate::compiling::driver::CompilationMode::Library,
            module_name: "B".to_string(),
            parse_mode: crate::compiling::driver::ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        };
        let driver_b = Driver::new(
            vec![Source::from(
                "use A::{ make }\nlet v = make(v: 3).x\nlet bad: Int = make(v: 3)",
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
        let resolved = &typed.phase.program.resolved_names();
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let v = resolved
            .symbol_names
            .iter()
            .find(|(sym, n)| {
                n.as_str() == "v" && typed.phase.program.types().schemes.contains_key(sym)
            })
            .map(|(sym, _)| *sym)
            .expect("v scheme");
        assert_eq!(typed.phase.program.types().schemes[&v].render(), "Int");
    }

    #[test]
    fn public_type_aliases_cross_module_boundary() {
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let id_a = ModuleId::External(0);
        let module_a = compile_library(
            "A",
            id_a,
            "public typealias UserId = Int\npublic func make() -> UserId { 1 }",
            ModuleEnvironment::default(),
        );

        let mut modules = ModuleEnvironment::default();
        modules.import_compiled(module_a, id_a).unwrap();
        let config = crate::compiling::driver::DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(modules),
            mode: crate::compiling::driver::CompilationMode::Library,
            module_name: "B".to_string(),
            parse_mode: crate::compiling::driver::ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        };
        let driver_b = Driver::new(
            vec![Source::from(
                "use A::{ UserId, make }\nlet id: UserId = make()",
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
        let resolved = &typed.phase.program.resolved_names();
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let symbol = resolved
            .symbol_names
            .iter()
            .find(|(sym, n)| {
                n.as_str() == "id" && typed.phase.program.types().schemes.contains_key(sym)
            })
            .map(|(sym, _)| *sym)
            .expect("id scheme");
        assert_eq!(typed.phase.program.types().schemes[&symbol].render(), "Int");
    }

    #[test]
    fn fib_against_core_is_int() {
        let typed = check_with_core(Source::from(
            "let x = fib(n: 24)\nfunc fib(n) {\n\tif n <= 1 { return n }\n\treturn fib(n: n - 2) + fib(n: n - 1)\n}",
        ));
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
        let resolved = &typed.phase.program.resolved_names();
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let symbol = resolved
            .symbol_names
            .iter()
            .find(|(sym, n)| {
                n.as_str() == "x" && typed.phase.program.types().schemes.contains_key(sym)
            })
            .map(|(sym, _)| *sym)
            .expect("x scheme");
        assert_eq!(typed.phase.program.types().schemes[&symbol].render(), "Int");
    }

    #[test]
    fn borrow_shaped_equatable_witness_conforms() {
        // ADR 0014: comparison requirements take `rhs: &RHS`, so a
        // non-Copy conforming type witnesses with the borrow spelled out.
        let typed = check_with_core(Source::from(
            "struct Pt {\n\tlet x: Int\n}\nextend Pt: Equatable<Pt> {\n\tfunc equals(_ rhs: &Pt) -> Bool {\n\t\tself.x == rhs.x\n\t}\n}\nlet hit = Pt(x: 1) == Pt(x: 1)",
        ));
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn equatable_is_derived_structurally_for_same_type_structs_and_enums() {
        let typed = check_with_core(Source::from(
            "struct Point {\n\tlet x: Int\n\tlet y: Int\n}\nenum Choice<T> {\n\tcase none\n\tcase value(T)\n}\nlet point = Point(x: 1, y: 2) == Point(x: 1, y: 2)\nlet choice = Choice.value(3) != Choice.value(4)",
        ));
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn equality_prefers_same_type_context_for_leading_dot_variants() {
        let typed = check_with_core(Source::from(
            "let iterator = [1, 2, 3].into_iter().peekable()\nlet matches = iterator.peek() == .some(1)\nlet differs = iterator.peek() != .none",
        ));
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn equality_keeps_concrete_cross_type_conformance_as_fallback() {
        let typed = check_with_core(Source::from(
            "struct A {}\nstruct B {}\nextend A: Equatable<B> {\n\tfunc equals(_ rhs: B) -> Bool { true }\n}\nlet matches = A() == B()",
        ));
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn derived_equatable_does_not_supply_cross_type_or_heap_conformance() {
        let cross_type = check_with_core(Source::from(
            "struct Point {\n\tlet x: Int\n}\nlet invalid = Point(x: 1) == 1",
        ));
        assert!(!type_errors(&cross_type).is_empty());

        let heap = check_with_core(Source::from(
            "struct Node 'heap {\n\tlet value: Int\n}\nlet invalid = Node(value: 1) == Node(value: 1)",
        ));
        assert!(!type_errors(&heap).is_empty());
    }

    #[test]
    fn equality_operator_reports_operand_types_without_changing_explicit_calls() {
        let operators = check_with_core(Source::from(
            "let value: Int? = .some(1)\nlet a = value == 1\nlet b = value != 2",
        ));
        let errors = type_errors(&operators);
        assert_eq!(
            errors
                .iter()
                .filter(|error| {
                    error.contains("Cannot compare Optional<Int> with Int for equality")
                })
                .count(),
            2,
            "{errors:?}"
        );

        let explicit = check_with_core(Source::from(
            "let value: Int? = .some(1)\nlet invalid = Equatable.equals(value, 1)",
        ));
        let errors = type_errors(&explicit);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Optional<Int> does not conform to Equatable<Int>")),
            "{errors:?}"
        );
        assert!(
            errors.iter().all(|error| !error.contains("Cannot compare")),
            "{errors:?}"
        );
    }

    #[test]
    fn conformance_dispatch_publishes_receiver_theta_on_node() {
        // Swift model: the node carries the complete θ. A ViaConformance
        // callee's instantiation must include the receiver-derived
        // entries (the conformance row's params bound at the receiver
        // head), not just method generics — lowering reads, never
        // re-derives.
        let typed = check_with_core(Source::from(
            "let xs = [10, 20, 30]\nlet it = xs.iter()\nlet r = it.skip(count: 1)",
        ));
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
        let published = typed
            .phase
            .program
            .types()
            .member_resolutions
            .iter()
            .filter(|(_, resolution)| {
                matches!(
                    resolution,
                    crate::types::output::MemberResolution::ViaConformance { .. }
                )
            })
            .any(|(node, _)| {
                typed
                    .phase
                    .program
                    .types()
                    .instantiations
                    .get(node)
                    .is_some_and(|pairs| {
                        pairs.iter().any(|(symbol, _)| {
                            matches!(symbol, crate::name_resolution::symbol::Symbol::Protocol(_))
                        })
                    })
            });
        let dump: Vec<String> = typed
            .phase
            .program
            .types()
            .member_resolutions
            .iter()
            .filter(|(_, r)| {
                matches!(
                    r,
                    crate::types::output::MemberResolution::ViaConformance { .. }
                )
            })
            .map(|(node, r)| {
                format!(
                    "{node:?} {r:?} => {:?}",
                    typed
                        .phase
                        .program
                        .types()
                        .instantiations
                        .get(node)
                        .map(|pairs| pairs
                            .iter()
                            .map(|(s, t)| format!("{s} = {}", t.render_mono()))
                            .collect::<Vec<_>>())
                )
            })
            .collect();
        assert!(
            published,
            "no ViaConformance callee node carries a receiver-derived θ entry; got:\n{}",
            dump.join("\n")
        );
    }

    #[test]
    fn chained_map_with_closure_checks() {
        // `map`'s closure param is a higher-order signature: its latent
        // effect row must be an eff param freshened per use, not a raw
        // store var leaked through the exported catalog (a foreign-store
        // id panics or silently couples unrelated constraints).
        let typed = check_with_core(Source::from(
            "let xs = [10, 20, 30]\nlet m = xs.iter().map() { x in x }",
        ));
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn map_to_array_uses_iterator_conformance_with_effect_row_arg() {
        let typed = check_with_core(Source::from(
            "let xs = [1, 2, 3]\nlet ys: [String] = xs.map { x in x.show() }.to_array()",
        ));
        let errors = type_errors(&typed);
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn chained_iterator_index_terminates() {
        // Dispatching a requirement whose where clause binds an assoc type
        // (`index`'s `Equatable<Element>`) at Element = &Int produces the
        // given `Int ~ &Int` — a self-referential rewrite (the target
        // contains the source) that must not diverge in the given-rewrite
        // fixpoint. Termination is the assertion; the diagnostics are
        // whatever the borrow story currently yields.
        let typed = check_with_core(Source::from(
            "let xs = [10, 20, 30]\nlet r = xs.iter().index(needle: 20)",
        ));
        let _ = type_errors(&typed);
    }

    #[test]
    fn struct_closure_fields_are_effect_polymorphic_per_construction() {
        // Effect params on structs (docs/effect-params-on-structs-plan.md):
        // a closure field's row is quantified per construction (implicit
        // effect params on the nominal head, instantiated at the
        // constructor, recovered at reads) — storing an effectful closure
        // in ONE Wrapper contaminates nothing else.
        let typed = check_with_core(Source::from(
            "struct Wrapper {\n\tlet f: () -> Int\n}\neffect 'ping() -> Void\nfunc pure_use() -> Int {\n\tlet w = Wrapper(f: func() { 1 })\n\tw.f()\n}\nfunc pingy_use() 'ping -> Int {\n\tlet w = Wrapper(f: func() {\n\t\t'ping()\n\t\t1\n\t})\n\tw.f()\n}\npure_use()",
        ));
        let errors = type_errors(&typed);
        assert_eq!(errors, Vec::<String>::new());
    }

    #[test]
    fn struct_closure_field_rows_travel_with_the_instance() {
        // The SOUND direction: the stored closure's effects ride the
        // instance's type out of `make`, so calling the field elsewhere
        // still demands a handler — a struct cannot launder an effect.
        let typed = check_with_core(Source::from(
            "struct Wrapper {\n\tlet f: () -> Int\n}\neffect 'ping() -> Void\nfunc make() -> Wrapper {\n\tWrapper(f: func() {\n\t\t'ping()\n\t\t1\n\t})\n}\nfunc use_it() -> Int {\n\tlet w = make()\n\tw.f()\n}\nuse_it()",
        ));
        let errors = type_errors(&typed);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].contains("No handler for 'ping"), "{errors:?}");
    }

    #[test]
    fn generic_struct_closure_fields_stay_polymorphic_per_instantiation() {
        // The Map-shaped case: a generic struct's closure field, two
        // instantiations with different rows — neither contaminates the
        // other (type params and effect params instantiate together).
        let typed = check_with_core(Source::from(
            "struct Holder<T> {\n\tlet f: (T) -> T\n}\neffect 'ping() -> Void\nfunc pure_use() -> Int {\n\tlet h = Holder(f: func(x: Int) { x })\n\th.f(1)\n}\nfunc pingy_use() 'ping -> Bool {\n\tlet h = Holder(f: func(x: Bool) {\n\t\t'ping()\n\t\tx\n\t})\n\th.f(true)\n}\npure_use()",
        ));
        let errors = type_errors(&typed);
        assert_eq!(errors, Vec::<String>::new());
    }

    #[test]
    fn for_loop_over_string_iterator_checks_cleanly() {
        // `String.iter()` resolves through the Iterable conformance
        // (protocol-extension dispatch); the for-loop consumes the
        // returned CharacterIterator with no diagnostics.
        let typed = check_with_core(Source::from(
            "func f(s: String) {\n\tlet chars = s.iter()\n\tfor c in chars {}\n}",
        ));
        let errors = type_errors(&typed);
        assert_eq!(errors, Vec::<String>::new());
    }

    // === Grades: Copy / Affine / Linear (substructural core) ===
    // These check against the real core prelude, where the Copy / CheapClone /
    // Deinit marker protocols live.

    fn assert_no_errors(driver: &Driver<Typed>) {
        let errors = type_errors(driver);
        assert!(errors.is_empty(), "expected no type errors: {errors:?}");
    }

    #[test]
    fn specialized_copy_row_does_not_stop_donation() {
        // `extend Box<Int>: Copy` is evidence about Box<Int> only — but
        // under implicit sharing a borrowed non-Copy Box<S> still fills
        // an owned parameter by donating a retain, so no grading question
        // arises at this boundary at all.
        let t = check_with_core(Source::from(
            "struct Box<T> {\n\tlet value: T\n}\nextend Box<Int>: Copy {}\nstruct S {\n\tlet name: String\n}\nfunc takes(consume b: Box<S>) {}\nfunc caller(b: &Box<S>) {\n\ttakes(b: b)\n}",
        ));
        let errors = type_errors(&t);
        assert!(
            errors.is_empty(),
            "donation covers this boundary: {errors:?}"
        );
    }

    #[test]
    fn each_marker_claim_validates_its_own_row() {
        // Two disjoint Copy rows must each validate against their own
        // arguments: Box<S> is not Copy even though Box<Int> is.
        let t = check_with_core(Source::from(
            "struct Box<T> {\n\tlet value: T\n}\nstruct S {\n\tlet name: String\n}\nextend Box<Int>: Copy {}\nextend Box<S>: Copy {}",
        ));
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("Copy")),
            "Box<S>: Copy must be rejected (S stores a String), got {errors:?}"
        );
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
    fn marker_field_check_sees_generic_conformance_row() {
        // A declared generic marker conformance (`extend Ref<T>: CheapClone`)
        // is the authority for `Ref<ExprTag>` fields — the field check must
        // consult the row, not re-derive its own per-argument rule (which
        // rejected the phantom empty-enum tag).
        let t = check_with_core(Source::from(
            "enum ExprTag {}\nenum Ref<T> {\n\tcase expr(Int) -> Ref<ExprTag>\n}\nextend Ref<T>: CheapClone {}\nenum Work {\n\tcase dump(Ref<ExprTag>)\n\tcase text(String)\n}\nextend Work: CheapClone {}",
        ));
        assert_no_errors(&t);
    }

    #[test]
    fn marker_field_check_sees_generic_copy_row() {
        let t = check_with_core(Source::from(
            "enum ExprTag {}\nenum Ref<T> {\n\tcase expr(Int) -> Ref<ExprTag>\n}\nextend<T> Ref<T>: Copy {}\nstruct Slot {\n\tlet target: Ref<ExprTag>\n}\nextend Slot: Copy {}",
        ));
        assert_no_errors(&t);
    }

    #[test]
    fn conditional_marker_conformance_validates_against_its_context() {
        // The where-clause is the authority for a conditional row's own
        // field check: `T` satisfies CheapClone because the context says so.
        let t = check_with_core(Source::from(
            "struct Box<T> {\n\tlet value: T\n}\nextend<T> Box<T>: CheapClone where T: CheapClone {}\nstruct Holder {\n\tlet inner: Box<String>\n}\nextend Holder: CheapClone {}",
        ));
        assert_no_errors(&t);
    }

    #[test]
    fn bare_method_reference_is_a_type_error() {
        // A method used as a value has no lowering yet; the TYPE CHECKER
        // owns the rejection — an internal lowering error is not a
        // diagnostic.
        let t = check_with_core(Source::from("let f = \"fizz\".add\nprint(f(\"buzz\"))"));
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("add")),
            "expected a method-reference diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn method_calls_and_unit_variants_still_resolve() {
        // The rejection is scoped to bare VALUE-receiver method
        // references: calls, operator desugars, fields, and type-receiver
        // members stay legal.
        let t = check_with_core(Source::from(
            "let text = \"fizz\" + \"buzz\"\nlet count = text.byte_count\nlet empty: Int? = Optional.none\nprint(text.to_string())\nprint(count)\nmatch empty {\n\t.some(v) -> print(v),\n\t.none -> print(0)\n}",
        ));
        assert_no_errors(&t);
    }

    #[test]
    fn conditional_cheap_clone_satisfied_context_extracts_from_borrow() {
        // The satisfied twin still extracts by silent clone.
        let t = check_with_core(Source::from(
            "struct Box<T> {\n\tlet value: T\n}\nextend<T> Box<T>: CheapClone where T: CheapClone {}\nfunc peek(b: &Box<String>?) -> Box<String>? {\n\tmatch b {\n\t\t.some(found) -> Optional.some(found),\n\t\t.none -> Optional.none\n\t}\n}",
        ));
        assert!(
            !t.has_errors(),
            "expected the satisfied context to extract cleanly"
        );
    }

    #[test]
    fn conditional_marker_conformance_rejects_unsatisfied_context() {
        // The same row must NOT satisfy a field whose argument fails the
        // where-clause: Box<NotCheap> is not CheapClone.
        let t = check_with_core(Source::from(
            "struct Box<T> {\n\tlet value: T\n}\nextend<T> Box<T>: CheapClone where T: CheapClone {}\nstruct NotCheap {\n\tlet value: String\n}\nstruct Holder {\n\tlet inner: Box<NotCheap>\n}\nextend Holder: CheapClone {}",
        ));
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("CheapClone")),
            "expected a non-CheapClone-field error, got {errors:?}"
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
    fn deinit_conformance_rejects_user_effects_in_its_row() {
        // ADR 0027 (open question 2): drop glue calls deinit hooks through
        // a fixed signature with no capability parameters, so an effectful
        // deinit body could never receive its handler — the conformance
        // must reject a user effect in the hook's row.
        let t = check_with_core(Source::from(
            "effect 'noise() -> Void\n@handle 'noise { 'continue () }\nstruct Loud {\n\tlet s: String\n}\nextend Loud: Deinit {\n\tconsuming func deinit() -> Void {\n\t\t'noise()\n\t}\n}",
        ));
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("Deinit")),
            "expected a Deinit-row error, got {errors:?}"
        );
    }

    #[test]
    fn deinit_conformance_accepts_effects_handled_inside_the_body() {
        // The twin: a deinit body may install its OWN handler and perform
        // under it — the hook's row stays pure at the conformance
        // boundary, so drop glue needs no capabilities.
        let t = check_with_core(Source::from(
            "effect 'noise() -> Void\nstruct Loud {\n\tlet s: String\n}\nextend Loud: Deinit {\n\tconsuming func deinit() -> Void {\n\t\t@handle 'noise { 'continue () }\n\t\t'noise()\n\t}\n}",
        ));
        assert_no_errors(&t);
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
            "effect 'oops(e) -> Never\n@handle 'oops { e in\n\t42\n}\nfunc boom() 'oops -> () {\n\t'oops(e: \"x\")\n}\nboom()",
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
            "effect 'oops(e) -> Never\nfunc f() -> Int {\n\t@handle 'oops { e in\n\t\t\"nope\"\n\t}\n\t'oops(e: \"x\")\n\t42\n}\nf()",
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
            "effect 'oops(e) -> Never\neffect 'ask(q) -> Int\n@handle 'oops { e in\n\t0\n}\n@handle 'ask { q in\n\t'continue 1\n}\nfunc go() '[oops, ask] -> Int {\n\t'ask(q: \"?\")\n}\ngo()",
        ));
        assert_no_errors(&t);
    }

    #[test]
    fn unique_annotation_parses_and_renders() {
        let t = check_with_core(Source::from(
            "func pass(consume x: *String) -> *String {\n\tx\n}",
        ));
        assert_no_errors(&t);
        let resolved = &t.phase.program.resolved_names();
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let symbol = resolved
            .symbol_names
            .iter()
            .find(|(sym, n)| {
                n.as_str() == "pass" && t.phase.program.types().schemes.contains_key(sym)
            })
            .map(|(sym, _)| *sym)
            .expect("pass scheme");
        assert_eq!(
            t.phase.program.types().schemes[&symbol].render(),
            "(*String) -> *String"
        );
    }

    #[test]
    fn character_literal_has_character_type() {
        let t = check_with_core(Source::from("let c = 'a'"));
        assert_no_errors(&t);
        let resolved = &t.phase.program.resolved_names();
        let _names =
            crate::name_resolution::symbol::set_symbol_names(resolved.symbol_names.clone());
        let symbol = resolved
            .symbol_names
            .iter()
            .find(|(sym, name)| {
                name.as_str() == "c" && t.phase.program.types().schemes.contains_key(sym)
            })
            .map(|(sym, _)| *sym)
            .expect("c scheme");
        assert_eq!(
            t.phase.program.types().schemes[&symbol].render(),
            "Character"
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
        let resolved = &t.phase.program.resolved_names();
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
        let catalog = &t.phase.program.types().catalog;
        assert_eq!(catalog.grade_of(symbol_named("FileHandle")), Grade::Linear);
        assert_eq!(catalog.grade_of(symbol_named("Plain")), Grade::Copy);
        assert_eq!(catalog.grade_of(symbol_named("Holder")), Grade::Affine);
        assert_eq!(catalog.grade_of(Symbol::Int), Grade::Copy);
        assert_eq!(catalog.grade_of(Symbol::String), Grade::Affine);
    }

    #[test]
    fn result_equatable_is_conditional_on_both_arguments() {
        let clean = check_with_core(Source::from(
            "let left: Result<Int, String> = .ok(1)\nlet right: Result<Int, String> = .ok(1)\nprint(left == right)",
        ));
        assert_no_errors(&clean);

        let rejected = check_with_core(Source::from(
            "struct NotEquatable {\n\tlet callback: () -> Int\n}\nlet left: Result<NotEquatable, String> = .ok(NotEquatable(callback: func() { 1 }))\nlet right: Result<NotEquatable, String> = .ok(NotEquatable(callback: func() { 1 }))\nprint(left == right)",
        ));
        let errors = type_errors(&rejected);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("does not conform") && error.contains("Equatable")),
            "{errors:?}"
        );
    }

    #[test]
    fn match_uses_all_variant_names_to_disambiguate_shared_cases() {
        let t = check_with_core(Source::from(
            "enum Scan {\n\tcase ok\n\tcase no\n\tcase failed(String)\n}\nfunc scan() -> Scan { .ok }\nlet value = match scan() {\n\t.ok -> 1,\n\t.no -> 2,\n\t.failed(_) -> 3\n}",
        ));
        assert_no_errors(&t);
    }

    #[test]
    fn clone_method_exists_for_copy_and_cheapclone_values() {
        let t = check_with_core(Source::from(
            "struct BoxedText {\n\tlet value: String\n}\nextend BoxedText: CheapClone {}\nlet original = BoxedText(value: \"hi\")\nlet duplicate = original.clone()\nlet number = 1\nlet copied = number.clone()\nprint(original.value)\nprint(duplicate.value)\nprint(number + copied)",
        ));
        assert_no_errors(&t);
    }

    #[test]
    fn clone_method_is_rejected_for_affine_values() {
        let t = check_with_core(Source::from(
            "struct Affine {\n\tlet value: String\n}\nlet value = Affine(value: \"hi\")\nlet duplicate = value.clone()",
        ));
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Unknown member 'clone'")),
            "{errors:?}"
        );
    }

    #[test]
    fn payload_free_enum_borrow_coerces_to_owned() {
        // A plain (non-consume) param arrives as a borrow; a payload-free
        // enum is a bare tag (Copy grade), so passing it on to an owned
        // position, even nested inside a construction, must succeed.
        let t = super::tests::check(
            "// no-core
enum Kind {
	case left
	case right
}

struct Token {
	let kind: Kind
	init(kind: Kind) { self.kind = kind }
}

func make_token(kind: Kind) -> Token {
	Token(kind: kind)
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn enum_with_payload_stays_affine() {
        use crate::name_resolution::symbol::Symbol;
        use crate::types::catalog::Grade;
        let t = super::tests::check(
            "// no-core
enum Tag {
	case a
	case b
}
enum Carrier {
	case none
	case value(Int)
}",
        );
        super::tests::assert_clean(&t);
        let resolved = &t.phase.program.resolved_names();
        let enum_named = |name: &str| -> Symbol {
            resolved
                .symbol_names
                .iter()
                .find(|(sym, n)| n.as_str() == name && matches!(sym, Symbol::Enum(_)))
                .map(|(sym, _)| *sym)
                .unwrap_or_else(|| panic!("no enum symbol named {name}"))
        };
        let catalog = &t.phase.program.types().catalog;
        assert_eq!(catalog.grade_of(enum_named("Tag")), Grade::Copy);
        assert_eq!(catalog.grade_of(enum_named("Carrier")), Grade::Affine);
    }

    #[test]
    fn static_func_can_construct_its_own_type() {
        let t = super::tests::check(
            "// no-core
struct Box3 {
	let flag: Bool
	init() { self.flag = false }

	static func make_it() -> Box3 {
		Box3()
	}
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_func_can_construct_its_own_type_with_args() {
        let t = super::tests::check(
            "// no-core
struct Pair {
	let a: Int
	let b: Int
	init(a: Int, b: Int) {
		self.a = a
		self.b = b
	}

	static func zero() -> Pair {
		Pair(a: 0, b: 0)
	}
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn question_mark_types_as_first_payload_and_returns_second_variant() {
        let t = super::tests::check(
            "// no-core
             enum Outcome<Value, Failure> {
                 case success(Value)
                 case failure(Failure)
             }
             func source() -> Outcome<Int, Bool> { .success(41) }
             func outer() -> Outcome<Bool, Bool> {
                 let value = source()?
                 Outcome.success(true)
             }",
        );
        super::tests::assert_clean(&t);
        assert_eq!(
            super::tests::ty_of(&t, "outer"),
            "() -> Outcome<Bool, Bool>"
        );
    }

    #[test]
    fn force_unwrap_types_as_first_payload_and_performs_panic() {
        let t = super::tests::check(
            "// no-core
             effect 'panic(message) -> Never
             enum Outcome<Value, Failure> {
                 case success(Value)
                 case failure(Failure)
             }
             func force(consume outcome: Outcome<Int, Bool>) -> Int {
                 outcome!
             }",
        );
        super::tests::assert_clean(&t);
        assert_eq!(
            super::tests::ty_of(&t, "force"),
            "(Outcome<Int, Bool>) -> Int ! <'panic>"
        );
    }

    #[test]
    fn force_unwrap_waits_for_a_member_call_result_to_resolve() {
        let t = super::tests::check(
            "// no-core
             effect 'panic(message) -> Never
             enum Outcome<Value, Failure> {
                 case success(Value)
                 case failure(Failure)
             }
             struct Parser {
                 consuming func parse() -> Outcome<Int, Bool> {
                     .success(42)
                 }
             }
             func force(consume parser: Parser) -> Int {
                 parser.parse()!
             }",
        );
        super::tests::assert_clean(&t);
        assert_eq!(
            super::tests::ty_of(&t, "force"),
            "(Parser) -> Int ! <'panic>"
        );
    }

    #[test]
    fn force_unwrap_uses_the_first_variants_payload_shape() {
        let t = super::tests::check(
            "// no-core
             effect 'panic(message) -> Never
             enum PairOrError<A, B, E> {
                 case pair(A, B)
                 case error(E)
             }
             func force(consume value: PairOrError<Int, Bool, Int>) -> (Int, Bool) {
                 value!
             }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn question_mark_rejects_enums_without_exactly_two_variants() {
        let t = super::tests::check(
            "// no-core
             enum Choice<T> { case first(T) case second case third }
             func bad() -> Choice<Int> {
                 Choice.first(1)?
             }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("propagation requires exactly two")),
            "{errors:?}"
        );
    }

    #[test]
    fn force_unwrap_rejects_enums_without_exactly_two_variants() {
        let t = super::tests::check(
            "// no-core
             effect 'panic(message) -> Never
             enum Choice<T> { case first(T) case second case third }
             func bad(consume choice: Choice<Int>) -> Int {
                 choice!
             }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("force unwrap requires exactly two")),
            "{errors:?}"
        );
    }

    #[test]
    fn instance_method_can_construct_its_own_type() {
        let t = super::tests::check(
            "// no-core
struct Counter {
	let n: Int
	init(n: Int) { self.n = n }

	func bump() -> Counter {
		Counter(n: self.n + 1)
	}
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_generic_argument_forms_a_type() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f(consume g: Grid<4>) -> Grid<4> { g }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn parenthesized_static_arguments_type_check() {
        // ADR 0035 grammar: parentheses are part of the index language,
        // including in leading position.
        let t = super::tests::check(
            "// no-core
struct Grid<static N: Int> {}
func f(consume g: Grid<(2 + 2)>) -> Grid<4> { g }
func h<static K: Int>(consume g: Grid<(K + 1)>) -> Grid<K + 1> { g }
func i<static K: Int>(consume g: Grid<(K)>) -> Grid<K> { g }
func j<static K: Int>(consume g: Grid<(K + 1) * 2>) -> Grid<2 * K + 2> { g }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_closed_arithmetic_reduces_before_identity() {
        // ADR 0035 §4: Grid<2 + 2> and Grid<4> are the same type.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f(consume g: Grid<2 + 2>) -> Grid<4> { g }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_affine_forms_are_definitionally_equal() {
        // ADR 0035 §4: N + 1 and 1 + N are one type; 2 * N and N + N too.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f<static N: Int>(consume g: Grid<N + 1>) -> Grid<1 + N> { g }
func h<static N: Int>(consume g: Grid<2 * N>) -> Grid<N + N> { g }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_argument_mismatch_is_rejected() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f(consume g: Grid<4>) -> Grid<5> { g }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("mismatch")
                || error.contains("Mismatch")
                || error.contains("requires")),
            "{errors:?}"
        );
    }

    #[test]
    fn static_param_value_type_domain_is_validated() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: String> {}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("value type must be Int, Bool, or a fieldless enum")),
            "{errors:?}"
        );
    }

    #[test]
    fn type_argument_in_static_slot_is_rejected() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f(g: Grid<Int>) { }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("must be a static value expression")),
            "{errors:?}"
        );
    }

    #[test]
    fn static_param_in_type_position_is_rejected() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f<static N: Int>(consume g: Grid<N>) -> N { g }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static value expression is not a type")),
            "{errors:?}"
        );
    }

    #[test]
    fn gadt_case_result_may_apply_static_argument_to_own_head() {
        // The enum's param kinds must be visible while its own case
        // results lower (header pre-pass), or `true` is rejected as a
        // static value in type position.
        let t = super::tests::check(
            "// no-core
enum GADTResult<T, static IsOK: Bool> {
case ok(T) -> GADTResult<T, true>
case err(T) -> GADTResult<T, false>
}
func f(consume r: GADTResult<Int, true>) -> GADTResult<Int, true> { r }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn recursive_payload_may_apply_static_argument_to_own_head() {
        let t = super::tests::check(
            "// no-core
enum Chain<T, static Flag: Bool> {
case leaf(T)
case nest(Chain<T, true>)
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn struct_field_may_apply_static_argument_to_own_head() {
        let t = super::tests::check(
            "// no-core
struct Grid<static N: Int> {
let shrink: (Grid<0>) -> Int
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_domain_admits_fieldless_enum_declared_later() {
        // The domain check reads the enum's variant shapes, which are
        // header facts — declaration order must not matter.
        let t = super::tests::check(
            "// no-core
struct Flagged<static C: Color> {}
enum Color {
case red
case blue
}
func f(consume s: Flagged<Color.red>) -> Flagged<Color.red> { s }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_domain_rejects_payload_enum_declared_later() {
        let t = super::tests::check(
            "// no-core
struct Flagged<static C: Color> {}
enum Color {
case rgb(Int)
}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("value type must be Int, Bool, or a fieldless enum")),
            "{errors:?}"
        );
    }

    #[test]
    fn self_reference_pads_declared_static_default() {
        // `Tree<T>` inside the enum's own body must pad to `Tree<T, 0>`,
        // so `nest`'s payload unifies with an explicit `Tree<Int, 0>`.
        let t = super::tests::check(
            "// no-core
enum Tree<T, static Depth: Int = 0> {
case leaf(T)
case nest(Tree<T>)
}
func takes(x: Tree<Int, 0>) -> Int { 1 }
func f(t: Tree<Int>) -> Int {
    match t {
        .nest(inner) -> takes(x: inner),
        .leaf(_) -> 0
    }
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn self_referential_static_equation_reports_unsatisfiable() {
        // `α ~ α + 1` cancels to `1 = 0`: plain unsatisfiable arithmetic,
        // not an infinite type.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func grow<static N: Int>(consume g: Grid<N>) -> Grid<N + 1> { Grid() }
func same<static M: Int>(a: Grid<M>, b: Grid<M>) -> Int { 1 }
func use() -> Int {
    let g = Grid()
    same(a: grow(g: g), b: g)
}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(!errors.is_empty(), "expected an error, got clean");
        assert!(
            errors.iter().all(|error| !error.contains("nfinite")),
            "should not report an infinite type: {errors:?}"
        );
    }

    #[test]
    fn unresolved_static_argument_gets_targeted_diagnostic() {
        // Nothing pins N: not a generic inference failure but an
        // underdetermined static argument (ADR 0035 §5).
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func make<static N: Int>() -> Grid<N> { Grid() }
func use() -> Int {
    let g = make()
    1
}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Cannot infer this static argument")),
            "{errors:?}"
        );
    }

    #[test]
    fn protocol_static_arguments_prove_bounds() {
        let t = super::tests::check(
            "// no-core
protocol Sized<static N: Int> {}
struct Cell {}
extend Cell: Sized<1> {}
func need<T>(x: T) -> Int where T: Sized<1> { 1 }
func use(c: Cell) -> Int { need(x: c) }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn protocol_static_argument_mismatch_rejects_conformance() {
        let t = super::tests::check(
            "// no-core
protocol Sized<static N: Int> {}
struct Cell {}
extend Cell: Sized<1> {}
func need<T>(x: T) -> Int where T: Sized<2> { 1 }
func use(c: Cell) -> Int { need(x: c) }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("conform")),
            "{errors:?}"
        );
    }

    #[test]
    fn protocol_static_param_default_applies() {
        let t = super::tests::check(
            "// no-core
protocol Sized<static N: Int = 1> {}
struct Cell {}
extend Cell: Sized {}
func need<T>(x: T) -> Int where T: Sized<1> { 1 }
func use(c: Cell) -> Int { need(x: c) }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn distinct_static_conformances_coexist_and_overlap_rejects() {
        let coexist = super::tests::check(
            "// no-core
protocol Sized<static N: Int> {}
struct Cell {}
extend Cell: Sized<1> {}
extend Cell: Sized<2> {}",
        );
        super::tests::assert_clean(&coexist);

        // ADR 0035 §8: no ordered specialization — a generic row and a
        // concrete row for the same protocol overlap and reject; the
        // concrete one gains no C++-style priority.
        let overlap = super::tests::check(
            "// no-core
protocol Sized<static N: Int> {}
struct Cell {}
extend<static N: Int> Cell: Sized<N> {}
extend Cell: Sized<1> {}",
        );
        let errors = super::tests::type_errors(&overlap);
        assert!(
            errors.iter().any(|error| error.contains("verlap")),
            "{errors:?}"
        );
    }

    #[test]
    fn static_equality_where_clause_proves_and_rejects() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f<static N: Int, static M: Int>(consume g: Grid<N>, h: Grid<M>) -> Grid<M> where N == M { g }",
        );
        super::tests::assert_clean(&t);

        let bare = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f<static N: Int, static M: Int>(consume g: Grid<N>, h: Grid<M>) -> Grid<M> { g }",
        );
        let errors = super::tests::type_errors(&bare);
        assert!(!errors.is_empty(), "expected a mismatch, got clean");
    }

    #[test]
    fn static_equality_given_feeds_entailment() {
        // N == M proves 0 <= M - N.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f<static N: Int, static M: Int>(g: Grid<N>, h: Grid<M>) -> Grid<M - N> where N == M { Grid() }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_equality_against_literal_pins_the_param() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f<static N: Int>(consume g: Grid<N>) -> Grid<3> where N == 3 { g }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_param_value_use_types_as_declared_value_type() {
        // The frontend owns the value typing of a static parameter; the
        // backend must never be the first phase to give `N` a meaning.
        let t = super::tests::check(
            "// no-core
func wrong<static N: Int>() -> Bool { N }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("Bool")),
            "{errors:?}"
        );

        let ok = super::tests::check(
            "// no-core
func width<static N: Int>() -> Int { N }",
        );
        super::tests::assert_clean(&ok);
    }

    #[test]
    fn static_generics_cross_module_boundary() {
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let id_a = ModuleId::External(0);
        let module_a = super::tests::compile_library(
            "A",
            id_a,
            "public struct Grid<static Rows: Int> {}\npublic func grow<static N: Int>(consume g: Grid<N>) -> Grid<N + 1> { Grid() }",
            ModuleEnvironment::default(),
        );

        let mut modules = ModuleEnvironment::default();
        modules.import_compiled(module_a, id_a).unwrap();
        let config = crate::compiling::driver::DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(modules),
            mode: crate::compiling::driver::CompilationMode::Library,
            module_name: "B".to_string(),
            parse_mode: crate::compiling::driver::ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        };
        let driver_b = Driver::new(
            vec![Source::from(
                "use A::{ Grid, grow }\nfunc f(consume g: Grid<4>) -> Grid<5> { grow(g: g) }",
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
    }

    #[test]
    fn enum_case_generics_carry_static_params() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
enum Holder {
	case sized<static K: Int>(Grid<K>)
	case empty
}
func pack(consume g: Grid<3>) -> Holder {
	Holder.sized(g)
}
func unpack(consume h: Holder) -> Int {
	match h {
		.sized(g) -> 1,
		.empty -> 0
	}
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_param_defaults_apply_on_nominals() {
        // ADR 0035 §1: defaults are valid static expressions mentioning
        // only earlier parameters.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int = 4> {}
func f(consume g: Grid) -> Grid<4> { g }
struct Pair<static A: Int, static B: Int = A + 1> {}
func h(consume p: Pair<2>) -> Pair<2, 3> { p }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn func_static_default_applies_when_uninferred() {
        let t = super::tests::check(
            "// no-core
func number<static N: Int = 4>() -> Int { N }
func use() -> Int { number() }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn func_static_default_yields_to_inference() {
        // An inferable argument beats the default (PreferEq semantics).
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func rows<static N: Int = 4>(g: Grid<N>) -> Grid<N> { Grid() }
func use(g: Grid<7>) -> Grid<7> { rows(g: g) }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn constructor_static_default_is_hard() {
        // `Grid()` IS `Grid<4>()`; a use demanding Grid<5> must reject.
        let t = super::tests::check(
            "// no-core
struct Grid<static N: Int = 4> {}
func five(g: Grid<5>) -> Int { 5 }
func use() -> Int {
    let g = Grid()
    five(g: g)
}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(!errors.is_empty(), "expected a mismatch, got clean");

        let ok = super::tests::check(
            "// no-core
struct Grid<static N: Int = 4> {}
func four(g: Grid<4>) -> Int { 4 }
func use() -> Int {
    let g = Grid()
    four(g: g)
}",
        );
        super::tests::assert_clean(&ok);
    }

    #[test]
    fn negative_static_default_rejects_at_declaration() {
        let t = super::tests::check(
            "// no-core
struct Grid<static N: Int = 0 - 1> {}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("nonnegative")),
            "{errors:?}"
        );
    }

    #[test]
    fn forward_referencing_default_rejects_at_declaration() {
        let t = super::tests::check(
            "// no-core
struct Pair<static A: Int = B, static B: Int = 2> {}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("earlier parameters")),
            "{errors:?}"
        );
    }

    #[test]
    fn symbolic_default_materialization_requires_proof() {
        // `Pair<0>` materializes B = 0 - 1: the default is a formed
        // static argument and owes nonnegativity like an explicit one.
        let t = super::tests::check(
            "// no-core
struct Pair<static A: Int, static B: Int = A - 1> {}
func f(consume p: Pair<0>) -> Int { 1 }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );

        // With a positive argument the same default proves.
        let ok = super::tests::check(
            "// no-core
struct Pair<static A: Int, static B: Int = A - 1> {}
func f(consume p: Pair<3>) -> Int { 1 }",
        );
        super::tests::assert_clean(&ok);

        // A generic use demands the proof from the declaration context.
        let generic = super::tests::check(
            "// no-core
struct Pair<static A: Int, static B: Int = A - 1> {}
func f<static K: Int>(consume p: Pair<K>) -> Int { 1 }",
        );
        let errors = super::tests::type_errors(&generic);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );

        let guarded = super::tests::check(
            "// no-core
struct Pair<static A: Int, static B: Int = A - 1> {}
func f<static K: Int>(consume p: Pair<K>) -> Int where 0 < K { 1 }",
        );
        super::tests::assert_clean(&guarded);
    }

    #[test]
    fn static_param_default_mismatch_still_rejects() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int = 4> {}
func f(consume g: Grid) -> Grid<5> { g }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(!errors.is_empty(), "expected a mismatch, got clean");
    }

    #[test]
    fn conformance_head_static_arguments_require_proof() {
        let t = super::tests::check(
            "// no-core
protocol Sized<static N: Int> {}
struct Cell {}
extend Cell: Sized<0 - 1> {}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );

        // A conditional row's context proves its head's obligations.
        let guarded = super::tests::check(
            "// no-core
protocol Sized<static N: Int> {}
struct Grid<static Rows: Int> {}
extend<static N: Int> Grid: Sized<N - 1> where 0 < N {}",
        );
        super::tests::assert_clean(&guarded);
    }

    #[test]
    fn superprotocol_static_arguments_require_proof() {
        let t = super::tests::check(
            "// no-core
protocol Sized<static N: Int> {}
protocol Bad: Sized<0 - 1> {}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );

        // The subprotocol's own params satisfy its super's obligations
        // through the ambient axiom.
        let ok = super::tests::check(
            "// no-core
protocol Sized<static N: Int> {}
protocol Ok<static N: Int>: Sized<N> {}",
        );
        super::tests::assert_clean(&ok);
    }

    #[test]
    fn type_alias_static_arguments_require_proof() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
typealias Bad = Grid<0 - 1>",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );
    }

    #[test]
    fn field_type_formation_requires_nonnegativity_proof() {
        // A field's formation obligations must not vanish just because
        // collection lowered the annotation first.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
struct Shrunk<static N: Int> {
	let g: Grid<N - 1>
}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );
    }

    #[test]
    fn field_type_formation_proves_from_nominal_where_clause() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
struct Shrunk<static N: Int> where 0 < N {
	let g: Grid<N - 1>
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn effect_static_generic_arguments_type_check() {
        let t = super::tests::check(
            "// no-core
effect 'tag<static N: Int>(value: Int) -> Int
@handle 'tag { value in
	'continue value
}
'tag<4>(value: 1)",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn effect_static_generic_argument_kind_mismatch_is_rejected() {
        let t = super::tests::check(
            "// no-core
effect 'tag<static N: Int>(value: Int) -> Int
@handle 'tag { value in
	'continue value
}
'tag<Bool>(value: 1)",
        );
        let errors = super::tests::type_errors(&t);
        assert!(!errors.is_empty(), "expected a kind mismatch, got clean");
    }

    #[test]
    fn extension_method_static_generics_check() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
struct S {}
extend S {
	func f<static N: Int>(consume g: Grid<N - 1>) -> Int where 0 < N { 1 }
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn protocol_where_clause_sees_protocol_params() {
        let t = super::tests::check(
            "// no-core
protocol Good<static N: Int> where 0 < N {}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn requirement_signature_obligations_prove_under_its_own_predicates() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
protocol P {
	func f<static N: Int>(consume g: Grid<N - 1>) -> Int where 0 < N
}",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn requirement_signature_without_positivity_given_is_rejected() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
protocol P {
	func f<static N: Int>(consume g: Grid<N - 1>) -> Int
}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );
    }

    #[test]
    fn constrained_static_in_compound_form_only_is_undetermined() {
        // A is constrained (0 < A) but occurs only inside `C - A`, which
        // no call site can uniquely solve: mention is not determination.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f<static A: Int, static C: Int>(g: Grid<C - A>) -> Int where 0 < A { 1 }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("constrained but not determined")),
            "{errors:?}"
        );
    }

    #[test]
    fn constrained_static_solvable_through_affine_form_is_determined() {
        // A bare occurrence determines A; C is then the only unknown in
        // `C - A` (unit coefficient), so both are determined.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f<static A: Int, static C: Int>(g: Grid<A>, h: Grid<C - A>) -> Int where 0 < A && A <= C { 1 }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn nonlinear_static_multiplication_is_rejected() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f<static N: Int, static M: Int>(g: Grid<N * M>) { }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("literal operand")),
            "{errors:?}"
        );
    }

    #[test]
    fn static_bool_arguments_type_check() {
        let t = super::tests::check(
            "// no-core
struct Flag<static On: Bool> {}
func f(consume flag: Flag<true>) -> Flag<true> { flag }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_bool_argument_mismatch_is_rejected() {
        let t = super::tests::check(
            "// no-core
struct Flag<static On: Bool> {}
func f(consume flag: Flag<true>) -> Flag<false> { flag }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(!errors.is_empty(), "expected a mismatch, got clean");
    }

    #[test]
    fn static_param_infers_from_argument_type() {
        // ADR 0035 §5: a call with Grid<4> infers N = 4; the affine
        // return Grid<N + 1> then solves to Grid<5>.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func grow<static N: Int>(g: Grid<N>) -> Grid<N + 1> { Grid() }
func use(g: Grid<4>) -> Grid<5> { grow(g: g) }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_param_inference_mismatch_is_rejected() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func grow<static N: Int>(g: Grid<N>) -> Grid<N + 1> { Grid() }
func use(g: Grid<4>) -> Grid<6> { grow(g: g) }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(!errors.is_empty(), "expected a mismatch, got clean");
    }

    #[test]
    fn explicit_static_type_argument_on_call() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func make<static N: Int>() -> Grid<N> { Grid() }
func use() -> Grid<4> { make<4>() }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_where_clause_proves_nonnegativity_of_subtraction() {
        // ADR 0035 §2: `Count - 1` needs a context proving `0 < Count`.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func shrink<static Count: Int>(g: Grid<Count>) -> Grid<Count - 1> where 0 < Count { Grid() }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_subtraction_without_positivity_given_is_rejected() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func shrink<static Count: Int>(g: Grid<Count>) -> Grid<Count - 1> { Grid() }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );
    }

    #[test]
    fn static_where_clause_obligation_holds_at_call() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func first<static Count: Int>(g: Grid<Count>) -> Int where 0 < Count { 1 }
func use(g: Grid<3>) -> Int { first(g: g) }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_where_clause_obligation_fails_at_call() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func first<static Count: Int>(g: Grid<Count>) -> Int where 0 < Count { 1 }
func use(g: Grid<0>) -> Int { first(g: g) }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );
    }

    #[test]
    fn static_ordering_givens_chain_transitively() {
        // 0 <= C - A follows from A <= B and B <= C only by combining
        // both givens: (C - B) + (B - A) >= 0.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func mid<static A: Int, static B: Int, static C: Int>(g: Grid<A>, h: Grid<B>, i: Grid<C>) -> Grid<C - A> where A <= B && B <= C { Grid() }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn undetermined_static_param_is_rejected() {
        // The determined-variable rule covers static params: B is
        // constrained but appears nowhere in the exposed type.
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func mid<static A: Int, static B: Int, static C: Int>(g: Grid<C - A>) -> Int where A <= B && B <= C { 1 }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("constrained but not determined")),
            "{errors:?}"
        );
    }

    #[test]
    fn negative_closed_static_argument_is_rejected() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f(g: Grid<0 - 1>) { }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("static predicate")),
            "{errors:?}"
        );
    }

    #[test]
    fn explicit_negative_static_argument_reports_once() {
        // The explicit argument owns its formation obligation; the
        // instantiation hole must not double-report it (constructor,
        // call, and effect forms alike).
        let constructor = super::tests::check(
            "// no-core
struct Grid<static N: Int> {}
Grid<0 - 1>()
()",
        );
        let call = super::tests::check(
            "// no-core
func width<static N: Int>() -> Int { N }
width<0 - 1>()
()",
        );
        let effect = super::tests::check(
            "// no-core
effect 'tag<static N: Int>(value: Int) -> Int
@handle 'tag { value in
	'continue value
}
'tag<0 - 1>(value: 1)
()",
        );
        for (name, t) in [
            ("constructor", &constructor),
            ("call", &call),
            ("effect", &effect),
        ] {
            let errors = super::tests::type_errors(t);
            let nonneg: Vec<&String> = errors
                .iter()
                .filter(|error| error.contains("static predicate"))
                .collect();
            assert_eq!(
                nonneg.len(),
                1,
                "{name}: expected exactly one formation error, got {errors:?}"
            );
        }
    }

    #[test]
    fn static_enum_case_arguments_type_check() {
        let t = super::tests::check(
            "// no-core
enum Color { case red case green }
struct Paint<static C: Color> {}
func f(consume p: Paint<Color.red>) -> Paint<Color.red> { p }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn unqualified_static_enum_case_arguments_use_the_declared_domain() {
        let t = super::tests::check(
            "// no-core
enum Outcome { case success case failure }
enum Res<T, static O: Outcome> {
case ok(T) -> Res<T, .success>
case err(T) -> Res<T, .failure>
}
func f(consume r: Res<Int, .success>) -> Res<Int, Outcome.success> { r }",
        );
        super::tests::assert_clean(&t);
    }

    #[test]
    fn static_enum_case_argument_mismatch_is_rejected() {
        let t = super::tests::check(
            "// no-core
enum Color { case red case green }
struct Paint<static C: Color> {}
func f(consume p: Paint<Color.red>) -> Paint<Color.green> { p }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(!errors.is_empty(), "expected a mismatch, got clean");
        // Cases render source-oriented (`Color.red`), never as compiler
        // internals (`@Variant(...)`).
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Color.red") && error.contains("Color.green")),
            "{errors:?}"
        );
        assert!(
            !errors.iter().any(|error| error.contains("@Variant")),
            "{errors:?}"
        );
    }

    #[test]
    fn payload_enum_static_param_is_rejected() {
        let t = super::tests::check(
            "// no-core
enum Wrap { case value(Int) }
struct Holder<static W: Wrap> {}",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("value type must be Int, Bool, or a fieldless enum")),
            "{errors:?}"
        );
    }

    #[test]
    fn closed_static_arithmetic_must_fit_i64() {
        let t = super::tests::check(
            "// no-core
struct Grid<static Rows: Int> {}
func f(g: Grid<4611686018427387904 * 4>) { }",
        );
        let errors = super::tests::type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("64-bit") || error.contains("out")),
            "{errors:?}"
        );
    }

    /// ADR 0035 §4: the affine normalizer makes these pairs definitionally
    /// equal, and closed arithmetic reduces before identity.
    #[test]
    fn static_int_normalization_canonicalizes_affine_forms() {
        use crate::compiling::module::ModuleId;
        use crate::name_resolution::symbol::{Symbol, TypeParameterId};
        use crate::types::ty::{StaticAtom, StaticInt, StaticValue, Ty};

        let n = Ty::Param(Symbol::TypeParameter(TypeParameterId::new(
            ModuleId::Current,
            1,
        )));
        let rows = Ty::Param(Symbol::TypeParameter(TypeParameterId::new(
            ModuleId::Current,
            2,
        )));
        let aff = |ty: &Ty| StaticInt::from_ty(ty).expect("affine-readable");

        // N + 1 == 1 + N
        let n_plus_1 = aff(&n).add(&StaticInt::constant(1)).into_ty();
        let one_plus_n = StaticInt::constant(1).add(&aff(&n)).into_ty();
        assert_eq!(n_plus_1, one_plus_n);

        // 2 * N == N + N
        let two_n = aff(&n).scale(&2.into()).into_ty();
        let n_plus_n = aff(&n).add(&aff(&n)).into_ty();
        assert_eq!(two_n, n_plus_n);

        // Rows * 4 + 4 == 4 * (Rows + 1)
        let lhs = aff(&rows)
            .scale(&4.into())
            .add(&StaticInt::constant(4))
            .into_ty();
        let rhs = aff(&rows)
            .add(&StaticInt::constant(1))
            .scale(&4.into())
            .into_ty();
        assert_eq!(lhs, rhs);

        // 2 + 2 reduces to the closed value 4.
        let closed = StaticInt::constant(2)
            .add(&StaticInt::constant(2))
            .into_ty();
        assert_eq!(closed, Ty::Static(StaticValue::Int(StaticInt::constant(4))));

        // 0 + 1·N collapses back to the bare parameter, so arithmetic-free
        // arguments stay ordinary generic arguments.
        assert_eq!(aff(&n).into_ty(), n);
        let roundabout = aff(&n)
            .add(&StaticInt::constant(3))
            .sub(&StaticInt::constant(3))
            .into_ty();
        assert_eq!(roundabout, n);

        // N - N cancels to the closed value 0.
        let cancelled = aff(&n).sub(&aff(&n)).into_ty();
        assert_eq!(
            cancelled,
            Ty::Static(StaticValue::Int(StaticInt::constant(0)))
        );

        // Substitution renormalizes: substituting N := 3 into N + 1 gives
        // the closed value 4 (the fold path used by instantiation).
        use rustc_hash::FxHashMap;
        let Ty::Param(n_symbol) = n else {
            unreachable!()
        };
        let mut subst: FxHashMap<_, _> = FxHashMap::default();
        subst.insert(
            n_symbol,
            Ty::Static(StaticValue::Int(StaticInt::constant(3))),
        );
        let substituted = n_plus_1.substitute(&subst, &FxHashMap::default(), &FxHashMap::default());
        assert_eq!(
            substituted,
            Ty::Static(StaticValue::Int(StaticInt::constant(4)))
        );

        // Terms are kept sorted regardless of insertion order.
        let n_atom = StaticAtom::Param(n_symbol);
        let Ty::Param(rows_symbol) = rows else {
            unreachable!()
        };
        let rows_atom = StaticAtom::Param(rows_symbol);
        let ab = StaticInt::atom(n_atom).add(&StaticInt::atom(rows_atom));
        let ba = StaticInt::atom(rows_atom).add(&StaticInt::atom(n_atom));
        assert_eq!(ab, ba);
    }
}

#[cfg(test)]
mod nested_types {
    use super::tests::{assert_clean, check, ty_of, type_errors};

    // A type declared inside a nominal body captures the enclosing type's
    // generic context (the C#/Swift model): its parameter list is the
    // enclosing params followed by its own, so `Res<T>.A` is implicitly
    // parameterized by `T`. Explicit generics on an expression-position
    // base (`Res<Int>.A.one(1)`) are a pre-existing parser gap shared
    // with flat enums (`Opt<Int>.some(1)`), so these tests pin captured
    // args through annotations.

    #[test]
    fn nested_enum_declarations_register() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tcase success\n\t\tcase failure\n\t}\n\n\tcase wrap(T)\n}\nlet x: Res<Int>.A = Res.A.success\nmatch x {\n\t.success -> 1,\n\t.failure -> 2\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn nested_enum_captures_outer_generics() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tcase one(T)\n\t}\n}\nlet x: Res<Int>.A = Res.A.one(1)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Res.A<Int>");
    }

    #[test]
    fn qualified_nested_type_pins_captured_args() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tcase one(T)\n\t}\n}\nlet x: Res<Int>.A = Res.A.one(true)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Int") && error.contains("Bool")),
            "expected the captured arg to pin the payload, got {errors:?}"
        );
    }

    #[test]
    fn bare_nested_name_in_outer_body_captures_current_self_args() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tcase one(T)\n\t}\n\n\tcase wrap(T)\n\n\tfunc first(consume value: T) -> A {\n\t\tA.one(value)\n\t}\n}\nlet x = Res.wrap(1).first(value: 2)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Res.A<Int>");
    }

    #[test]
    fn nested_variants_resolve_from_leading_dots() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tcase one(T)\n\t\tcase none\n\t}\n}\nfunc id<T>(consume x: T) -> T { x }\nlet x: Res<Int>.A = id(x: Res.A.one(1))\nlet y: Res<Bool>.A = .none",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Res.A<Int>");
        assert_eq!(ty_of(&t, "y"), "Res.A<Bool>");
    }

    #[test]
    fn nested_types_nest_recursively() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tenum B {\n\t\t\tcase leaf(T)\n\t\t}\n\t}\n}\nlet x: Res<Int>.A.B = Res.A.B.leaf(1)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Res.A.B<Int>");
    }

    #[test]
    fn nested_structs_capture_outer_generics() {
        let t = check(
            "// no-core\nstruct Outer<T> {\n\tstruct Inner {\n\t\tlet item: T\n\t}\n\n\tlet value: T\n}\nlet x: Outer<Int>.Inner = Outer.Inner(item: 1)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Outer.Inner<Int>");
    }

    #[test]
    fn nested_type_arity_counts_only_its_own_params() {
        // The captured slot is invisible: `A` declares no generics of its
        // own, so applying it to an explicit argument is an arity error
        // measured against zero, not against the flattened list.
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tcase one(T)\n\t}\n}\nlet x: Res<Int>.A<Int> = Res.A.one(1)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("expected 0, found 1")),
            "expected an own-params arity error, got {errors:?}"
        );
    }

    #[test]
    fn outer_where_clause_carries_to_nested_type() {
        let t = check(
            "// no-core\nprotocol P {}\nextend Int: P {}\nenum Res<T> where T: P {\n\tenum A {\n\t\tcase one(T)\n\t}\n}\nlet bad: Res<Bool>.A = Res.A.one(true)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Bool does not conform to P")),
            "expected the outer bound to burden the nested application, got {errors:?}"
        );
    }

    #[test]
    fn outer_where_clause_accepts_conforming_nested_args() {
        let t = check(
            "// no-core\nprotocol P {}\nextend Int: P {}\nenum Res<T> where T: P {\n\tenum A {\n\t\tcase one(T)\n\t}\n}\nlet good: Res<Int>.A = Res.A.one(1)",
        );
        assert_clean(&t);
    }

    // ----- Explicit base type args in expression position ----------------
    // `Type<Args>.member` specializes the type reference itself: the args
    // pin the head's instantiation, whether the member is a variant call,
    // a payload-less variant, or a nested type's construction.

    #[test]
    fn explicit_base_args_pin_variant_calls() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nlet x = Opt<Int>.some(1)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Opt<Int>");
    }

    #[test]
    fn explicit_base_args_reject_mismatched_payloads() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nlet x = Opt<Int>.some(true)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Int") && error.contains("Bool")),
            "expected the explicit arg to pin the payload, got {errors:?}"
        );
    }

    #[test]
    fn explicit_base_args_pin_payloadless_variants() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nlet x = Opt<Int>.none",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Opt<Int>");
    }

    #[test]
    fn explicit_base_args_reject_over_arity() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nlet x = Opt<Int, Bool>.some(1)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("expected 1, found 2")),
            "expected an arity error, got {errors:?}"
        );
    }

    #[test]
    fn explicit_base_args_pin_nested_variants() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tcase one(T)\n\t\tcase none\n\t}\n}\nlet x = Res<Int>.A.one(1)\nlet y = Res<Bool>.A.none",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Res.A<Int>");
        assert_eq!(ty_of(&t, "y"), "Res.A<Bool>");
    }

    #[test]
    fn explicit_base_args_pin_nested_struct_constructions() {
        let t = check(
            "// no-core\nstruct Outer<T> {\n\tstruct Inner {\n\t\tlet item: T\n\t}\n\n\tlet value: T\n}\nlet x = Outer<Int>.Inner(item: 1)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Outer.Inner<Int>");
    }

    // ----- Qualified pattern heads ---------------------------------------

    #[test]
    fn qualified_pattern_heads_name_nested_enums() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tcase one(T)\n\t\tcase none\n\t}\n}\nfunc f(x: Res<Int>.A) -> Int {\n\tmatch x {\n\t\tRes.A.one(v) -> v,\n\t\tRes.A.none -> 0\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn bare_specialized_references_parse_and_reject_value_use() {
        let t =
            check("// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nlet x = Opt<Int>");
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("type names as values")),
            "expected a graceful type error, got {errors:?}"
        );
    }

    #[test]
    fn specialized_member_segments_pin_their_own_params() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A<U> {\n\t\tcase pair(T, U)\n\t}\n}\nlet x = Res<Int>.A<Bool>.pair(1, true)\nlet y = Res.A<Bool>.pair(1, true)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Res.A<Int, Bool>");
        assert_eq!(ty_of(&t, "y"), "Res.A<Int, Bool>");
    }

    #[test]
    fn specialized_member_segments_respect_own_arity() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A<U> {\n\t\tcase pair(T, U)\n\t}\n}\nlet x = Res<Int>.A<Bool, Int>.pair(1, true)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("expected 1, found 2")),
            "expected a per-segment arity error, got {errors:?}"
        );
    }

    #[test]
    fn call_site_args_fill_the_final_segment() {
        let t = check(
            "// no-core\nstruct Outer<T> {\n\tstruct Inner<U> {\n\t\tlet a: T\n\t\tlet b: U\n\t}\n\n\tlet value: T\n}\nlet x = Outer<Int>.Inner<Bool>(a: 1, b: true)",
        );
        assert_clean(&t);
        assert_eq!(ty_of(&t, "x"), "Outer.Inner<Int, Bool>");
    }

    #[test]
    fn variant_patterns_accept_head_generics() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc f(x: Opt<Int>) -> Int {\n\tmatch x {\n\t\tOpt<Int>.some(v) -> v,\n\t\tOpt.none -> 0\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn variant_pattern_head_generics_must_match_the_scrutinee() {
        let t = check(
            "// no-core\nenum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nfunc f(x: Opt<Int>) -> Int {\n\tmatch x {\n\t\tOpt<Bool>.some(v) -> 1,\n\t\tOpt.none -> 0\n\t}\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|error| error.contains("Int") && error.contains("Bool")),
            "expected the pattern head args to conflict with the scrutinee, got {errors:?}"
        );
    }

    #[test]
    fn qualified_struct_pattern_heads_resolve() {
        let t = check(
            "// no-core\nstruct Outer<T> {\n\tstruct Inner {\n\t\tlet item: T\n\t}\n\n\tlet value: T\n}\nfunc f(consume x: Outer<Int>.Inner) -> Int {\n\tmatch x {\n\t\tOuter.Inner { item } -> item\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn qualified_struct_pattern_heads_accept_generics() {
        let t = check(
            "// no-core\nstruct Outer<T> {\n\tstruct Inner {\n\t\tlet item: T\n\t}\n\n\tlet value: T\n}\nfunc f(consume x: Outer<Int>.Inner) -> Int {\n\tmatch x {\n\t\tOuter<Int>.Inner { item } -> item\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn qualified_pattern_heads_reject_unknown_variants() {
        let t = check(
            "// no-core\nenum Res<T> {\n\tenum A {\n\t\tcase one(T)\n\t}\n}\nfunc f(x: Res<Int>.A) -> Int {\n\tmatch x {\n\t\tRes.A.nope(v) -> v\n\t}\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|error| error.contains("nope")),
            "expected an unknown-variant diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn enforces_labels_on_direct_calls() {
        // ADR 0041: a normal argument must have exactly the declared label.
        let t = check("func id(x: Int) -> Int {\n\tx\n}\nid(x: 1)");
        assert_clean(&t);

        let t = check("func id(x: Int) -> Int {\n\tx\n}\nid(1)");
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Missing argument label 'x'")),
            "{errors:?}"
        );

        let t = check("func id(x: Int) -> Int {\n\tx\n}\nid(other: 1)");
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Expected argument label 'x', found 'other'")),
            "{errors:?}"
        );
    }

    #[test]
    fn enforces_omitted_labels() {
        // `_` declares positional calling; written labels are unexpected.
        let t = check("func id(_ x: Int) -> Int {\n\tx\n}\nid(1)");
        assert_clean(&t);

        let t = check("func id(_ x: Int) -> Int {\n\tx\n}\nid(x: 1)");
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Unexpected argument label 'x'")),
            "{errors:?}"
        );

        let t = check("func id(_ x: Int) -> Int {\n\tx\n}\nid(_: 1)");
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Unexpected argument label '_'")),
            "{errors:?}"
        );
    }

    #[test]
    fn two_name_params_use_the_external_label() {
        let t = check("func split(foo fizz: Int) -> Int {\n\tfizz\n}\nsplit(foo: 1)");
        assert_clean(&t);

        let t = check("func split(foo fizz: Int) -> Int {\n\tfizz\n}\nsplit(fizz: 1)");
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Expected argument label 'foo', found 'fizz'")),
            "{errors:?}"
        );
    }

    #[test]
    fn function_values_erase_labels() {
        // Indirect calls are positional; a written label is unexpected.
        let t = check("func id(value: Int) -> Int {\n\tvalue\n}\nlet fn = id\nfn(1)");
        assert_clean(&t);

        let t = check("func id(value: Int) -> Int {\n\tvalue\n}\nlet fn = id\nfn(value: 1)");
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Unexpected argument label 'value'")),
            "{errors:?}"
        );

        // Callback parameters are indirect calls too.
        let t = check(
            "func apply(callback: (Int) -> Int) -> Int {\n\tcallback(1)\n}\napply(callback: func(n: Int) -> Int {\n\tn\n})",
        );
        assert_clean(&t);
    }

    #[test]
    fn enforces_labels_on_method_calls() {
        let t = check(
            "struct Point {\n\tlet x: Int\n\n\tfunc scaled(by factor: Int) -> Int {\n\t\tfactor\n\t}\n}\nfunc use(p: Point) -> Int {\n\tp.scaled(by: 2)\n}",
        );
        assert_clean(&t);

        let t = check(
            "struct Point {\n\tlet x: Int\n\n\tfunc scaled(by factor: Int) -> Int {\n\t\tfactor\n\t}\n}\nfunc use(p: Point) -> Int {\n\tp.scaled(2)\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Missing argument label 'by'")),
            "{errors:?}"
        );
    }

    #[test]
    fn arity_failures_suppress_label_cascades() {
        let t = check("func id(x: Int) -> Int {\n\tx\n}\nid(1, 2)");
        let errors = type_errors(&t);
        assert!(errors.iter().any(|e| e.contains("arguments")), "{errors:?}");
        assert!(
            !errors.iter().any(|e| e.contains("argument label")),
            "label errors must not cascade after arity errors: {errors:?}"
        );
    }

    #[test]
    fn trailing_blocks_satisfy_labeled_final_params() {
        // The trailing block omits the final label by syntax; preceding
        // parenthesized arguments keep their labels.
        let t = check(
            "func map(count: Int, transform fn: (Int) -> Int) -> Int {\n\tfn(count)\n}\nmap(count: 1) { $0 }",
        );
        assert_clean(&t);

        let t = check(
            "func map(count: Int, transform fn: (Int) -> Int) -> Int {\n\tfn(count)\n}\nmap(1) { $0 }",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Missing argument label 'count'")),
            "{errors:?}"
        );
    }

    #[test]
    fn label_overloads_select_by_full_name() {
        // ADR 0041: fizz(a:) and fizz(b:) coexist; calls select by labels
        // before ordinary type checking.
        let t = check(
            "// no-core\nfunc fizz(a: Int) -> Int {\n\ta\n}\nfunc fizz(b: Bool) -> Bool {\n\tb\n}\nlet x: Int = fizz(a: 1)\nlet y: Bool = fizz(b: true)",
        );
        assert_clean(&t);
    }

    #[test]
    fn local_label_overloads_select_by_full_name() {
        let t = check(
            "// no-core\nfunc run() -> Int {\n\tfunc fizz(a: Int) -> Int {\n\t\ta\n\t}\n\tfunc fizz(b: Bool) -> Int {\n\t\t0\n\t}\n\tfizz(a: 1) + fizz(b: true)\n}",
        );
        assert_clean(&t);
    }

    fn all_diagnostics(
        driver: &crate::compiling::driver::Driver<crate::compiling::driver::Typed>,
    ) -> Vec<String> {
        driver
            .phase
            .diagnostics
            .iter()
            .map(|d| format!("{d:?}"))
            .collect()
    }

    #[test]
    fn duplicate_full_callable_names_are_rejected() {
        // Parameter types and binder names do not distinguish declarations.
        let t = check(
            "// no-core\nfunc fizz(_ a: Int) -> Int {\n\ta\n}\nfunc fizz(_ b: Bool) -> Int {\n\t0\n}\nfizz(1)",
        );
        let diagnostics = all_diagnostics(&t);
        assert!(
            diagnostics
                .iter()
                .any(|d| d.contains("DuplicateDeclaration")),
            "expected a duplicate-declaration diagnostic, got {diagnostics:?}"
        );
    }

    #[test]
    fn ambiguous_bare_overload_references_error() {
        // A bare reference resolves only when the set has one callable.
        let t = check(
            "// no-core\nfunc fizz(a: Int) -> Int {\n\ta\n}\nfunc fizz(b: Bool) -> Bool {\n\tb\n}\nlet f = fizz",
        );
        let diagnostics = all_diagnostics(&t);
        assert!(
            diagnostics.iter().any(|d| d.contains("AmbiguousCallable")),
            "expected an ambiguous-reference diagnostic, got {diagnostics:?}"
        );
    }

    #[test]
    fn overload_miss_recovers_to_unique_arity_candidate() {
        // No exact label match, one same-arity candidate: recover to it and
        // report its label mismatch (no cascade, no guessing among many).
        let t = check(
            "// no-core\nfunc fizz(a: Int) -> Int {\n\ta\n}\nfunc fizz(c: Int, d: Int) -> Int {\n\tc\n}\nfizz(zz: 1)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Expected argument label 'a', found 'zz'")),
            "{errors:?}"
        );
    }

    #[test]
    fn method_label_overloads_select_by_full_name() {
        // ADR 0041: scaled(by:) and scaled(times:) coexist on one type;
        // instance and static calls select by written labels.
        let t = check(
            "// no-core\nstruct P {\n\tlet x: Int\n\n\tfunc scaled(by factor: Int) -> Int {\n\t\tfactor\n\t}\n\n\tfunc scaled(times count: Bool) -> Bool {\n\t\tcount\n\t}\n\n\tstatic func make(x: Int) -> Int {\n\t\tx\n\t}\n\n\tstatic func make(flag: Bool) -> Bool {\n\t\tflag\n\t}\n}\nfunc use(p: P) -> Int {\n\tlet a: Int = p.scaled(by: 2)\n\tlet b: Bool = p.scaled(times: true)\n\tlet c: Int = P.make(x: 1)\n\tlet d: Bool = P.make(flag: true)\n\ta\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn duplicate_method_full_names_are_rejected() {
        let t = check(
            "// no-core\nstruct P {\n\tlet x: Int\n\n\tfunc scaled(by factor: Int) -> Int {\n\t\tfactor\n\t}\n\n\tfunc scaled(by count: Int) -> Int {\n\t\tcount\n\t}\n}\nP(x: 1).scaled(by: 2)",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("scaled(by:)")),
            "expected a duplicate-callable diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn ambiguous_bare_method_references_error() {
        // A bare member reference cannot disambiguate an overload set.
        let t = check(
            "// no-core\nstruct P {\n\tlet x: Int\n\n\tfunc scaled(by factor: Int) -> Int {\n\t\tfactor\n\t}\n\n\tfunc scaled(times count: Bool) -> Bool {\n\t\tcount\n\t}\n}\nfunc use(p: P) -> Int {\n\tlet f = p.scaled\n\tp.x\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("mbiguous")),
            "expected an ambiguity diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn overloaded_conformance_methods_witness_by_full_name() {
        // A conformance body may overload a base name; the candidate whose
        // labels agree with the requirement witnesses, the other is
        // inherent.
        let t = check(
            "// no-core\nprotocol Greeter {\n\tfunc greet(name: Bool) -> Bool\n}\nstruct S {}\nextend S: Greeter {\n\tfunc greet(name: Bool) -> Bool {\n\t\tname\n\t}\n\n\tfunc greet(loud flag: Bool) -> Bool {\n\t\tflag\n\t}\n}\nfunc use(s: S) -> Bool {\n\ts.greet(name: true) == s.greet(loud: false)\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_head_extend_non_witness_members_become_defaults() {
        // Option 2 for `extend P: Q`: a body method that witnesses no Q
        // requirement is a protocol-extension default on P — declared
        // once, dispatchable on every conforming type.
        let t = check(
            "// no-core\nprotocol Show2 {\n\tfunc show2() -> Int\n}\nprotocol Pretty {\n\tfunc pretty(indent: Int) -> Int\n}\nextend Show2: Pretty {\n\tfunc pretty(indent: Int) -> Int {\n\t\tself.show2() + indent\n\t}\n\n\tfunc pretty(compact flag: Bool) -> Int {\n\t\tself.show2()\n\t}\n}\nstruct S {}\nextend S: Show2 {\n\tfunc show2() -> Int {\n\t\t1\n\t}\n}\nfunc use(s: S) -> Int {\n\ts.pretty(indent: 2) + s.pretty(compact: true)\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn protocol_head_extend_defaults_collide_on_full_names() {
        // A non-witness member whose full name matches an existing
        // requirement of the head protocol is a duplicate, not a default.
        let t = check(
            "// no-core\nprotocol Show2 {\n\tfunc show2() -> Int\n}\nprotocol Pretty {\n\tfunc pretty(indent: Int) -> Int\n}\nextend Show2: Pretty {\n\tfunc pretty(indent: Int) -> Int {\n\t\tself.show2() + indent\n\t}\n\n\tfunc show2() -> Int {\n\t\t0\n\t}\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("show2()")),
            "expected a duplicate-callable diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn requirement_label_overloads_select_by_full_name() {
        // ADR 0041: protocol requirements use the same full-name rule;
        // concrete and generic dispatch select by written labels.
        let t = check(
            "// no-core\nprotocol Greeter {\n\tfunc greet(name: Bool) -> Bool\n\tfunc greet(loud flag: Bool) -> Bool\n}\nstruct S {}\nextend S: Greeter {\n\tfunc greet(name: Bool) -> Bool {\n\t\tname\n\t}\n\n\tfunc greet(loud flag: Bool) -> Bool {\n\t\tflag\n\t}\n}\nfunc direct(s: S) -> Bool {\n\ts.greet(name: true) == s.greet(loud: false)\n}\nfunc generic<T: Greeter>(x: T) -> Bool {\n\tx.greet(name: true) == x.greet(loud: false)\n}\ngeneric(x: S())",
        );
        assert_clean(&t);
    }

    #[test]
    fn duplicate_requirement_full_names_are_rejected() {
        let t = check(
            "// no-core\nprotocol Greeter {\n\tfunc greet(name: Bool) -> Bool\n\tfunc greet(name other: Bool) -> Bool\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("greet(name:)")),
            "expected a duplicate-callable diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn init_overloads_select_by_label_sequence() {
        // ADR 0041: initializer selection uses the declared label sequence,
        // not arity alone.
        let t = check(
            "// no-core\nstruct P {\n\tlet x: Int\n\n\tinit(x: Int) {\n\t\tself.x = x\n\t}\n\n\tinit(flag: Bool) {\n\t\tself.x = 0\n\t}\n}\nlet a: P = P(x: 1)\nlet b: P = P(flag: true)",
        );
        assert_clean(&t);
    }

    #[test]
    fn duplicate_init_full_names_are_rejected() {
        let t = check(
            "// no-core\nstruct P {\n\tlet x: Int\n\n\tinit(x: Int) {\n\t\tself.x = x\n\t}\n\n\tinit(x other: Int) {\n\t\tself.x = other\n\t}\n}\nP(x: 1)",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("init(x:)")),
            "expected a duplicate-callable diagnostic naming init(x:), got {errors:?}"
        );
    }

    #[test]
    fn witness_full_names_must_agree() {
        // A witness whose labels differ from the requirement's does not
        // satisfy it (ADR 0041).
        let t = check(
            "// no-core\nprotocol Greeter {\n\tfunc greet(name: Bool) -> Bool\n}\nstruct S {}\nextend S: Greeter {\n\tfunc greet(_ name: Bool) -> Bool {\n\t\tname\n\t}\n}",
        );
        let errors = type_errors(&t);
        assert!(
            errors.iter().any(|e| e.contains("greet")),
            "expected a witness mismatch diagnostic, got {errors:?}"
        );

        let t = check(
            "// no-core\nprotocol Greeter {\n\tfunc greet(name: Bool) -> Bool\n}\nstruct S {}\nextend S: Greeter {\n\tfunc greet(name: Bool) -> Bool {\n\t\tname\n\t}\n}",
        );
        assert_clean(&t);
    }

    #[test]
    fn enforces_labels_on_effect_operations() {
        // Effect names are non-overloadable but their calls obey the same
        // parameter label rules (ADR 0041).
        let t = check(
            "// no-core\neffect 'ask(prompt: Int) -> Int\n@handle 'ask { v in 'continue v }\n'ask(prompt: 1)",
        );
        assert_clean(&t);

        let t = check(
            "// no-core\neffect 'ask(prompt: Int) -> Int\n@handle 'ask { v in 'continue v }\n'ask(1)",
        );
        let errors = type_errors(&t);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Missing argument label 'prompt'")),
            "{errors:?}"
        );
    }

    #[test]
    fn public_overloads_cross_the_module_boundary() {
        // ADR 0041: public declarations with the same base but different
        // full callable names coexist in the export table; the importer
        // gets the whole overload set.
        use super::tests::compile_library;
        use crate::compiling::driver::{Driver, Source};
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let id_a = ModuleId::External(0);
        let module_a = compile_library(
            "A",
            id_a,
            "public func fizz(a: Int) -> Int {\n\ta\n}\npublic func fizz(flag: Bool) -> Bool {\n\tflag\n}",
            ModuleEnvironment::default(),
        );

        let mut modules = ModuleEnvironment::default();
        modules.import_compiled(module_a, id_a).unwrap();
        let config = crate::compiling::driver::DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(modules),
            mode: crate::compiling::driver::CompilationMode::Library,
            module_name: "B".to_string(),
            parse_mode: crate::compiling::driver::ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        };
        let driver_b = Driver::new(
            vec![Source::from(
                "use A::{ fizz }\nfunc f() -> Int {\n\tfizz(a: 1)\n}\nfunc g() -> Bool {\n\tfizz(flag: true)\n}",
            )],
            config,
        );
        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        assert_eq!(type_errors(&typed), Vec::<String>::new());
    }

    #[test]
    fn imported_bare_overload_references_are_ambiguous() {
        use super::tests::compile_library;
        use crate::compiling::driver::{Driver, Source};
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let id_a = ModuleId::External(0);
        let module_a = compile_library(
            "A",
            id_a,
            "public func fizz(a: Int) -> Int {\n\ta\n}\npublic func fizz(flag: Bool) -> Bool {\n\tflag\n}",
            ModuleEnvironment::default(),
        );

        let mut modules = ModuleEnvironment::default();
        modules.import_compiled(module_a, id_a).unwrap();
        let config = crate::compiling::driver::DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(modules),
            mode: crate::compiling::driver::CompilationMode::Library,
            module_name: "B".to_string(),
            parse_mode: crate::compiling::driver::ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        };
        let driver_b = Driver::new(
            vec![Source::from("use A::{ fizz }\nlet f = fizz")],
            config,
        );
        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        let diagnostics = all_diagnostics(&typed);
        assert!(
            diagnostics.iter().any(|d| d.contains("AmbiguousCallable")),
            "expected an ambiguous-reference diagnostic, got {diagnostics:?}"
        );
    }

    #[test]
    fn duplicate_public_full_names_still_collide() {
        let t = check(
            "// no-core\npublic func fizz(a: Int) -> Int {\n\ta\n}\npublic func fizz(a: Int) -> Int {\n\ta\n}",
        );
        let diagnostics = all_diagnostics(&t);
        assert!(
            diagnostics
                .iter()
                .any(|d| d.contains("DuplicateExport") || d.contains("DuplicateDeclaration")),
            "expected a duplicate diagnostic, got {diagnostics:?}"
        );
    }

    #[test]
    fn callable_contracts_cross_the_module_boundary() {
        // ADR 0041: imported contracts merge alongside imported schemes,
        // surviving module serialization.
        use super::tests::compile_library;
        use crate::compiling::driver::{Driver, Source};
        use crate::compiling::module::{ModuleEnvironment, ModuleId};
        use std::rc::Rc;

        let id_a = ModuleId::External(0);
        let module_a = compile_library(
            "A",
            id_a,
            "public func split(foo fizz) -> Int {\n\tfizz\n}\npublic struct Point {\n\tlet x: Int\n\n\tpublic func scaled(by factor: Int) -> Int {\n\t\tfactor\n\t}\n}",
            ModuleEnvironment::default(),
        );

        let mut modules = ModuleEnvironment::default();
        modules.import_compiled(module_a, id_a).unwrap();
        let config = crate::compiling::driver::DriverConfig {
            module_id: ModuleId::Main,
            modules: Rc::new(modules),
            mode: crate::compiling::driver::CompilationMode::Library,
            module_name: "B".to_string(),
            parse_mode: crate::compiling::driver::ParseMode::Strict,
            preserve_comments: false,
            workspace_root: None,
            source_root: None,
            libraries: Vec::new(),
        };
        let driver_b = Driver::new(
            vec![Source::from(
                "use A::{ split, Point }\nfunc use_them(p: Point) -> Int {\n\tsplit(foo: p.scaled(by: 2))\n}",
            )],
            config,
        );
        let typed = driver_b
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check();
        assert_eq!(type_errors(&typed), Vec::<String>::new());

        let catalog = &typed.phase.program.types().catalog;
        let names: Vec<String> = catalog
            .callable_contracts
            .values()
            .map(|contract| contract.name.to_string())
            .collect();
        assert!(names.contains(&"split(foo:)".to_string()), "{names:?}");
        assert!(names.contains(&"scaled(by:)".to_string()), "{names:?}");
    }

    #[test]
    fn registers_callable_contracts() {
        // ADR 0041: every named callable publishes a full callable name —
        // external labels only, implicit receivers excluded.
        use crate::types::callables::CallableRole;

        let t = check(
            "
            func split(foo fizz) -> Int { fizz }
            func positional(_ value) -> Int { value }

            struct Point {
                let x: Int
                let y: Int

                func scaled(by factor: Int) -> Int { factor }
                static func origin() -> Int { 0 }
                init(fromX x: Int, fromY y: Int) {
                    self.x = x
                    self.y = y
                }
            }

            struct Size {
                let width: Int
                let height: Int
            }

            protocol Greeter {
                func greet(name: String) -> String
            }

            effect 'ask(prompt: String) -> String
            ",
        );

        let catalog = &t.phase.program.types().catalog;
        let contracts: std::collections::HashMap<String, CallableRole> = catalog
            .callable_contracts
            .values()
            .map(|contract| (contract.name.to_string(), contract.role))
            .collect();

        assert_eq!(contracts.get("split(foo:)"), Some(&CallableRole::Function));
        assert_eq!(
            contracts.get("positional(_:)"),
            Some(&CallableRole::Function)
        );
        assert_eq!(
            contracts.get("scaled(by:)"),
            Some(&CallableRole::Method { is_static: false })
        );
        assert_eq!(
            contracts.get("origin()"),
            Some(&CallableRole::Method { is_static: true })
        );
        assert_eq!(
            contracts.get("init(fromX:fromY:)"),
            Some(&CallableRole::Init)
        );
        // The memberwise init's labels are the field names.
        assert_eq!(
            contracts.get("init(width:height:)"),
            Some(&CallableRole::Init)
        );
        assert_eq!(
            contracts.get("greet(name:)"),
            Some(&CallableRole::Requirement)
        );
        assert_eq!(contracts.get("ask(prompt:)"), Some(&CallableRole::Effect));
        // Local binder names never leak into callable names.
        assert!(!contracts.contains_key("split(fizz:)"));
        assert!(
            !contracts.keys().any(|name| name.contains("self")),
            "implicit receivers must stay out of callable names: {contracts:?}"
        );
    }
}
