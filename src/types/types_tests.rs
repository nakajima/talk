#[cfg(test)]
pub mod tests {
    use crate::{
        ast::AST,
        diagnostic::Diagnostic,
        name::Name,
        name_resolution::name_resolver::NameResolved,
        types::{
            passes::{
                dependencies_pass::tests::resolve_dependencies,
                inference_pass::{InferencePass, Inferenced},
            },
            ty::Ty,
            type_error::TypeError,
            type_session::TypeSession,
        },
    };

    fn typecheck(code: &'static str) -> (AST<NameResolved>, TypeSession<Inferenced>) {
        let (ast, session) = typecheck_err(code);
        assert!(
            ast.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            ast.diagnostics
        );
        (ast, session)
    }

    fn typecheck_err(code: &'static str) -> (AST<NameResolved>, TypeSession<Inferenced>) {
        let (mut ast, session) = resolve_dependencies(code);
        let session = InferencePass::perform(session, &mut ast);
        (ast, session)
    }

    fn ty(i: usize, ast: &AST<NameResolved>, session: &TypeSession<Inferenced>) -> Ty {
        session
            .phase
            .types_by_node
            .get(&ast.roots[i].as_stmt().clone().as_expr().id)
            .unwrap()
            .clone()
    }

    #[test]
    fn types_int_literal() {
        let (ast, session) = typecheck("123");
        assert_eq!(ty(0, &ast, &session), Ty::Int);
    }

    #[test]
    fn types_int() {
        let (ast, session) = typecheck("let a = 123; a");
        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn types_float() {
        let (ast, session) = typecheck("let a = 1.23; a");
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Float
        );
    }

    #[test]
    fn types_bool() {
        let (ast, session) = typecheck("let a = true; a ; let b = false ; b");
        assert_eq!(ty(1, &ast, &session), Ty::Bool);
        assert_eq!(ty(3, &ast, &session), Ty::Bool);
    }

    #[test]
    fn monomorphic_let_annotation() {
        let (ast, session) = typecheck(
            r#"
        let a: Int = 123
        a
    "#,
        );
        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn monomorphic_let_annotation_mismatch() {
        let (ast, _session) = typecheck_err(
            r#"
        let a: Bool = 123
        a
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_identity() {
        let (ast, session) = typecheck(
            "
        func identity(x) { x }
        identity(123)
        identity(true)
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[2].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_nested_func() {
        let (ast, session) = typecheck(
            r#"
        func fizz(x) {
            func buzz() { x }
            buzz()
        }

        fizz(123)
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn explicit_generic_function_instantiates() {
        let (ast, session) = typecheck(
            r#"
        func id<T>(x: T) -> T { x }
        id(123)
        id(true)
    "#,
        );

        let call1 = ast.roots[1].as_stmt().clone().as_expr().id;
        let call2 = ast.roots[2].as_stmt().clone().as_expr().id;

        assert_eq!(*session.phase.types_by_node.get(&call1).unwrap(), Ty::Int);
        assert_eq!(*session.phase.types_by_node.get(&call2).unwrap(), Ty::Bool);
    }

    #[test]
    fn generic_function_body_must_respect_its_own_type_vars() {
        let (ast, _session) = typecheck_err(
            r#"
        func bad<T>(x: T) -> T { 0 } // 0 == Int != T
        bad(true)
    "#,
        );
        assert_eq!(
            ast.diagnostics.len(),
            1,
            "didn't get correct diagnostic: {:?}",
            ast.diagnostics
        );
    }

    #[test]
    fn generalizes_locals() {
        let (ast, session) = typecheck(
            "
        func outer() {
            func id(x) { x }
            (id(123), id(true))
        }

        outer()
        ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    fn types_call_let() {
        let (ast, session) = typecheck(
            "
        func id(x) { x }
        let a = id(123)
        let b = id(1.23)
        a
        b
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[3].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[4].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Float
        );
    }

    #[test]
    fn types_nested_identity() {
        let (ast, session) = typecheck(
            "
        func identity(x) { x }
        identity(identity(123))
        identity(identity(true))
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[2].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_multiple_args() {
        let (ast, session) = typecheck(
            "
        func makeTuple(x, y) {
            (x, y)
        }

        makeTuple(123, true)
            ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    fn types_tuple_value() {
        let (ast, session) = typecheck(
            "
        let z = (123, true)
        z
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    #[ignore = "waiting on rows"]
    fn types_tuple_assignment() {
        let (ast, session) = typecheck(
            "
        let z = (123, 1.23)
        let (x, y) = z
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
    }

    #[test]
    fn types_if_expr() {
        let (ast, session) = typecheck(
            "
        let z = if true { 123 } else { 456 }
        z
        ",
        );
        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[1].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
    }

    #[test]
    fn requires_if_expr_cond_to_be_bool() {
        let (ast, _session) = typecheck_err(
            "
        let z = if 123 { 123 } else { 456 }
        z
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn requires_if_expr_arms_to_match() {
        let (ast, _session) = typecheck_err(
            "
        let z = if true { 123 } else { false }
        z
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn requires_if_stmt_cond_to_be_bool() {
        let (ast, _session) = typecheck_err(
            "
        if 123 { 123 } 
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_match() {
        let (ast, session) = typecheck(
            "
        match 123 {
            123 -> true,
            456 -> false
        }
        ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[0].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_match_binding() {
        let (ast, session) = typecheck(
            "
        match 123 {
            a -> a,
        }
        ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[0].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Int
        );
    }

    #[test]
    fn checks_match_pattern_type() {
        assert_eq!(
            typecheck_err(
                "
        match 123 {
            true -> false,
        }
        ",
            )
            .0
            .diagnostics
            .len(),
            1
        );
        assert_eq!(
            typecheck_err(
                "
        match 1.23 {
            123 -> false,
        }
        ",
            )
            .0
            .diagnostics
            .len(),
            1
        );
    }

    #[test]
    fn checks_tuple_match() {
        let (ast, session) = typecheck(
            "
        match (123, true) {
            (a, b) -> (b, a),
        }
        ",
        );

        assert_eq!(
            *session
                .phase
                .types_by_node
                .get(&ast.roots[0].as_stmt().clone().as_expr().id)
                .unwrap(),
            Ty::Tuple(vec![Ty::Bool, Ty::Int])
        );
    }

    #[test]
    fn checks_loop_cond_is_bool() {
        assert_eq!(
            typecheck_err(
                "
        loop 123 {}
        ",
            )
            .0
            .diagnostics
            .len(),
            1
        );
    }

    #[test]
    fn checks_assignment() {
        assert_eq!(
            typecheck_err(
                "
        let bool = true
        bool = 123
        ",
            )
            .0
            .diagnostics
            .len(),
            1
        );
    }

    #[test]
    fn call_time_type_args_are_checked() {
        // Should be a type error because <Bool> contradicts the actual arg 123.
        let (ast, _session) = typecheck_err(
            r#"
        func id<T>(x: T) -> T { x }
        id<Bool>(123)
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1, "expected 1 diagnostic");
    }

    #[test]
    fn match_arms_must_agree_on_result_type() {
        // Arms return Int vs Bool → should be an error.
        let (ast, _session) = typecheck_err(
            r#"
        match 123 {
            123 -> 1,
            456 -> true,
        }
    "#,
        );
        assert_eq!(
            ast.diagnostics.len(),
            1,
            "match arms not constrained to same type"
        );
    }

    #[test]
    fn param_annotation_is_enforced_at_call() {
        let (ast, _session) = typecheck_err(
            r#"
        func f(x: Int) -> Int { x }
        f(true)
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn return_annotation_is_enforced_in_body() {
        let (ast, _session) = typecheck_err(
            r#"
        func f(x: Int) -> Int { true }
        f(1)
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_recursive_func() {
        let (ast, session) = typecheck(
            "
        func fizz(n) {
            if true {
                123
            } else {
                fizz(n)
            }
        }

        fizz(456)
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn recursion_is_monomorphic_within_binding_group() {
        // Polymorphic recursion should NOT be inferred.
        let (ast, _session) = typecheck_err(
            r#"
        func g(x) { 
            // Force a shape change on the recursive call to try to “polymorphically” recurse.
            g( (x, x) ) 
        }
        g(1)
    "#,
        );

        // We expect either an occurs check error or an invalid unification error
        // Both indicate that polymorphic recursion is not allowed
        assert!(
            !ast.diagnostics.is_empty(),
            "expected errors for polymorphic recursion"
        );

        // Check that we have the expected error types
        let has_occurs_check = ast.diagnostics.iter().any(|d| {
            matches!(
                d,
                crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
                    kind: TypeError::OccursCheck(_),
                    ..
                })
            )
        });

        let has_invalid_unification = ast.diagnostics.iter().any(|d| {
            matches!(
                d,
                crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
                    kind: TypeError::InvalidUnification(_, _),
                    ..
                })
            )
        });

        assert!(
            has_occurs_check || has_invalid_unification,
            "expected OccursCheck or InvalidUnification error for polymorphic recursion, got {:?}",
            ast.diagnostics
        );
    }

    #[test]
    #[ignore = "TypeAnnotationKind::Func not implemented"]
    fn func_type_annotation_on_let_is_honored() {
        // Once Func annotations work, this should typecheck and instantiate.
        let (ast, session) = typecheck(
            r#"
        let id: func<T>(T) -> T = func(x) { x }
        (id(123), id(true))
    "#,
        );
        let pair = ast.roots[1].as_stmt().clone().as_expr().id;
        assert_eq!(
            *session.phase.types_by_node.get(&pair).unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    #[ignore = "TypeAnnotationKind::Tuple not implemented"]
    fn tuple_type_annotation_on_let_is_honored() {
        let (ast, session) = typecheck(
            r#"
        let z: (Int, Bool) = (123, true)
        z
    "#,
        );
        let use_id = ast.roots[1].as_stmt().clone().as_expr().id;
        assert_eq!(
            *session.phase.types_by_node.get(&use_id).unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    fn let_generalization_for_value_bindings() {
        let (ast, session) = typecheck(
            r#"
        let id = func(x) { x }
        (id(123), id(true))
    "#,
        );
        let pair = ast.roots[1].as_stmt().clone().as_expr().id;
        assert_eq!(
            *session.phase.types_by_node.get(&pair).unwrap(),
            Ty::Tuple(vec![Ty::Int, Ty::Bool])
        );
    }

    #[test]
    fn types_record_literal() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: true, b: 123, c: 1.23 }
        rec
        "#,
        );

        let Ty::Struct(_, row) = ty(1, &ast, &session) else {
            panic!("did not get record");
        };

        assert_eq!(
            row.close(),
            [
                ("a".into(), Ty::Bool),
                ("b".into(), Ty::Int),
                ("c".into(), Ty::Float),
            ]
            .into()
        );
    }

    #[test]
    fn types_record_type_out_of_order() {
        // shouldn't blow up
        let (ast, session) = typecheck(
            "
        let x: { a: Int, b: Bool } = { b: true, a: 1 }
        x
        ",
        );

        let Ty::Struct(_, row) = ty(1, &ast, &session) else {
            panic!("Didn't get row");
        };

        assert_eq!(
            row.close(),
            [("a".into(), Ty::Int), ("b".into(), Ty::Bool)].into()
        )
    }

    #[test]
    fn types_record_member() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: true, b: 123, c: 1.23 }
        rec.a
        rec.b
        rec.c
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Bool);
        assert_eq!(ty(2, &ast, &session), Ty::Int);
        assert_eq!(ty(3, &ast, &session), Ty::Float);
    }

    #[test]
    fn types_nested_record() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: { b: { c: 1.23 } } }
        rec.a.b.c
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Float);
    }

    #[test]
    fn types_record_pattern_out_of_order() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: 123, b: true }
        match rec {
            { b, a } -> (a, b)
        }
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn types_record_pattern_with_equalities() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: 123, b: true }
        match rec {
            { a: 123, b } -> b
        }
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Bool);
    }

    #[test]
    fn types_nested_record_pattern() {
        let (ast, session) = typecheck(
            r#"
        let rec = { a: 123, b: { c: true } }
        match rec {
            { a, b: { c } } -> c
        }
        "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Bool);
    }

    #[test]
    fn checks_fields_exist() {
        let (ast, _session) = typecheck_err(
            r#"
        let rec = { a: 123, b: true }
        match rec {
            { a, c } -> (a, c)
        }
        "#,
        );

        assert_eq!(
            ast.diagnostics.len(),
            1,
            "did not get diagnostic: {:?}",
            ast.diagnostics
        );
    }

    #[test]
    fn checks_field_types() {
        let (ast, _session) = typecheck_err(
            r#"
        let rec = { a: 123 }
        match rec {
            { a: true } -> ()
        }
        "#,
        );

        assert_eq!(
            ast.diagnostics.len(),
            1,
            "did not get diagnostic: {:?}",
            ast.diagnostics
        );
    }

    /// id over rows should generalize the *row tail* and instantiate independently.
    #[test]
    fn row_id_generalizes_and_instantiates() {
        let (ast, session) = typecheck(
            r#"
        let id = func id(r) { r }
        // project different fields from differently-shaped records
        (id({ a: 1 }).a, id({ b: true }).b)
    "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    /// Simple polymorphic projection: fstA extracts `a` from any record that has it.
    #[test]
    fn row_projection_polymorphic() {
        let (ast, session) = typecheck(
            r#"
        func fstA(r) { r.a }
        (fstA({ a: 1 }), fstA({ a: 2, b: true }))
    "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Int]));
    }

    /// Local `let` that returns an *env row* must NOT generalize its tail.
    /// Matching on a field that isn't known in the env row should fail inside `outer`.
    #[test]
    fn row_env_tail_not_generalized_in_local_let() {
        let (ast, _session) = typecheck_err(
            r#"
        func outer(r) {
            let _x = r.a;               // forces r to have field `a`
            let k  = func() { r };      // returns the *same* env row (no row-generalization)
            match k() {
                { c } -> c              // `c` is not known; should produce one error
            }
        }
        outer({ a: 1 })
    "#,
        );

        // exactly one "missing field" diagnostic
        assert_eq!(ast.diagnostics.len(), 1, "{:?}", ast.diagnostics);
    }

    /// Local `let` with a fresh row in RHS should generalize its row tail.
    /// Using it twice with different shapes must type independently.
    #[test]
    fn row_generalizes_in_local_let_when_fresh() {
        let (ast, session) = typecheck(
            r#"
        func outer() {
            let id = func(r) { r };     // fresh row metas -> generalize to a row param
            (id({ a: 1 }).a, id({ b: true }).b)
        }
        outer()
    "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    /// Instantiation stability: once a row param is instantiated at a call site,
    /// subsequent projections line up with the instantiated fields.
    #[test]
    fn row_instantiation_stability_across_uses() {
        let (ast, session) = typecheck(
            r#"
        let id = func id(r) { r }
        let x  = id({ a: 1, b: true });
        (x.a, x.b)
    "#,
        );

        assert_eq!(ty(2, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    /// Polymorphic consumer: a function requiring presence of `a` should accept any record
    /// with `a`, regardless of extra fields.
    #[test]
    fn row_presence_constraint_is_polymorphic() {
        let (ast, session) = typecheck(
            r#"
        func useA(r) { r.a } // imposes HasField(row_var, "a", Int)
        (useA({ a: 1 }), useA({ a: 2, c: true }))
    "#,
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Int]));
    }

    #[test]
    fn row_meta_levels_prevent_leak() {
        // Outer forces r to be an open record { a: Int | row_var } by projecting r.a.
        // Then local let k = func(){ r } must NOT generalize row_var; match should fail on { c }.
        let (ast, _session) = typecheck_err(
            r#"
        func outer(r) {
            let x = r.a; // creates an internal Row::Var tail for r's row (your ensure_row/projection does this)
            let k = func() { r } // local let; do NOT generalize the outer row var into a Row::Param
            match k() {
                { c } -> c // should be a missing-field error (no 'c' in r)
            }
        }
        outer({ a: 1 })
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_row_type_as_params() {
        let (ast, session) = typecheck(
            "
        func foo(x: { y: Int, z: Bool }) {
            (x.y, x.z)
        }

        foo({ y: 123, z: true })
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn enforces_non_annotated_record() {
        let (ast, _session) = typecheck_err(
            "
        func foo(point) {
            (point.x, point.y)
        }

        foo({ x: 123, z: 123 })
        ",
        );

        assert_eq!(
            ast.diagnostics.len(),
            1,
            "diagnostics: {:?}",
            ast.diagnostics
        );
    }

    #[test]
    fn types_non_annotated_record_param() {
        let (ast, session) = typecheck(
            "
        func foo(x) {
            (x.y, x.z)
        }

        foo({ y: 123, z: 1.23 })
        foo({ y: 123, z: 123 })
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Float]));
        assert_eq!(ty(2, &ast, &session), Ty::Tuple(vec![Ty::Int, Ty::Int]));
    }

    #[test]
    fn enforces_row_type_as_params() {
        let (ast, _session) = typecheck_err(
            "
        func foo(x: { y: Int, z: Bool }) {
            (x.y, x.z)
        }

        foo({ y: 123 })
        ",
        );

        assert_eq!(
            ast.diagnostics.len(),
            1,
            "diagnostics: {:?}",
            ast.diagnostics
        );
    }

    #[test]
    fn types_struct_constructor() {
        let (ast, session) = typecheck(
            "
        struct Person {
            let age: Int
            let height: Float
        }

        Person(age: 123, height: 1.23)
        ",
        );

        let Ty::Struct(Some(Name::Resolved(..)), row) = ty(1, &ast, &session) else {
            panic!("didn't get struct");
        };

        assert_eq!(
            row.close(),
            [("age".into(), Ty::Int), ("height".into(), Ty::Float)].into()
        );
    }

    #[test]
    fn types_struct_member_access() {
        let (ast, session) = typecheck(
            "
        struct Person {
            let age: Int
            let height: Float
        }

        Person(age: 123, height: 1.23).age
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn types_generic_struct() {
        let (ast, session) = typecheck(
            "
        struct Person<T> {
            let age: T
        }

        Person(age: 123).age
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn checks_struct_init_args() {
        let (ast, _session) = typecheck_err(
            "
        struct Person {
            let age: Int
        }

        Person(age: 1.23)
        ",
        );

        assert_eq!(1, ast.diagnostics.len(), "{:?}", ast.diagnostics);
    }

    #[test]
    fn types_struct_init() {
        let (ast, session) = typecheck(
            "
        struct Person<T> {
            let age: T

            init(other: T) {
                self.age = other
            }
        }

        Person(age: 123).age
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn types_static_struct_methods() {
        let (ast, session) = typecheck(
            "
        struct Person {
           static func getAge() { 123 }
        }

        Person.getAge()
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn type_struct_method() {
        let (ast, session) = typecheck(
            "
        struct Person {
            let age: Int

            func getAge() {
                self.age
            }
        }

        Person(age: 123).getAge()
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
    }

    #[test]
    fn types_struct_method_on_arg() {
        let (ast, session) = typecheck(
            "
        struct Person {
            let age: Int

            func getAge() {
                self.age
            }
        }

        let person = Person(age: 123)
        getAge(person)

        func getAge(aged) {
            aged.getAge()
        }
        ",
        );

        assert_eq!(ty(2, &ast, &session), Ty::Int);
    }

    #[test]
    fn checks_struct_method_on_arg() {
        let (ast, _session) = typecheck_err(
            "
        struct Person {
            let age: Int
        }

        let person = Person(age: 123)
        getAge(person)

        func getAge(aged) {
            aged.getAge()
        }
        ",
        );

        assert_eq!(1, ast.diagnostics.len(), "{:?}", ast.diagnostics);
    }

    #[test]
    fn types_generic_struct_method() {
        let (ast, session) = typecheck(
            "
        struct Wrapper<T> {
            let wrapped: T

            func getWrapped() {
                self.wrapped
            }
        }

        Wrapper(wrapped: 123).getWrapped()
        Wrapper(wrapped: 1.23).getWrapped()
        ",
        );

        assert_eq!(ty(1, &ast, &session), Ty::Int);
        assert_eq!(ty(2, &ast, &session), Ty::Float);
    }

    #[test]
    fn types_nested_generic_struct_method() {
        let (ast, session) = typecheck(
            "

        struct Inner<T> {
            let inner: T
        }
        struct Middle<T> {
            let middle: T
        }
        struct Outer<T> {
            let outer: T
        }

        let inner = Inner(inner: true)
        let middle = Middle(middle: inner)
        let outer = Outer(outer: middle)

        outer.outer.middle.inner
        inner.inner
        ",
        );

        assert_eq!(ty(6, &ast, &session), Ty::Bool);
        assert_eq!(ty(7, &ast, &session), Ty::Bool);
    }

    #[test]
    fn types_simple_enum_constructor() {
        let (ast, session) = typecheck(
            "
            enum Fizz {
                case foo, bar
            }

            Fizz.foo
            Fizz.bar
        ",
        );

        assert_eq!(
            ty(1, &ast, &session),
            Ty::Variant("foo".into(), Box::new(Ty::Void))
        );
        assert_eq!(
            ty(2, &ast, &session),
            Ty::Variant("bar".into(), Box::new(Ty::Void))
        );
    }

    #[test]
    fn types_enum_constructor_with_values() {
        let (ast, session) = typecheck(
            "
            enum Fizz {
                case foo(Int, Bool), bar(Float)
            }

            Fizz.foo(123, true)
            Fizz.bar(1.23)
        ",
        );

        assert_eq!(
            ty(1, &ast, &session),
            Ty::Variant("foo".into(), Box::new(Ty::Tuple(vec![Ty::Int, Ty::Bool])))
        );
        assert_eq!(
            ty(2, &ast, &session),
            Ty::Variant("bar".into(), Box::new(Ty::Tuple(vec![Ty::Float])))
        );
    }

    #[test]
    fn types_enum_constructor_with_generic_value() {
        let (ast, session) = typecheck(
            "
            enum Opt<T> {
                case some(T), none
            }

            Opt.some(123)
            Opt.some(1.23)
            Opt.none
        ",
        );

        assert_eq!(
            ty(1, &ast, &session),
            Ty::Variant("some".into(), Box::new(Ty::Tuple(vec![Ty::Int])))
        );

        assert_eq!(
            ty(3, &ast, &session),
            Ty::Variant("none".into(), Box::new(Ty::Void))
        );
    }
}
