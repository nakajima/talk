#[cfg(test)]
pub mod tests {
    use crate::{
        ast::AST,
        compiling::{
            driver::{Driver, DriverConfig, Source},
            module::ModuleId,
        },
        diagnostic::Diagnostic,
        ir::monomorphizer::uncurry_function,
        make_row,
        name_resolution::{
            name_resolver::NameResolved,
            symbol::{EnumId, GlobalId, ProtocolId, StructId, Symbol, SynthesizedId},
        },
        node_kinds::{
            expr::{Expr, ExprKind},
            stmt::{Stmt, StmtKind},
        },
        types::{
            infer_ty::InferTy,
            row::Row,
            scheme::{ForAll, Scheme},
            ty::Ty,
            type_catalog::ConformanceKey,
            type_error::TypeError,
            type_session::{TypeDefKind, TypeEntry, Types},
        },
    };

    fn typecheck(code: &'static str) -> (AST<NameResolved>, Types) {
        let (ast, types) = typecheck_err(code);
        assert!(
            ast.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            ast.diagnostics
        );
        (ast, types)
    }

    fn typecheck_core(code: &'static str) -> (AST<NameResolved>, Types) {
        let driver = Driver::new(vec![Source::from(code)], DriverConfig::default());
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let types = typed.phase.types;
        let ast = typed.phase.asts.into_iter().next().unwrap().1;

        (ast, types)
    }

    fn typecheck_err(code: &'static str) -> (AST<NameResolved>, Types) {
        let driver = Driver::new_bare(vec![Source::from(code)], DriverConfig::default());
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let types = typed.phase.types;
        let ast = typed.phase.asts.into_iter().next().unwrap().1;

        (ast, types)
    }

    pub fn decl_ty(i: usize, ast: &AST<NameResolved>, session: &Types) -> Ty {
        let entry = session.get(&ast.roots[i].as_decl().id).unwrap();

        match entry {
            TypeEntry::Mono(ty) => ty.clone(),
            TypeEntry::Poly(scheme) => scheme.ty.clone(),
        }
    }

    pub fn ty(i: usize, ast: &AST<NameResolved>, session: &Types) -> Ty {
        let entry = session
            .get(&ast.roots[i].as_stmt().clone().as_expr().id)
            .unwrap();

        match entry {
            TypeEntry::Mono(ty) => ty.clone(),
            TypeEntry::Poly(scheme) => scheme.ty.clone(),
        }
    }

    #[test]
    fn types_int_literal() {
        let (ast, types) = typecheck("123");
        assert_eq!(ty(0, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_int() {
        let (ast, types) = typecheck("let a = 123; a");
        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_float() {
        let (ast, types) = typecheck("let a = 1.23; a");
        assert_eq!(ty(1, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_bool() {
        let (ast, types) = typecheck("let a = true; a ; let b = false ; b");
        assert_eq!(ty(1, &ast, &types), Ty::Bool);
        assert_eq!(ty(3, &ast, &types), Ty::Bool);
    }

    #[test]
    fn types_string() {
        let (ast, types) = typecheck("\"hello\"");
        assert_eq!(ty(0, &ast, &types), Ty::String());
    }

    #[test]
    fn types_string_concat() {
        let (ast, types) = typecheck_core("\"hello\" + \"world\"");
        assert_eq!(ty(0, &ast, &types), Ty::String());
    }

    #[test]
    fn types_equals_int() {
        let (ast, types) = typecheck_core("1 == 2; 1 != 2");
        assert_eq!(ty(0, &ast, &types), Ty::Bool);
        assert_eq!(ty(1, &ast, &types), Ty::Bool);
    }

    #[test]
    fn types_equals_float() {
        let (ast, types) = typecheck_core("1.0 == 2.0; 1.0 != 2.0");
        assert_eq!(ty(0, &ast, &types), Ty::Bool);
        assert_eq!(ty(1, &ast, &types), Ty::Bool);
    }

    #[test]
    fn types_equals_string() {
        let (ast, types) = typecheck_core("\"hello\" == \"world\" ; \"hello\" != \"world\"");
        assert_eq!(ty(0, &ast, &types), Ty::Bool);
        assert_eq!(ty(1, &ast, &types), Ty::Bool);
    }

    #[test]
    fn types_array_literal() {
        let (ast, types) = typecheck_core("[1,2,3]; [1.2, 3.4, 5.6]");
        assert_eq!(ty(0, &ast, &types), Ty::Array(InferTy::Int));
        assert_eq!(ty(1, &ast, &types), Ty::Array(InferTy::Float));
    }

    #[test]
    fn types_ir_builtin() {
        let (ast, types) = typecheck("__IR<Int>(\"add int 1 2\"); __IR<Float>(\"add int 1 2\")");
        assert_eq!(ty(0, &ast, &types), Ty::Int);
        assert_eq!(ty(1, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_array_properties() {
        let (ast, types) = typecheck_core("[1,2,3].count");
        assert_eq!(ty(0, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_basic_binary() {
        let (ast, types) = typecheck_core("func a(x) { x + 1 } ; a(123)");
        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn monomorphic_let_annotation() {
        let (ast, types) = typecheck(
            r#"
        let a: Int = 123
        a
    "#,
        );
        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn monomorphic_let_annotation_mismatch() {
        let (ast, _types) = typecheck_err(
            r#"
        let a: Bool = 123
        a
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_identity() {
        let (ast, types) = typecheck(
            "
        func identity(x) { x }
        identity(123)
        identity(true)
        ",
        );
        assert_eq!(ty(1, &ast, &types), Ty::Int);
        assert_eq!(ty(2, &ast, &types), Ty::Bool);
    }

    #[test]
    fn stores_func_instantiations() {
        let (ast, types) = typecheck(
            "
        func identity(x) { x }
        identity(123)
        identity(true)
        ",
        );

        let Stmt {
            kind:
                StmtKind::Expr(Expr {
                    kind:
                        ExprKind::Call {
                            callee: box root_1, ..
                        },
                    ..
                }),
            ..
        } = ast.roots[1].as_stmt()
        else {
            panic!("didn't get expr");
        };
        let Stmt {
            kind:
                StmtKind::Expr(Expr {
                    kind:
                        ExprKind::Call {
                            callee: box root_2, ..
                        },
                    ..
                }),
            ..
        } = ast.roots[2].as_stmt()
        else {
            panic!("didn't get expr");
        };

        let TypeEntry::Poly(Scheme {
            ty: Ty::Func(box Ty::Param(type_param), ..),
            ..
        }) = types
            .get_symbol(&Symbol::Global(GlobalId::from(1)))
            .unwrap()
        else {
            panic!("didn't get func type param");
        };

        assert_eq!(
            *types
                .catalogold
                .instantiations
                .ty
                .get(&(root_1.id, *type_param))
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *types
                .catalogold
                .instantiations
                .ty
                .get(&(root_2.id, *type_param))
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn stores_struct_instantiations() {
        let (ast, types) = typecheck(
            "
        struct Wrapper<T> {
            let wrapped: T
        }
        Wrapper(wrapped: 123)
        Wrapper(wrapped: true)
        ",
        );

        // Extract the constructor calls
        let Stmt {
            kind:
                StmtKind::Expr(Expr {
                    kind:
                        ExprKind::Call {
                            callee:
                                box Expr {
                                    kind: ExprKind::Constructor(_),
                                    id: constructor_1_id,
                                    ..
                                },
                            ..
                        },
                    ..
                }),
            ..
        } = ast.roots[1].as_stmt()
        else {
            panic!("didn't get first constructor call");
        };

        let Stmt {
            kind:
                StmtKind::Expr(Expr {
                    kind:
                        ExprKind::Call {
                            callee:
                                box Expr {
                                    kind: ExprKind::Constructor(_),
                                    id: constructor_2_id,
                                    ..
                                },
                            ..
                        },
                    ..
                }),
            ..
        } = ast.roots[2].as_stmt()
        else {
            panic!("didn't get second constructor call");
        };

        // Get the struct's type parameter
        let TypeEntry::Poly(Scheme { foralls, .. }) = types
            .get_symbol(&Symbol::Struct(StructId::from(1)))
            .unwrap_or_else(|| panic!("did not find struct {:#?}", types.types_by_symbol))
        else {
            panic!("didn't get struct scheme");
        };

        let ForAll::Ty(type_param) = foralls
            .iter()
            .find(|p| matches!(p, ForAll::Ty(..)))
            .unwrap()
        else {
            unreachable!()
        };

        // Check instantiations are stored
        assert_eq!(
            *types
                .catalogold
                .instantiations
                .ty
                .get(&(*constructor_1_id, *type_param))
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *types
                .catalogold
                .instantiations
                .ty
                .get(&(*constructor_2_id, *type_param))
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn stores_enum_instantiations() {
        let (ast, types) = typecheck(
            "
        enum Opt<T> {
            case some(T), none
        }
        Opt.some(123)
        Opt.some(true)
        ",
        );

        // Extract the variant access calls
        let Stmt {
            kind:
                StmtKind::Expr(Expr {
                    kind:
                        ExprKind::Call {
                            callee:
                                box Expr {
                                    kind: ExprKind::Member(..),
                                    id: member_1_id,
                                    ..
                                },
                            ..
                        },
                    ..
                }),
            ..
        } = ast.roots[1].as_stmt()
        else {
            panic!("didn't get first enum variant call");
        };

        let Stmt {
            kind:
                StmtKind::Expr(Expr {
                    kind:
                        ExprKind::Call {
                            callee:
                                box Expr {
                                    kind: ExprKind::Member(..),
                                    id: member_2_id,
                                    ..
                                },
                            ..
                        },
                    ..
                }),
            ..
        } = ast.roots[2].as_stmt()
        else {
            panic!("didn't get second enum variant call");
        };

        // Get the enum's type parameter
        let TypeEntry::Poly(Scheme { foralls, .. }) =
            types.get_symbol(&Symbol::Enum(EnumId::from(1))).unwrap()
        else {
            panic!("didn't get enum scheme");
        };

        let ForAll::Ty(type_param) = foralls
            .iter()
            .find(|p| matches!(p, ForAll::Ty(..)))
            .unwrap()
        else {
            unreachable!()
        };

        // Check instantiations are stored
        assert_eq!(
            *types
                .catalogold
                .instantiations
                .ty
                .get(&(*member_1_id, *type_param))
                .unwrap(),
            Ty::Int
        );
        assert_eq!(
            *types
                .catalogold
                .instantiations
                .ty
                .get(&(*member_2_id, *type_param))
                .unwrap(),
            Ty::Bool
        );
    }

    #[test]
    fn types_nested_generalized_funcs() {
        let (ast, types) = typecheck(
            "
            func foo() {
                func id(x) { x }
                (id(123), id(1.23))
            };

            foo()
            ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Float]));
    }

    #[test]
    fn types_nested_func() {
        let (ast, types) = typecheck(
            r#"
        func fizz(x) {
            func buzz() { x }
            buzz()
        }

        fizz(123)
        "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    #[ignore = "waiting on binary ops"]
    fn infers_simple_recursion() {
        let (ast, types) = typecheck(
            "
        func rec(x, y, z) {
            if x == y { x } else { rec(y-z, y, z) }
        }

        rec(0, 2, 1)
        rec(0.0, 2.0, 1.0)
        ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
        assert_eq!(ty(2, &ast, &types), Ty::Float);
    }

    #[test]
    fn explicit_generic_function_instantiates() {
        let (ast, types) = typecheck(
            r#"
        func id<T>(x: T) -> T { x }
        id(123)
        id(true)
    "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
        assert_eq!(ty(2, &ast, &types), Ty::Bool);
    }

    #[test]
    fn generic_function_body_must_respect_its_own_type_vars() {
        let (ast, _types) = typecheck_err(
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
        let (ast, types) = typecheck(
            "
        func outer() {
            func id(x) { x }
            (id(123), id(true))
        }

        outer()
        ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn types_call_let() {
        let (ast, types) = typecheck(
            "
        func id(x) { x }
        let a = id(123)
        let b = id(1.23)
        a
        b
        ",
        );
        assert_eq!(ty(3, &ast, &types), Ty::Int);
        assert_eq!(ty(4, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_nested_identity() {
        let (ast, types) = typecheck(
            "
        func identity(x) { x }
        identity(identity(123))
        identity(identity(true))
        ",
        );
        assert_eq!(ty(1, &ast, &types), Ty::Int);
        assert_eq!(ty(2, &ast, &types), Ty::Bool);
    }

    #[test]
    fn types_multiple_args() {
        let (ast, types) = typecheck(
            "
        func makeTuple(x, y) {
            (x, y)
        }

        makeTuple(123, true)
            ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn types_tuple_value() {
        let (ast, types) = typecheck(
            "
        let z = (123, true)
        z
        ",
        );
        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn types_tuple_assignment() {
        let (ast, types) = typecheck(
            "
        let z = (123, 1.23)
        let (x, y) = z
        x
        y
        ",
        );
        assert_eq!(ty(2, &ast, &types), Ty::Int);
        assert_eq!(ty(3, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_record_assignment() {
        let (ast, types) = typecheck(
            "
        let z = { x: 1, y: 1.23 }
        let { x, y } = z
        x
        y
        ",
        );
        assert_eq!(ty(2, &ast, &types), Ty::Int);
        assert_eq!(ty(3, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_if_expr() {
        let (ast, types) = typecheck(
            "
        let z = if true { 123 } else { 456 }
        z
        ",
        );
        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn requires_if_expr_cond_to_be_bool() {
        let (ast, _types) = typecheck_err(
            "
        let z = if 123 { 123 } else { 456 }
        z
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn requires_if_expr_arms_to_match() {
        let (ast, _types) = typecheck_err(
            "
        let z = if true { 123 } else { false }
        z
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn requires_if_stmt_cond_to_be_bool() {
        let (ast, _types) = typecheck_err(
            "
        if 123 { 123 }
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_match() {
        let (ast, types) = typecheck(
            "
        match 123 {
            123 -> true,
            456 -> false
        }
        ",
        );

        assert_eq!(ty(0, &ast, &types), Ty::Bool);
    }

    #[test]
    fn types_match_binding() {
        let (ast, types) = typecheck(
            "
        match 123 {
            a -> a,
        }
        ",
        );

        assert_eq!(ty(0, &ast, &types), Ty::Int);
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
        let (ast, types) = typecheck(
            "
        match (123, true) {
            (a, b) -> (b, a),
        }
        ",
        );

        assert_eq!(ty(0, &ast, &types), Ty::Tuple(vec![Ty::Bool, Ty::Int]));
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
        let (ast, _types) = typecheck_err(
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
        let (ast, _types) = typecheck_err(
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
        let (ast, _types) = typecheck_err(
            r#"
        func f(x: Int) -> Int { x }
        f(true)
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn return_annotation_is_enforced_in_body() {
        let (ast, _types) = typecheck_err(
            r#"
        func f(x: Int) -> Int { true }
        f(1)
    "#,
        );
        assert_eq!(ast.diagnostics.len(), 1);
    }

    #[test]
    fn types_recursive_func() {
        let (ast, types) = typecheck(
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

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn recursion_is_monomorphic_within_binding_group() {
        // Polymorphic recursion should NOT be inferred.
        let (ast, _types) = typecheck_err(
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
    #[ignore = "need to figure out syntax for generic func annotations"]
    fn func_type_annotation_on_let_is_honored() {
        // Once Func annotations work, this should typecheck and instantiate.
        let (ast, types) = typecheck(
            r#"
        let id: (T) -> T = func(x) { x }
        (id(123), id(true))
    "#,
        );
        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    #[ignore = "TypeAnnotationKind::Tuple not implemented"]
    fn tuple_type_annotation_on_let_is_honored() {
        let (ast, types) = typecheck(
            r#"
        let z: (Int, Bool) = (123, true)
        z
    "#,
        );
        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn let_generalization_for_value_bindings() {
        let (ast, types) = typecheck(
            r#"
        let id = func(x) { x }
        (id(123), id(true))
    "#,
        );
        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn types_record_literal() {
        let (ast, types) = typecheck(
            r#"
        let rec = { a: true, b: 123, c: 1.23 }
        rec
        "#,
        );

        let Ty::Record(row) = ty(1, &ast, &types) else {
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
        let (ast, types) = typecheck(
            "
        let x: { a: Int, b: Bool } = { b: true, a: 1 }
        x
        ",
        );

        let Ty::Record(row) = ty(1, &ast, &types) else {
            panic!("Didn't get row");
        };

        assert_eq!(
            row.close(),
            [("a".into(), Ty::Int), ("b".into(), Ty::Bool)].into()
        )
    }

    #[test]
    fn types_record_member() {
        let (ast, types) = typecheck(
            r#"
        let rec = { a: true, b: 123, c: 1.23 }
        rec.a
        rec.b
        rec.c
        "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Bool);
        assert_eq!(ty(2, &ast, &types), Ty::Int);
        assert_eq!(ty(3, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_nested_record() {
        let (ast, types) = typecheck(
            r#"
        let rec = { a: { b: { c: 1.23 } } }
        rec.a.b.c
        "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_record_pattern_out_of_order() {
        let (ast, types) = typecheck(
            r#"
        let rec = { a: 123, b: true }
        match rec {
            { b, a } -> (a, b)
        }
        "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn types_record_pattern_with_equalities() {
        let (ast, types) = typecheck(
            r#"
        let rec = { a: 123, b: true }
        match rec {
            { a: 123, b } -> b
        }
        "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Bool);
    }

    #[test]
    fn type_nested_record_pattern() {
        let (ast, types) = typecheck(
            r#"
        let rec = { a: 123, b: { c: true } }
        match rec {
            { a, b: { c } } -> c
        }
        "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Bool);
    }

    #[test]
    fn checks_fields_exist() {
        let (ast, _types) = typecheck_err(
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
        let (ast, _types) = typecheck_err(
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
        let (ast, types) = typecheck(
            r#"
        let id = func id(r) { r }
        // project different fields from differently-shaped records
        (id({ a: 1 }).a, id({ b: true }).b)
    "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    /// Simple polymorphic projection: fstA extracts `a` from any record that has it.
    #[test]
    fn row_projection_polymorphic() {
        let (ast, types) = typecheck(
            r#"
        func fstA(r) { r.a }
        (fstA({ a: 1 }), fstA({ a: 2, b: true }))
    "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Int]));
    }

    /// Local `let` that returns an *env row* must NOT generalize its tail.
    /// Matching on a field that isn't known in the env row should fail inside `outer`.
    #[test]
    fn row_env_tail_not_generalized_in_local_let() {
        let (ast, _types) = typecheck_err(
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
        let (ast, types) = typecheck(
            r#"
        func outer() {
            let id = func(r) { r };     // fresh row metas -> generalize to a row param
            (id({ a: 1 }).a, id({ b: true }).b)
        }
        outer()
    "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    /// Instantiation stability: once a row param is instantiated at a call site,
    /// subsequent projections line up with the instantiated fields.
    #[test]
    fn row_instantiation_stability_across_uses() {
        let (ast, types) = typecheck(
            r#"
        let id = func id(r) { r }
        let x  = id({ a: 1, b: true });
        (x.a, x.b)
    "#,
        );

        assert_eq!(ty(2, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    /// Polymorphic consumer: a function requiring presence of `a` should accept any record
    /// with `a`, regardless of extra fields.
    #[test]
    fn row_presence_constraint_is_polymorphic() {
        let (ast, types) = typecheck(
            r#"
        func useA(r) { r.a } // imposes HasField(row_var, "a", Int)
        (useA({ a: 1 }), useA({ a: 2, c: true }))
    "#,
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Int]));
    }

    #[test]
    fn row_meta_levels_prevent_leak() {
        // Outer forces r to be an open record { a: Int | row_var } by projecting r.a.
        // Then local let k = func(){ r } must NOT generalize row_var; match should fail on { c }.
        let (ast, _types) = typecheck_err(
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
        let (ast, types) = typecheck(
            "
        func foo(x: { y: Int, z: Bool }) {
            (x.y, x.z)
        }

        foo({ y: 123, z: true })
        ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn enforces_non_annotated_record() {
        let (ast, _types) = typecheck_err(
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
        let (ast, types) = typecheck(
            "
        func foo(x) {
            (x.y, x.z)
        }

        foo({ y: 123, z: 1.23 })
        foo({ y: 123, z: 123 })
        ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Float]));
        assert_eq!(ty(2, &ast, &types), Ty::Tuple(vec![Ty::Int, Ty::Int]));
    }

    #[test]
    fn enforces_row_type_as_params() {
        let (ast, _types) = typecheck_err(
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
        let (ast, types) = typecheck(
            "
        struct Person {
            let age: Int
            let height: Float
        }

        Person(age: 123, height: 1.23)
        ",
        );

        let nominal = Ty::Nominal {
            symbol: StructId::from(1).into(),
            row: Box::new(make_row!(Struct, "age" => Ty::Int, "height" => Ty::Float)),
        };

        let (params, _ret) = uncurry_function(
            types
                .get_symbol(&Symbol::from(SynthesizedId::from(1)))
                .unwrap()
                .clone()
                .as_mono_ty()
                .clone(),
        );

        assert_eq!(params.len(), 3);
        assert_eq!(ty(1, &ast, &types), nominal);
    }

    #[test]
    fn types_struct_referencing_another_struct() {
        let (ast, types) = typecheck(
            "
        struct A {
            let count: Int
        }

        struct B {
            let a: A
        }

        B(a: A(count: 1)).a.count
        ",
        );

        assert_eq!(ty(2, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_struct_member_access() {
        let (ast, types) = typecheck(
            "
        struct Person {
            let age: Int
            let height: Float
        }

        Person(age: 123, height: 1.23).age
        ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn type_generic_struct() {
        let (ast, types) = typecheck(
            "
        struct Person<T> {
            let age: T
        }

        Person(age: 123).age
        ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn checks_struct_init_args() {
        let (ast, _types) = typecheck_err(
            "
        struct Person {
            let age: Int

            // init(age: Int) {
            //     self.age = age
            // }
        }

        Person(age: 1.23)
        ",
        );

        assert_eq!(ast.diagnostics.len(), 1, "{:?}", ast.diagnostics);
    }

    #[test]
    fn types_generic_struct_init() {
        let (ast, types) = typecheck(
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

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_static_struct_methods() {
        let (ast, types) = typecheck(
            "
        struct Person {
           static func getAge() { 123 }
        }

        Person.getAge()
        ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn type_struct_method() {
        let (ast, types) = typecheck(
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

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_struct_method_on_arg() {
        let (ast, types) = typecheck(
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

        assert_eq!(ty(2, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_explicit_type_application() {
        let (ast, types) = typecheck(
            r#"
          struct Boxy<T> { let value: T }

          // Explicit type application
          let x: Boxy<Int> = Boxy(value: 42)
          let y: Boxy<Float> = Boxy(value: 3.14)

          x
          "#,
        );

        assert_eq!(
            ty(3, &ast, &types),
            Ty::Nominal {
                symbol: StructId::from(1).into(),
                row: make_row!(Struct, "value" => Ty::Int).into()
            }
        );
    }

    #[test]
    fn checks_struct_method_on_arg() {
        let (ast, _types) = typecheck_err(
            "
        struct Person {
            let age: Int
        }

        let person = Person(age: 123)
        callNonExisting(person)

        func callNonExisting(aged) {
            aged.getAge()
        }
        ",
        );

        assert_eq!(
            1,
            ast.diagnostics.len(),
            "should have no method error: {:?}",
            ast.diagnostics
        );
    }

    #[test]
    fn checks_generic_struct_arg() {
        let (ast, types) = typecheck(
            "
        struct Person {
            func getAge<T>(t: T) -> T { t }
        }

        Person().getAge(123)
        Person().getAge(1.23)
        ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
        assert_eq!(ty(2, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_generic_struct_method() {
        let (ast, types) = typecheck(
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

        assert_eq!(ty(1, &ast, &types), Ty::Int);
        assert_eq!(ty(2, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_nested_generic_struct_method() {
        let (ast, types) = typecheck(
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

        assert_eq!(ty(6, &ast, &types), Ty::Bool);
        assert_eq!(ty(7, &ast, &types), Ty::Bool);
    }

    #[test]
    fn types_simple_enum_constructor() {
        let (ast, types) = typecheck(
            "
            enum Fizz {
                case foo, bar
            }

            Fizz.foo
            Fizz.bar
        ",
        );

        assert_eq!(
            ty(1, &ast, &types),
            Ty::Nominal {
                symbol: EnumId::from(1).into(),
                row: Box::new(make_row!(Enum, "foo" => Ty::Void, "bar" => Ty::Void)),
            }
        );
        assert_eq!(
            ty(2, &ast, &types),
            Ty::Nominal {
                symbol: EnumId::from(1).into(),
                row: Box::new(make_row!(Enum, "foo" => Ty::Void, "bar" => Ty::Void)),
            }
        );
    }

    #[test]
    fn types_enum_constructor_with_values() {
        let (ast, types) = typecheck(
            "
            enum Fizz {
                case foo(Int, Bool), bar(Float)
            }

            Fizz.foo(123, true)
            Fizz.bar(1.23)
        ",
        );

        assert_eq!(
            ty(1, &ast, &types),
            Ty::Nominal {
                symbol: EnumId::from(1).into(),
                row: Box::new(
                    make_row!(Enum, "foo" => Ty::Tuple(vec![Ty::Int, Ty::Bool]), "bar" => Ty::Float)
                ),
            }
        );
        assert_eq!(
            ty(2, &ast, &types),
            Ty::Nominal {
                symbol: EnumId::from(1).into(),
                row: Box::new(
                    make_row!(Enum, "foo" => Ty::Tuple(vec![Ty::Int, Ty::Bool]), "bar" => Ty::Float)
                ),
            }
        );
    }

    #[test]
    fn types_enum_constructor_with_generic_value() {
        let (ast, types) = typecheck(
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
            ty(1, &ast, &types),
            Ty::Nominal {
                symbol: EnumId::from(1).into(),
                row: Box::new(make_row!(Enum, "some" => Ty::Int, "none" => Ty::Void)),
            }
        );
        assert_eq!(
            ty(2, &ast, &types),
            Ty::Nominal {
                symbol: EnumId::from(1).into(),
                row: Box::new(make_row!(Enum, "some" => Ty::Float, "none" => Ty::Void)),
            }
        );
        assert_eq!(
            ty(3, &ast, &types),
            Ty::Nominal {
                symbol: EnumId::from(1).into(),
                row: Box::new(make_row!(Enum, "some" => Ty::Param(1.into()), "none" => Ty::Void)),
            }
        );
    }

    #[test]
    fn types_simple_enum_match() {
        let (ast, types) = typecheck(
            "
            enum Fizz {
                case foo, bar
            }

            match Fizz.foo {
                Fizz.foo -> 1,
                Fizz.bar -> 2
            }
            ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_nested_enum_match() {
        let (ast, types) = typecheck(
            "
            enum Fizz<T> {
                case foo(T)
            }

            match Fizz.foo(Fizz.foo(123)) {
                Fizz.foo(Fizz.foo(x)) -> x,
            }
            ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_enum_instance_methods() {
        let (ast, types) = typecheck(
            "
            enum Fizz<T> {
                case foo(T), bar(T)

                func unwrap() {
                    match self {
                        Fizz.foo(t) -> t,
                        Fizz.bar(t) -> t
                    }
                }
            }

            Fizz.foo(123).unwrap()
            ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_unqualified_variant() {
        let (ast, types) = typecheck(
            "
            enum Fizz {
                case foo(Int), bar(Int)
            }

            match Fizz.foo(123) {
                .foo(x) -> x,
                .bar(y) -> y
            }
            ",
        );

        assert_eq!(ty(1, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_unqualified_variant_as_param() {
        let (ast, types) = typecheck(
            "
            enum Fizz {
                case foo(Int), bar(Int)
            }

            func buzz(fizz: Fizz) {
                match fizz {
                    .foo(x) -> x,
                    .bar(y) -> y
                }
            }

            buzz(fizz: .foo(123))
            ",
        );

        assert_eq!(ty(2, &ast, &types), Ty::Int);
    }

    #[test]
    fn types_simple_conformance() {
        let (_ast, types) = typecheck(
            "
            protocol Countable {
                func getCount() -> Int
            }

            struct Person {}

            extend Person: Countable {
                func getCount() {
                    123
                }
            }
            ",
        );

        assert!(types.catalogold.conformances.contains_key(&ConformanceKey {
            protocol_id: ProtocolId::from(1),
            conforming_id: StructId::from(1).into(),
        }));
    }

    #[test]
    fn checks_method_protocol_conformance() {
        let (ast, _types) = typecheck_err(
            "
            protocol Countable {
                func getCount() -> Int
            }

            struct Person {}

            extend Person: Countable {
                func getCount() -> Float {
                    1.123 // This is wrong
                }
            }
        ",
        );

        assert_eq!(
            1,
            ast.diagnostics.len(),
            "didn't get diagnostic: {:?}",
            ast.diagnostics
        );
    }

    #[test]
    fn checks_protocol_method() {
        let (ast, types) = typecheck(
            "
            protocol Countable {
                func getCount() -> Int
                func getOtherCount() {
                    self.getCount()
                }
            }

            struct Person {}

            extend Person: Countable {
                func getCount() { 123 }
            }

            Person().getOtherCount()
        ",
        );

        assert_eq!(ty(3, &ast, &types), Ty::Int)
    }

    #[test]
    fn types_simple_protocol() {
        let (ast, types) = typecheck(
            "
            protocol Countable { func getCount() -> Int }
            struct Person { let count: Int }
            extend Person: Countable {
                func getCount() {
                    self.count
                }
            }

            func getCount<T: Countable>(countable: T) {
                countable.getCount()
            }

            let person = Person(count: 1)
            getCount(person)
            ",
        );

        assert_eq!(ty(5, &ast, &types), Ty::Int)
    }

    #[test]
    fn tests_infers_associated_types() {
        let (ast, types) = typecheck(
            "
        protocol Aged {
            associated T

            func getAge() -> T
        }

        struct Inty: Aged {
            func getAge() {
                123
            }
        }

        struct Floaty: Aged {
            func getAge() {
                1.23
            }
        }

        func get<A: Aged>(aged: A) {
            aged.getAge()
        }

        get(Inty())
        get(Floaty())
        ",
        );

        assert_eq!(ty(4, &ast, &types), Ty::Int);
        assert_eq!(ty(5, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_protocol_associated_types() {
        let (ast, types) = typecheck(
            "
        protocol Aged {
            associated T

            func getAge() -> T
        }

        struct Person<A>: Aged {
            typealias T = A
            let age: A

            func getAge() -> A {
                self.age
            }
        }

        func getFloat<A: Aged>(aged: A) {
            aged.getAge()
        }

        // Make sure associated types can be represented
        func getInt<A: Aged>(aged: A) -> A.T {
            aged.getAge()
        }

        getFloat(Person(age: 1.2))
        getInt(Person(age: 1))
        ",
        );

        assert_eq!(ty(4, &ast, &types), Ty::Float);
        assert_eq!(ty(5, &ast, &types), Ty::Int);
    }

    #[test]
    fn can_extend_builtins() {
        let (ast, types) = typecheck(
            "
        protocol Foo {
            func foo() -> Int
        }
        extend Int: Foo {
            func foo() { 123 }
        }
        1.foo()
        ",
        );

        assert_eq!(ty(2, &ast, &types), Ty::Int);
    }

    #[test]
    fn add_protocol_prototype() {
        let (ast, session) = typecheck(
            "
        protocol Addy { func addy<Ret, RHS>(rhs: RHS) -> Ret }

        extend Int: Addy {
            func addy(rhs: Int) -> Int {
                self
            }
        }

        1.addy(2)
        ",
        );

        assert_eq!(ty(2, &ast, &session), Ty::Int);
    }

    #[test]
    fn includes_core_optional() {
        let (ast, session) = typecheck_core(
            "
        enum Opt<T> {
            case some(T), none
        }

        Optional.some(123)
        Opt.some(1.23)
        ",
        );

        assert_eq!(
            ty(1, &ast, &session),
            Ty::Nominal {
                symbol: Symbol::Enum(EnumId {
                    module_id: ModuleId::Core,
                    local_id: 1
                }),
                row: make_row!(Enum, "some" => Ty::Int, "none" => Ty::Void).into()
            }
        );

        // Make sure it doesn't clash
        assert_eq!(
            ty(2, &ast, &session),
            Ty::Nominal {
                symbol: Symbol::Enum(EnumId {
                    module_id: ModuleId::Current,
                    local_id: 1
                }),
                row: make_row!(Enum, "some" => Ty::Float, "none" => Ty::Void).into()
            }
        );
    }

    #[test]
    fn types_plus() {
        let (ast, types) = typecheck_core(
            "
        1 + 2
        1.0 + 2.0
        ",
        );

        assert_eq!(ty(0, &ast, &types), Ty::Int);
        assert_eq!(ty(1, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_minus() {
        let (ast, types) = typecheck_core(
            "
        1 - 2
        1.0 - 2.0
        ",
        );

        assert_eq!(ty(0, &ast, &types), Ty::Int);
        assert_eq!(ty(1, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_multiplication() {
        let (ast, types) = typecheck_core(
            "
        1 * 2
        1.0 * 2.0
        ",
        );

        assert_eq!(ty(0, &ast, &types), Ty::Int);
        assert_eq!(ty(1, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_division() {
        let (ast, types) = typecheck_core(
            "
        1 / 2
        1.0 / 2.0
        ",
        );

        assert_eq!(ty(0, &ast, &types), Ty::Int);
        assert_eq!(ty(1, &ast, &types), Ty::Float);
    }

    #[test]
    fn types_comparisons() {
        let (ast, types) = typecheck_core(
            "
        1 == 2
        1.0 == 2.0
        ",
        );

        assert_eq!(ty(0, &ast, &types), Ty::Bool);
        assert_eq!(ty(1, &ast, &types), Ty::Bool);
    }

    #[test]
    fn types_custom_add() {
        let (ast, types) = typecheck_core(
            "
        struct A {}
        struct B {}
        struct C {}
        extend A: Add {
            func add(rhs: B) -> C {
                C()
            }
        }
        A() + B()
        ",
        );

        assert_eq!(
            ty(4, &ast, &types),
            Ty::Nominal {
                symbol: StructId::from(3).into(),
                row: Row::Empty(TypeDefKind::Struct).into()
            }
        );
    }
}
