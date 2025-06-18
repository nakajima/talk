#![feature(box_patterns)]

#[cfg(test)]
mod type_checker_tests {
    use talk::{
        SourceFile, SymbolID, Typed,
        environment::TypeDef,
        expr::Expr,
        name::Name,
        type_checker::{Ty, TypeVarID, TypeVarKind},
    };

    fn check(code: &'static str) -> SourceFile<Typed> {
        talk::check(code).unwrap()
    }

    #[test]
    fn checks_an_int() {
        let checker = check("123");
        assert_eq!(checker.type_for(0).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_a_float() {
        let checker = check("123.");
        assert_eq!(checker.type_for(0).unwrap(), Ty::Float);
    }

    #[test]
    fn checks_a_named_func() {
        let checker = check("func sup(name) { name }\nsup");
        let root_id = checker.root_ids()[0];

        let Ty::Func(params, return_type, _) = checker.type_for(root_id).unwrap() else {
            panic!(
                "didnt get a func, got: {:#?}",
                checker.type_for(root_id).unwrap()
            );
        };

        let param_type = params[0].clone();

        assert_eq!(return_type, param_type.into());
        assert_eq!(
            *return_type,
            Ty::TypeVar(TypeVarID(3, TypeVarKind::FuncParam))
        );

        // The second root-expr is the *use* of `sup`.
        let Ty::Func(params2, return_type2, _) = checker.type_for(checker.root_ids()[1]).unwrap()
        else {
            panic!(
                "expected `sup` to be a function, got: {:?}",
                checker.type_for(checker.root_ids()[1]).unwrap()
            );
        };

        // It must still be a one-parameter function …
        assert_eq!(params2.len(), 1);
        // … whose return type equals its parameter (α → α),
        // even though this α is a fresh type-variable distinct
        // from the one in the definition above.
        assert_eq!(*return_type2, params2[0].clone());
    }

    #[test]
    fn checks_a_func_with_return_type() {
        let checker = check("func sup(name) -> Int { name }\n");
        let root_id = checker.root_ids()[0];
        let Ty::Func(params, return_type, _) = checker.type_for(root_id).unwrap() else {
            panic!(
                "didnt get a func, got: {:#?}",
                checker.type_for(root_id).unwrap()
            );
        };

        assert_eq!(params, vec![Ty::Int]);
        assert_eq!(*return_type, Ty::Int);
    }

    #[test]
    fn checks_call() {
        let checker = check(
            "
        func fizz(c) { c }
        fizz(c: 123)
        ",
        );
        let root_id = checker.root_ids()[1];
        assert_eq!(checker.type_for(root_id).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_a_let_assignment() {
        let checker = check("let count = 123\ncount");
        let root_id = checker.root_ids()[1];
        assert_eq!(checker.type_for(root_id).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_apply_twice() {
        let checker = check(
            "
        func applyTwice(f, x) { f(f(x)) }
        applyTwice
        ",
        );

        let root_id = checker.root_ids()[0];
        let Ty::Func(params, return_type, _) = checker.type_for(root_id).unwrap() else {
            panic!(
                "expected `applyTwice` to be a function, got: {:?}",
                checker.type_for(root_id).unwrap()
            );
        };

        // applyTwice should have exactly 2 parameters
        assert_eq!(params.len(), 2);

        // f : A -> A
        match &params[0] {
            Ty::Func(arg_tys, ret_ty, _) => {
                assert_eq!(arg_tys.len(), 1);
                // the return of f must be the same type as x
                assert_eq!(**ret_ty, params[1].clone());
            }
            other => panic!("`f` should be a function, got {other:?}"),
        }

        // the overall return type of applyTwice is the same as x
        assert_eq!(return_type, params[1].clone().into());
    }

    #[test]
    fn checks_call_with_generics() {
        let checked = check(
            "
        func fizz<T>(ty: T) { T }

        fizz<Int>(123)
        fizz<Bool>(true)
        ",
        );

        assert_eq!(checked.type_for(checked.root_ids()[1]).unwrap(), Ty::Int);
        assert_eq!(checked.type_for(checked.root_ids()[2]).unwrap(), Ty::Bool);
    }

    #[test]
    fn checks_composition() {
        let checker = check(
            "
        func compose(f, g) {
            func inner(x) { f(g(x)) }
            inner
        }
        compose
        ",
        );
        let root_id = checker.root_ids()[0];
        let Ty::Func(params, return_type, _) = checker.type_for(root_id).unwrap() else {
            panic!(
                "expected `compose` to be a function, got: {:?}",
                checker.type_for(root_id).unwrap()
            );
        };

        // compose should have exactly 2 parameters: f and g
        assert_eq!(params.len(), 2);
        let f_ty = &params[0];
        let g_ty = &params[1];

        // f : B -> C
        let Ty::Func(f_args, f_ret, _) = f_ty.clone() else {
            panic!("did not get func: {f_ty:?}");
        };
        assert_eq!(f_args.len(), 1);

        // g : A -> B
        let Ty::Func(g_args, g_ret, _) = g_ty.clone() else {
            panic!("did not get func")
        };

        assert_eq!(g_args.len(), 1);

        // g's return type (B) must match f's argument type
        assert_eq!(*g_ret, f_args[0].clone());

        // the inner function's return (and thus compose's return) is f's return type C
        let Ty::Closure {
            func: box Ty::Func(inner_params, inner_ret, _),
            ..
        } = *return_type
        else {
            panic!("expected `compose` to return a closure, got {return_type:?}",);
        };
        assert_eq!(inner_params.len(), 1);
        assert_eq!(inner_params[0], g_args[0].clone()); // inner's x : A
        assert_eq!(*inner_ret, *f_ret.clone()); // inner returns C
    }

    #[test]
    fn checks_simple_recursion() {
        let checker = check(
            "
        func rec(n) {
            rec(n)
        }
        rec
        ",
        );

        // the bare `rec` at the top level should be a Func([α], α)
        let root_id = checker.root_ids()[0];
        let ty = checker.type_for(root_id).unwrap();
        let Ty::Closure {
            func: box Ty::Func(params, ret, _),
            ..
        } = ty
        else {
            panic!()
        };
        // exactly one parameter
        assert_eq!(params.len(), 1);
        // return type equals the parameter type
        assert_eq!(*ret, Ty::TypeVar(TypeVarID(4, TypeVarKind::CallReturn)));
    }

    #[test]
    fn checks_mutual_recursion() {
        let checker = check(
            "
        func even(n: Int) -> Int {
            odd(n)
        }
        func odd(n: Int) -> Int {
            even(n)
        }
        even
        ",
        );

        let root_id = checker.root_ids()[0];
        let ty = checker.type_for(root_id).unwrap();
        match ty {
            Ty::Closure {
                func: box Ty::Func(params, ret, _),
                ..
            } => {
                assert_eq!(params.len(), 1);
                // both even and odd must have the same input and output type
                assert_eq!(*ret, Ty::Int);
                assert_eq!(params[0].clone(), Ty::Int);
            }
            other => panic!("expected a function, got {other:?}"),
        }
    }

    #[test]
    fn infers_let_with_enum_case() {
        let checked = check(
            "
        enum Maybe<T> {
          case definitely(T), nope
        }

        let maybe = Maybe.definitely(123)
        maybe
        ",
        );

        assert_eq!(
            checked.type_for(checked.root_ids()[2]).unwrap(),
            Ty::Enum(SymbolID::typed(1), vec![Ty::Int]),
        );
    }

    #[test]
    fn infers_identity() {
        let checker = check(
            "
            func identity(arg) { arg }
            identity(1)
            identity(2.0)
        ",
        );

        assert_eq!(checker.type_for(checker.root_ids()[1]).unwrap(), Ty::Int);
        assert_eq!(checker.type_for(checker.root_ids()[2]).unwrap(), Ty::Float);
    }

    #[test]
    fn checks_simple_enum_declaration() {
        let checker = check(
            "
            enum Fizz {
                case foo, bar
            }
        ",
        );

        assert_eq!(
            checker.type_for(checker.root_ids()[0]).unwrap(),
            Ty::Enum(SymbolID::typed(1), vec![])
        );

        // Check the variants
        assert_eq!(
            checker.type_for(0).unwrap(),
            Ty::EnumVariant(SymbolID::typed(1), vec![])
        );
        assert_eq!(
            checker.type_for(1).unwrap(),
            Ty::EnumVariant(SymbolID::typed(1), vec![])
        );
    }

    #[test]
    fn checks_enum_with_associated_values() {
        let checker = check(
            "
            enum Option {
                case some(Int), none
            }
            ",
        );

        assert_eq!(
            checker.type_for(checker.root_ids()[0]).unwrap(),
            Ty::Enum(SymbolID::typed(1), vec![])
        );

        // Check variant types
        assert_eq!(
            checker.type_for(1).unwrap(),
            Ty::EnumVariant(SymbolID::typed(1), vec![Ty::Int]),
        );
        assert_eq!(
            checker.type_for(2).unwrap(),
            Ty::EnumVariant(SymbolID::typed(1), vec![])
        );
    }

    #[test]
    fn checks_generic_enum_declaration() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none
            }
            ",
        );

        let enum_ty = checker.type_for(checker.root_ids()[0]).unwrap();
        match enum_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics.len(), 1);
                // Should be a type variable for T
                assert!(matches!(generics[0], Ty::TypeVar(_)));
            }
            _ => panic!("Expected generic enum type, got {enum_ty:?}"),
        }
    }

    #[test]
    fn checks_enum_variant_constructor_call() {
        let checker = check(
            "
            enum Option {
                case some(Int), none
            }

            Option.some(42)
            ",
        );

        // The call to some(42) should return Option type
        let call_result = checker.type_for(checker.root_ids()[1]).unwrap();
        assert_eq!(call_result, Ty::Enum(SymbolID::typed(1), vec![]));
    }

    #[test]
    fn checks_generic_enum_variant_constructor() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none  
            }
            Option.some(42)
            Option.some(3.14)
            ",
        );

        // First call should be Option<Int>
        let call1 = checker.type_for(checker.root_ids()[1]).unwrap();
        match call1 {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Option<Int>, got {call1:?}"),
        }

        // Second call should be Option<Float>
        let call2 = checker.type_for(checker.root_ids()[2]).unwrap();
        match call2 {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics, vec![Ty::Float]);
            }
            _ => panic!("Expected Option<Float>, got {call2:?}"),
        }
    }

    #[test]
    fn checks_nested_enum_types() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none
            }

            enum Result<T, E> {
                case ok(T), err(E)
            }
            Result.ok(Option.some(42))
            ",
        );

        // Should be Result<Option<Int>, _>
        let result_ty = checker.type_for(checker.root_ids()[2]).unwrap();
        match result_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(3)); // Result enum
                assert_eq!(generics.len(), 2);

                // First generic should be Option<Int>
                match &generics[0] {
                    Ty::Enum(opt_id, opt_generics) => {
                        assert_eq!(*opt_id, SymbolID::typed(1)); // Option enum
                        assert_eq!(opt_generics, &vec![Ty::Int]);
                    }
                    _ => panic!("Expected Option<Int> as first generic"),
                }
            }
            _ => panic!("Expected Result type, got {result_ty:?}"),
        }
    }

    #[test]
    fn checks_basic_match_expression() {
        let checker = check(
            "
            enum Bool {
                case yes, no
            }

            func test(b: Bool) {
                match b {
                    .yes -> 1
                    .no -> 0
                }
            }
            ",
        );

        // Function should have type Bool -> Int
        let func_ty = checker.type_for(checker.root_ids()[1]).unwrap();
        match func_ty {
            Ty::Func(params, ret, _) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], Ty::Enum(SymbolID::typed(1), vec![])); // Bool
                assert_eq!(*ret, Ty::Int);
            }
            _ => panic!("Expected function type, got {func_ty:?}"),
        }
    }

    #[test]
    fn checks_match_with_variable_binding() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none
            }
            func unwrap(opt: Option<Int>) {
                match opt {
                    .some(value) -> value
                    .none -> 0
                }
            }
            ",
        );

        // Function should have type Option<Int> -> Int
        let func_ty = checker.type_for(checker.root_ids()[1]).unwrap();
        match func_ty {
            Ty::Func(params, ret, _) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], Ty::Enum(SymbolID::typed(1), vec![Ty::Int])); // Option<Int>
                assert_eq!(*ret, Ty::Int);
            }
            _ => panic!("Expected function type, got {func_ty:?}"),
        }
    }

    #[test]
    fn checks_recursive_enum() {
        let checker = check(
            "
            enum List<T> {
                case cons(T, List<T>), nil
            }
            ",
        );

        let enum_ty = checker.type_for(checker.root_ids()[0]).unwrap();
        match enum_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics.len(), 1);
            }
            _ => panic!("Expected List<T> type, got {enum_ty:?}"),
        }

        let Some(Expr::EnumDecl(_, _, body)) = checker.roots()[0] else {
            panic!("did not get enum decl");
        };

        assert_eq!(*body, 6);

        let Some(Expr::Block(exprs)) = checker.get(&6) else {
            panic!("did not get body");
        };

        assert_eq!(exprs[0], 4);

        // Check cons variant has recursive structure: T, List<T>
        let cons_variant = checker.type_for(4);
        match cons_variant {
            Some(Ty::EnumVariant(enum_id, field_types)) => {
                assert_eq!(enum_id, SymbolID::typed(1));
                assert_eq!(field_types.len(), 2);
                // Second field should be List<T> (recursive reference)
                match &field_types[1] {
                    Ty::Enum(list_id, _) => assert_eq!(*list_id, SymbolID::typed(1)),
                    _ => panic!("Expected recursive List type"),
                }
            }
            _ => panic!("Expected cons variant type, got: {cons_variant:?}"),
        }
    }

    #[test]
    fn checks_match_type_mismatch_error() {
        // This should fail due to inconsistent return types in match arms
        let result = std::panic::catch_unwind(|| {
            check(
                "
                enum Bool {
                    case true, false  
                }
                func test(b: Bool) {
                    match b {
                        .true -> 1      // Int
                        .false -> 3.14  // Float - type mismatch!
                    }
                }
                ",
            )
        });

        // Should fail type checking
        assert!(result.is_err());
    }

    #[test]
    fn checks_enum_in_function_parameters() {
        let checker = check(
            "
            enum Color {
                case red, green, blue
            }
            func describe(c: Color) -> Int {
                match c {
                    .red -> 1
                    .green -> 2  
                    .blue -> 3
                }
            }
            describe(.red)
            ",
        );

        // Call should type check correctly
        let call_result = checker.type_for(checker.root_ids()[2]).unwrap();
        assert_eq!(call_result, Ty::Int);
    }

    #[test]
    fn checks_multiple_enum_parameters() {
        let checker = check(
            "
            enum Bool {
                case yes, no
            }
            func and(a: Bool, b: Bool) -> Bool {
                match a {
                    .yes -> b
                    .no -> .no
                }
            }
            and(.yes, .no)
            ",
        );

        let call_result = checker.type_for(checker.root_ids()[2]).unwrap();
        assert_eq!(call_result, Ty::Enum(SymbolID::typed(1), vec![])); // Bool
    }

    #[test]
    fn checks_enum_as_return_type() {
        let checker = check(
            "
            enum Option<T> {
                case some(T), none
            }
            func create_some(x: Int) -> Option<Int> {
                .some(x)
            }
            create_some(42)
            ",
        );

        let call_result = checker.type_for(checker.root_ids()[2]).unwrap();
        assert_eq!(call_result, Ty::Enum(SymbolID::typed(1), vec![Ty::Int])); // Option<Int>
    }

    #[test]
    fn checks_complex_generic_constraints() {
        let checker = check(
            "
            enum Either<L, R> {
                case left(L), right(R)
            }
            func swap(e: Either<Int, Float>) -> Either<Float, Int> {
                match e {
                    .left(i) -> .right(i)
                    .right(f) -> .left(f)
                }
            }
            ",
        );

        let func_ty = checker.type_for(checker.root_ids()[1]).unwrap();
        match func_ty {
            Ty::Func(params, ret, _) => {
                // Input: Either<Int, Float>
                assert_eq!(
                    params[0],
                    Ty::Enum(SymbolID::typed(1), vec![Ty::Int, Ty::Float])
                );
                // Output: Either<Float, Int>
                assert_eq!(*ret, Ty::Enum(SymbolID::typed(1), vec![Ty::Float, Ty::Int]));
            }
            _ => panic!("Expected function type"),
        }
    }

    #[test]
    fn checks_builtin_optional() {
        let checker = check(
            "
        let x = Optional.some(42)
        let y = Optional.none
        
        match x {
            .some(val) -> val
            .none -> 0
        }
        ",
        );

        // x should be Optional<Int>
        let x_ty = checker.type_for(checker.root_ids()[0]).unwrap();
        assert_eq!(x_ty, Ty::Int.optional());
        match x_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::OPTIONAL); // Optional's ID
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Optional<Int>, got {x_ty:?}"),
        }

        // The match should return Int
        let match_ty = checker.type_for(checker.root_ids()[2]).unwrap();
        assert_eq!(match_ty, Ty::Int);
    }

    #[test]
    fn checks_polymorphic_match() {
        let checker = check(
            "
            func map<U, T>(opt: T?, f: (T) -> U) -> U? {
                match opt {
                    .some(value) -> .some(f(value))
                    .none -> .none
                }
            }

            map(.some(123), func(foo) { foo })
            ",
        );

        // Should type check without errors - polymorphic function
        let Ty::Func(args, ret, _) = checker.type_for(checker.root_ids()[0]).unwrap() else {
            panic!("did not get func")
        };

        assert_eq!(
            args[0],
            Ty::Enum(
                SymbolID::OPTIONAL,
                vec![Ty::TypeVar(TypeVarID(
                    6,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::typed(3), "T".into()))
                ))]
            )
        );
        assert_eq!(
            args[1],
            Ty::Func(
                vec![Ty::TypeVar(TypeVarID(
                    6,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::resolved(3), "T".into()))
                ))],
                Ty::TypeVar(TypeVarID(
                    5,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::resolved(2), "U".into()))
                ))
                .into(),
                vec![]
            )
        );
        assert_eq!(
            ret,
            Ty::Enum(
                SymbolID(1),
                vec![Ty::TypeVar(TypeVarID(
                    5,
                    TypeVarKind::TypeRepr(Name::Resolved(SymbolID::resolved(2), "U".into()))
                ))]
            )
            .into()
        );

        let call_result = checker.type_for(checker.root_ids()[1]).unwrap();
        match call_result {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::OPTIONAL); // Optional's ID
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Optional<Int>, got {call_result:?}"),
        }
    }

    #[test]
    fn checks_self() {
        let checked = check(
            "enum Fizz {
            func buzz() {
                self
            }

            func foo() {
                123
            }
        }",
        );

        assert_eq!(
            checked.typed_roots()[0].ty,
            Ty::Enum(SymbolID::typed(1), vec![])
        );
        let Some(TypeDef::Enum(enum_def)) = checked.type_def(&SymbolID::typed(1)) else {
            panic!();
        };
        assert_eq!(enum_def.methods.len(), 2);
        assert_eq!(
            enum_def.methods.get("buzz").unwrap().ty,
            Ty::Func(
                vec![],
                Box::new(Ty::Enum(SymbolID::typed(1), vec![])),
                vec![]
            )
        );
        assert_eq!(
            enum_def.methods.get("foo").unwrap().ty,
            Ty::Func(vec![], Box::new(Ty::Int), vec![])
        );
    }

    #[test]
    fn checks_closure() {
        let checked = check(
            "
        let x = 1 
        func add(y) {
            x + y
        }
        ",
        );

        assert_eq!(
            checked.type_for(8).unwrap(),
            Ty::Closure {
                func: Ty::Func(vec![Ty::Int], Ty::Int.into(), vec![]).into(),
                captures: vec![Ty::Int]
            }
        );
    }

    #[test]
    fn checks_array() {
        let checked = check(
            "
            [1,2,3]
        ",
        );

        assert_eq!(
            checked.type_for(checked.root_ids()[0]).unwrap(),
            Ty::Struct(SymbolID::ARRAY, vec![Ty::Int])
        );
    }

    #[test]
    fn checks_array_builtin() {
        let checked = check("func c(a: Array<Int>) { a }");
        let root = checked.typed_expr(&checked.root_ids()[0]).unwrap();
        assert_eq!(
            root.ty,
            Ty::Func(
                vec![Ty::Struct(SymbolID::ARRAY, vec![Ty::Int])],
                Ty::Struct(SymbolID::ARRAY, vec![Ty::Int]).into(),
                vec![],
            )
        );
    }

    #[test]
    fn checks_arrays_with_polymorphism() {
        let checked = check(
            "
        func identity(a) { a }
        identity([1,2,3])
        identity([1.0, 2.0, 3.0])
        ",
        );

        assert_eq!(
            checked.type_for(checked.root_ids()[1]).unwrap(),
            Ty::Struct(SymbolID::ARRAY, vec![Ty::Int])
        );
        assert_eq!(
            checked.type_for(checked.root_ids()[2]).unwrap(),
            Ty::Struct(SymbolID::ARRAY, vec![Ty::Float])
        );
    }
}

#[cfg(test)]
mod pending {
    use talk::{
        SourceFile, Typed,
        diagnostic::Diagnostic,
        type_checker::{Ty, TypeError},
    };

    fn check_err(code: &'static str) -> Result<SourceFile<Typed>, TypeError> {
        talk::check(code)
    }

    fn check(code: &'static str) -> Ty {
        let typed = check_err(code).unwrap();
        typed.type_for(typed.root_ids()[0]).unwrap()
    }

    // #[test]
    // fn checks_match_exhaustiveness_error() {
    //     // This should fail type checking due to non-exhaustive match
    //     let result = std::panic::catch_unwind(|| {
    //         check(
    //             "
    //             enum Bool {
    //                 case yes, no
    //             }
    //             func test(b: Bool) -> Int {
    //                 match b {
    //                     .yes -> 1
    //                 }
    //             }
    //             ",
    //         )
    //     });

    //     // Should panic or return error - depends on your error handling
    //     assert!(result.is_err());
    // }

    #[test]
    fn checks_literal_true() {
        assert_eq!(check("true"), Ty::Bool);
    }

    #[test]
    fn checks_literal_false() {
        assert_eq!(check("false"), Ty::Bool);
    }

    #[test]
    fn checks_if_expression() {
        assert_eq!(check("if true { 1 } else { 0 }"), Ty::Int);
    }

    #[test]
    fn checks_if_expression_without_else() {
        assert_eq!(check("if true { 1 }"), Ty::Int.optional());
    }

    #[test]
    fn checks_if_expression_with_non_bool_condition() {
        let checked = check_err("if 123 { 1 }").unwrap();
        assert_eq!(checked.diagnostics().len(), 1);
    }

    #[test]
    fn checks_loop_expression() {
        assert_eq!(check("loop { 1 }"), Ty::Void);
    }

    #[test]
    fn checks_loop_expression_with_condition() {
        assert_eq!(check("loop true { 1 }"), Ty::Void);
    }

    #[test]
    fn checks_loop_expression_with_invalid_condition() {
        let checked = check_err("loop 1.2 { 1 }").unwrap();
        assert_eq!(checked.diagnostics().len(), 1);
        assert!(
            checked.diagnostics.contains(&Diagnostic::typing(
                0,
                TypeError::UnexpectedType(Ty::Bool, Ty::Float)
            )),
            "{:?}",
            checked.diagnostics
        )
    }

    #[test]
    fn checks_tuple_expression() {
        assert_eq!(check("(1, true)"), Ty::Tuple(vec![Ty::Int, Ty::Bool]));
    }

    #[test]
    fn checks_unit_tuple_expression() {
        assert_eq!(check("()"), Ty::Tuple(vec![]));
    }

    #[test]
    fn checks_tuple_expectations() {
        let checked = check_err(
            "
            let my_tuple: (Int, Bool) = (42, 10)
            ",
        )
        .unwrap();

        assert_eq!(checked.diagnostics().len(), 1);
    }

    #[test]
    fn checks_grouping_expression() {
        assert_eq!(check("(1)"), Ty::Int);
    }

    #[test]
    fn checks_unary_expression() {
        check("-1"); // Assuming '-' is a unary op
    }

    #[test]
    fn checks_binary_expression() {
        check("1 + 2");
    }

    #[test]
    fn checks_void_expr() {
        assert_eq!(
            check(
                "func foo() {
            return
        }()"
            ),
            Ty::Void
        );
    }

    #[test]
    fn checks_return_err() {
        let checked = check_err(
            "func foo() -> Int {
                return
            }()",
        )
        .unwrap();
        assert_eq!(checked.diagnostics().len(), 2);
    }

    #[test]
    fn checks_return_infer() {
        assert_eq!(
            check(
                "func foo(x) {
            return x
            123
        }"
            ),
            Ty::Func(vec![Ty::Int], Ty::Int.into(), vec![])
        );
    }

    #[test]
    fn checks_return_expr() {
        assert_eq!(
            check(
                "func foo() {
            return 123
        }()"
            ),
            Ty::Int
        );
    }

    #[test]
    fn checks_pattern_literal_int_in_match() {
        check(
            "
            enum MyEnum {
                case val(Int)
            }
            func test(e: MyEnum) {
                match e {
                    .val(1) -> 0
                }
            }
        ",
        );
    }

    #[test]
    #[should_panic]
    fn checks_pattern_wildcard_in_match() {
        check(
            "
            enum MyEnum { case Val(Int) }
            func test(e: MyEnum) {
                match e {
                    _ -> 0 // Pattern::Wildcard
                }
            }
        ",
        );
    }
}
