#[cfg(test)]
mod tests {
    use crate::{
        SymbolID, check, check_without_prelude, expr::Expr, ty::Ty, typed_expr::TypedExpr,
    };

    #[test]
    fn checks_initializer() {
        let checked = check_without_prelude(
            "
        struct Person {
            let age: Int

            init(age: Int) {
                self.age = age
            }
        }

        Person(age: 123)
        ",
        )
        .unwrap();

        assert_eq!(
            checked.type_for(&checked.root_ids()[1]).unwrap(),
            Ty::Struct(SymbolID(1), vec![])
        );

        let Some(TypedExpr {
            expr: Expr::Call { callee, .. },
            ..
        }) = checked.typed_expr(&checked.root_ids()[1])
        else {
            panic!("did not get call")
        };

        let Some(ty) = checked.type_for(&callee) else {
            panic!("did not get callee")
        };

        assert_eq!(ty, Ty::Init(SymbolID(1), vec![Ty::Int]));
    }

    #[test]
    fn checks_generic_init() {
        let checked = check_without_prelude(
            "
        struct Person<T> {
            init() {
            }

            func foo(t: T) { t }
        }

        Person().foo(1)
        Person().foo(1.23)
        ",
        )
        .unwrap();

        let Some(TypedExpr {
            expr: Expr::Call { .. },
            ..
        }) = checked.typed_expr(&checked.root_ids()[1])
        else {
            panic!("did not get call")
        };

        let Some(TypedExpr {
            expr: Expr::Call { callee, .. },
            ..
        }) = checked.typed_expr(&checked.root_ids()[2])
        else {
            panic!("did not get call")
        };

        let Some(Ty::Func(_, box ret, _)) = checked.type_for(&callee) else {
            panic!("did not get callee")
        };

        assert_eq!(ret, Ty::Float);
    }

    #[test]
    fn checks_property() {
        let checked = check_without_prelude(
            "
        struct Person {
            let age: Int
        }

        Person(age: 123).age
        ",
        )
        .unwrap();

        assert_eq!(checked.type_for(&checked.root_ids()[1]).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_method() {
        let checked = check_without_prelude(
            "
        struct Person {
            let age: Int

            func getAge() {
                self.age
            }
        }

        Person(age: 123).getAge()
        ",
        )
        .unwrap();

        assert_eq!(checked.type_for(&checked.root_ids()[1]).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_method_out_of_order() {
        let checked = check_without_prelude(
            "
        struct Person {
            let age: Int

            func getAge() {
                self.getAgeAgain()
            }

            func getAgeAgain() {
                self.age
            }
        }
        let person = Person(age: 123)
        person.getAge()
        ",
        )
        .unwrap();

        assert_eq!(checked.type_for(&checked.root_ids()[2]).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_constructor_args() {
        let checked = check_without_prelude(
            "struct Person {
                let age: Int

                func getAge() {
                    self.age
                }
            }

            Person()",
        )
        .unwrap();

        assert_eq!(checked.diagnostics().len(), 1);
    }

    #[test]
    fn checks_setter() {
        let checked = check(
            "struct Person {
                let age: Int
            }

            Person(age: 1).age = 1.2",
        )
        .unwrap();

        assert!(checked.diagnostics().len() >= 1);
    }
}

#[cfg(test)]
mod type_tests {
    use crate::{
        SymbolID, check_without_prelude,
        environment::TypeDef,
        expr::Expr,
        ty::Ty,
        type_checking::CheckResult,
        type_var_id::{TypeVarID, TypeVarKind},
    };

    fn check(code: &'static str) -> CheckResult {
        crate::check(code).unwrap()
    }

    #[test]
    fn checks_an_int() {
        let checker = check("123");
        assert_eq!(checker.type_for(&checker.root_ids()[0]).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_a_float() {
        let checker = check("123.");
        assert_eq!(checker.type_for(&checker.root_ids()[0]).unwrap(), Ty::Float);
    }

    #[test]
    fn checks_a_named_func() {
        let checker = check("func sup(name) { name }\nsup");
        let root_id = checker.root_ids()[0];

        let Ty::Func(params, return_type, _) = checker.type_for(&root_id).unwrap() else {
            panic!(
                "didnt get a func, got: {:#?}",
                checker.type_for(&root_id).unwrap()
            );
        };

        let param_type = params[0].clone();

        assert_eq!(return_type, param_type.into());

        let Ty::TypeVar(TypeVarID(_, TypeVarKind::FuncParam(name))) = *return_type else {
            panic!("did not get func param type var");
        };

        assert_eq!(name, "name".to_string());

        // The second root-expr is the *use* of `sup`.
        let Ty::Func(params2, return_type2, _) = checker.type_for(&checker.root_ids()[1]).unwrap()
        else {
            panic!(
                "expected `sup` to be a function, got: {:?}",
                checker.type_for(&checker.root_ids()[1]).unwrap()
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
        let Ty::Func(params, return_type, _) = checker.type_for(&root_id).unwrap() else {
            panic!(
                "didnt get a func, got: {:#?}",
                checker.type_for(&root_id).unwrap()
            );
        };

        assert_eq!(params, vec![Ty::Int]);
        assert_eq!(*return_type, Ty::Int);
    }

    #[test]
    fn checks_call() {
        let checker = check_without_prelude(
            "
        func fizz(c) { c }
        fizz(c: 123)
        ",
        )
        .unwrap();
        let root_id = checker.root_ids()[1];
        assert_eq!(checker.type_for(&root_id).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_a_let_assignment() {
        let checker = check_without_prelude("let count = 123\ncount").unwrap();
        let root_id = checker.root_ids()[1];
        assert_eq!(checker.type_for(&root_id).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_apply_twice() {
        let checker = check_without_prelude(
            "
        func applyTwice(f, x) { f(f(x)) }
        applyTwice
        ",
        )
        .unwrap();

        let root_id = checker.root_ids()[0];
        let Ty::Func(params, return_type, _) = checker.type_for(&root_id).unwrap() else {
            panic!(
                "expected `applyTwice` to be a function, got: {:?}",
                checker.type_for(&root_id).unwrap()
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
        let checked = check_without_prelude(
            "
        func fizz<T>(ty: T) { T }

        fizz<Int>(123)
        fizz<Bool>(true)
        ",
        )
        .unwrap();

        assert_eq!(checked.type_for(&checked.root_ids()[1]).unwrap(), Ty::Int);
        assert_eq!(checked.type_for(&checked.root_ids()[2]).unwrap(), Ty::Bool);
    }

    #[test]
    fn checks_composition() {
        let checker = check_without_prelude(
            "
        func compose(f, g) {
            func inner(x) { f(g(x)) }
            inner
        }
        compose
        ",
        )
        .unwrap();
        let root_id = checker.root_ids()[0];
        let Ty::Func(params, return_type, _) = checker.type_for(&root_id).unwrap() else {
            panic!(
                "expected `compose` to be a function, got: {:?}",
                checker.type_for(&root_id).unwrap()
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

        let Ty::TypeVar(TypeVarID(_, TypeVarKind::Instantiated(inner_id))) = inner_params[0] else {
            panic!("didn't get innerid");
        };

        let Ty::TypeVar(TypeVarID(g_arg, _)) = g_args[0] else {
            panic!("didn't get arg: {:?}", g_args[0]);
        };

        assert_eq!(inner_id, g_arg);

        let Ty::TypeVar(TypeVarID(_, TypeVarKind::Instantiated(inner_ret))) = *inner_ret else {
            panic!("didn't get inner_ret");
        };

        let Ty::TypeVar(TypeVarID(f_ret, _)) = *f_ret else {
            panic!("didn't get f_ret: {:?}", f_ret);
        };

        assert_eq!(inner_ret, f_ret); // inner returns C
    }

    #[test]
    fn checks_simple_recursion() {
        let checker = check_without_prelude(
            "
        func rec(n) {
            rec(n)
        }
        rec
        ",
        )
        .unwrap();

        // the bare `rec` at the top level should be a Func([α], α)
        let root_id = checker.root_ids()[0];
        let ty = checker.type_for(&root_id).unwrap();
        let Ty::Func(params, ret, _) = ty else {
            panic!("didn't get closure for ty: {ty:?}");
        };
        // exactly one parameter
        assert_eq!(params.len(), 1);
        // return type equals the parameter type
        let Ty::TypeVar(TypeVarID(_, _call_ret)) = *ret else {
            panic!("didn't get call return");
        };
    }

    #[test]
    fn checks_mutual_recursion() {
        let checker = check_without_prelude(
            "
        func even(n: Int) -> Int {
            odd(n)
        }
        func odd(n: Int) -> Int {
            even(n)
        }
        even
        ",
        )
        .unwrap();

        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let root_id = checker.root_ids()[0];
        let ty = checker.type_for(&root_id).unwrap();
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
        let checked = check_without_prelude(
            "
        enum Maybe<T> {
          case definitely(T), nope
        }

        let maybe = Maybe.definitely(123)
        maybe
        ",
        )
        .unwrap();

        assert_eq!(
            checked.type_for(&checked.root_ids()[2]).unwrap(),
            Ty::EnumVariant(SymbolID(1), vec![Ty::Int]),
        );
    }

    #[test]
    fn infers_identity() {
        let checker = check_without_prelude(
            "
            func identity(arg) { arg }
            identity(1)
            identity(2.0)
        ",
        )
        .unwrap();

        assert_eq!(checker.type_for(&checker.root_ids()[1]).unwrap(), Ty::Int);
        assert_eq!(checker.type_for(&checker.root_ids()[2]).unwrap(), Ty::Float);
    }

    #[test]
    fn updates_definition() {
        let checker = check_without_prelude(
            "
            struct Person {}

            let person = Person()

            person
        ",
        )
        .unwrap();

        let symbols = checker.symbols.all();
        let person_local = symbols
            .values()
            .find_map(|info| {
                if info.name == "person" {
                    Some(info)
                } else {
                    None
                }
            })
            .unwrap();
        let person_struct = symbols
            .iter()
            .find_map(|(id, info)| {
                if info.name == "Person" {
                    Some(id)
                } else {
                    None
                }
            })
            .unwrap();

        assert_eq!(person_local.name, "person");
        assert_eq!(
            person_local.definition.as_ref().unwrap().sym.unwrap(),
            *person_struct
        );
        assert_eq!(
            checker.type_for(&checker.root_ids()[1]).unwrap(),
            Ty::Struct(*person_struct, vec![])
        );
    }

    #[test]
    fn checks_simple_enum_declaration() {
        let checker = check_without_prelude(
            "
            enum Fizz {
                case foo, bar
            }
        ",
        )
        .unwrap();

        assert_eq!(
            checker.type_for(&checker.root_ids()[0]).unwrap(),
            Ty::Enum(SymbolID(1), vec![])
        );

        let Some(Expr::EnumDecl { body, .. }) = checker.source_file.get(&checker.root_ids()[0])
        else {
            panic!("didn't get enum decl");
        };

        let Some(Expr::Block(body_ids)) = checker.source_file.get(body) else {
            panic!("didn't get enum body");
        };

        // Check the variants
        assert_eq!(
            checker.type_for(&body_ids[0]).unwrap(),
            Ty::EnumVariant(SymbolID(1), vec![])
        );
        assert_eq!(
            checker.type_for(&body_ids[1]).unwrap(),
            Ty::EnumVariant(SymbolID(1), vec![])
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
            checker.type_for(&checker.root_ids()[0]).unwrap(),
            Ty::Enum(SymbolID::typed(1), vec![])
        );

        let Some(Expr::EnumDecl { body, .. }) = checker.source_file.get(&checker.root_ids()[0])
        else {
            panic!("didn't get enum decl");
        };

        let Some(Expr::Block(body_ids)) = checker.source_file.get(body) else {
            panic!("didn't get enum body");
        };

        // Check variant types
        assert_eq!(
            checker.type_for(&body_ids[0]).unwrap(),
            Ty::EnumVariant(SymbolID::typed(1), vec![Ty::Int]),
        );
        assert_eq!(
            checker.type_for(&body_ids[1]).unwrap(),
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

        let enum_ty = checker.type_for(&checker.root_ids()[0]).unwrap();
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
        let call_result = checker.type_for(&checker.root_ids()[1]).unwrap();
        assert_eq!(
            call_result,
            Ty::EnumVariant(SymbolID::typed(1), vec![Ty::Int])
        );
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
        let call1 = checker.type_for(&checker.root_ids()[1]).unwrap();
        match call1 {
            Ty::EnumVariant(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Option<Int>, got {call1:?}"),
        }

        // Second call should be Option<Float>
        let call2 = checker.type_for(&checker.root_ids()[2]).unwrap();
        match call2 {
            Ty::EnumVariant(symbol_id, generics) => {
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
        let result_ty = checker.type_for(&checker.root_ids()[2]).unwrap();
        match result_ty {
            Ty::EnumVariant(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(5)); // Result enum
                assert_eq!(generics.len(), 1);

                // First generic should be Option<Int>
                match &generics[0] {
                    Ty::EnumVariant(opt_id, opt_generics) => {
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
        let func_ty = checker.type_for(&checker.root_ids()[1]).unwrap();
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
        let func_ty = checker.type_for(&checker.root_ids()[1]).unwrap();
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

        let enum_ty = checker.type_for(&checker.root_ids()[0]).unwrap();
        match enum_ty {
            Ty::Enum(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::typed(1));
                assert_eq!(generics.len(), 1);
            }
            _ => panic!("Expected List<T> type, got {enum_ty:?}"),
        }

        let Some(Expr::EnumDecl { body, .. }) = checker.expr(&checker.root_ids()[0]) else {
            panic!("did not get enum decl");
        };

        let Some(Expr::Block(exprs)) = checker.expr(&body) else {
            panic!("did not get body");
        };

        // Check cons variant has recursive structure: T, List<T>
        let cons_variant = checker.type_for(&exprs[0]);
        match cons_variant {
            Some(Ty::EnumVariant(enum_id, field_types)) => {
                assert_eq!(enum_id, SymbolID::typed(1));
                assert_eq!(field_types.len(), 2);
                // Second field should be List<T> (recursive reference)
                match &field_types[1] {
                    Ty::Enum(list_id, _) => assert_eq!(*list_id, enum_id),
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
        let call_result = checker.type_for(&checker.root_ids()[2]).unwrap();
        assert_eq!(call_result, Ty::Int);
    }

    #[test]
    fn checks_multiple_enum_parameters() {
        let checker = check_without_prelude(
            "
            enum Boolean {
                case yes, no
            }
            func and(a: Boolean, b: Boolean) -> Boolean {
                match a {
                    .yes -> b
                    .no -> .no
                }
            }
            and(.yes, .no)
            ",
        )
        .unwrap();

        let call_result = checker.type_for(&checker.root_ids()[2]).unwrap();
        assert_eq!(call_result, Ty::Enum(SymbolID(1), vec![])); // Bool
    }

    #[test]
    fn checks_enum_as_return_type() {
        let checker = check_without_prelude(
            "
            enum Option<T> {
                case some(T), none
            }
            func create_some(x: Int) -> Option<Int> {
                .some(x)
            }
            create_some(42)
            ",
        )
        .unwrap();

        let call_result = checker.type_for(&checker.root_ids()[2]).unwrap();
        assert_eq!(call_result, Ty::Enum(SymbolID(1), vec![Ty::Int])); // Option<Int>
    }

    #[test]
    fn checks_complex_generic_constraints() {
        let checker = check_without_prelude(
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
        )
        .unwrap();

        let func_ty = checker.type_for(&checker.root_ids()[1]).unwrap();
        match func_ty {
            Ty::Func(params, ret, _) => {
                // Input: Either<Int, Float>
                assert_eq!(params[0], Ty::Enum(SymbolID(1), vec![Ty::Int, Ty::Float]));
                // Output: Either<Float, Int>
                assert_eq!(*ret, Ty::Enum(SymbolID(1), vec![Ty::Float, Ty::Int]));
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

        Optional.some(123)
        ",
        );

        // x should be Optional<Int>
        let x_ty = checker.type_for(&checker.root_ids()[0]).unwrap();
        assert_eq!(x_ty, Ty::Int.optional());
        match x_ty {
            Ty::EnumVariant(symbol_id, generics) => {
                assert_eq!(symbol_id, SymbolID::OPTIONAL); // Optional's ID
                assert_eq!(generics, vec![Ty::Int]);
            }
            _ => panic!("Expected Optional<Int>, got {x_ty:?}"),
        }

        // The match should return Int
        let match_ty = checker.type_for(&checker.root_ids()[2]).unwrap();
        assert_eq!(match_ty, Ty::Int);
        assert_eq!(
            checker.type_for(&checker.root_ids()[3]).unwrap(),
            Ty::Int.optional()
        );
    }

    #[test]
    fn checks_polymorphic_match() {
        let checker = check_without_prelude(
            "
            enum O<I> {
                case some(I), none
            }

            func map<U, T>(opt: O<T>, f: (T) -> U) -> O<U> {
                match opt {
                    .some(value) -> .some(f(value))
                    .none -> .none
                }
            }

            map(.some(123), func(foo) { foo })
            ",
        )
        .unwrap();

        // Should type check without errors - polymorphic function
        let Some(Ty::Func(args, _ret, _)) = checker.type_for(&checker.root_ids()[1]) else {
            panic!(
                "did not get func: {:?}",
                checker.type_for(&checker.root_ids()[1])
            )
        };

        let Ty::Enum(symbol_id, _type_params) = &args[0] else {
            panic!("didn't get enum_ty");
        };

        // assert!(
        //     matches!(
        //         type_params[0],
        //         Ty::TypeVar(TypeVarID(_, TypeVarKind::TypeRepr(Name::Resolved(_, _)),),),
        //     ),
        //     "{:?}",
        //     type_params[0]
        // );

        assert_eq!(*symbol_id, SymbolID(1));

        let Ty::Func(params, ret, _) = &args[1] else {
            panic!("didn't get func");
        };

        assert_eq!(1, params.len());
        let Ty::TypeVar(TypeVarID(_, TypeVarKind::Placeholder(t))) = &params[0] else {
            panic!("didn't get T: {:?}", params[0]);
        };
        assert_eq!(*t, "T");

        let box Ty::TypeVar(TypeVarID(_, TypeVarKind::Placeholder(u))) = ret else {
            panic!("didn't get U: {:?}", ret);
        };
        assert_eq!(*u, "U");

        let call_result = checker.type_for(&checker.root_ids()[2]).unwrap();
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
            checked.type_for(&checked.root_ids()[0]),
            Some(Ty::Enum(SymbolID::typed(1), vec![]))
        );
        let Some(TypeDef::Enum(enum_def)) = checked.env.lookup_type(&SymbolID::typed(1)) else {
            panic!();
        };
        assert_eq!(enum_def.methods.len(), 2);
        assert_eq!(
            checked
                .type_for(
                    &TypeDef::Enum(enum_def.clone())
                        .find_method("buzz")
                        .unwrap()
                        .expr_id
                )
                .unwrap(),
            Ty::Func(
                vec![],
                Box::new(Ty::Enum(SymbolID::typed(1), vec![])),
                vec![]
            )
        );
        assert_eq!(
            checked
                .type_for(
                    &TypeDef::Enum(enum_def.clone())
                        .find_method("foo")
                        .unwrap()
                        .expr_id
                )
                .unwrap(),
            Ty::Func(vec![], Box::new(Ty::Int), vec![])
        );
    }

    #[test]
    fn checks_closure() {
        let checked = check_without_prelude(
            "
        let x = 1 
        func add(y) {
            x + y
        }
        add(2)
        ",
        )
        .unwrap();

        assert_eq!(
            checked.type_for(&checked.root_ids()[1]).unwrap(),
            Ty::Closure {
                func: Ty::Func(vec![Ty::Int], Ty::Int.into(), vec![]).into(),
                captures: vec![SymbolID(2)]
            }
        );

        let Some(Expr::Func { body, .. }) = checked.source_file.get(&checked.root_ids()[1]) else {
            panic!("no body");
        };

        let Some(Expr::Block(ids)) = checked.source_file.get(&body) else {
            panic!("didn't get body");
        };

        let Some(Expr::Binary(lhs, _, _)) = checked.source_file.get(&ids[0]) else {
            panic!("didn't get binary expr");
        };

        assert_eq!(checked.type_for(&lhs).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_array() {
        let checked = check(
            "
            [1,2,3]
        ",
        );

        assert_eq!(
            checked.type_for(&checked.root_ids()[0]).unwrap(),
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
    fn checks_array_get() {
        let checked = check(
            "
        let a = [1,2,3]
        a.get(0)
        ",
        );

        assert_eq!(checked.type_for(&checked.root_ids()[1]).unwrap(), Ty::Int);
    }

    #[test]
    fn checks_arrays_with_polymorphism() {
        let checked = check(
            "
        func identity(a) { a }
        identity([1,2,3])
        identity([1.0, 2.0, 3.0])
        [1,2,3]
        ",
        );

        assert_eq!(
            checked.type_for(&checked.root_ids()[1]).unwrap(),
            Ty::Struct(SymbolID::ARRAY, vec![Ty::Int])
        );
        assert_eq!(
            checked.type_for(&checked.root_ids()[2]).unwrap(),
            Ty::Struct(SymbolID::ARRAY, vec![Ty::Float])
        );
    }
}

#[cfg(test)]
mod pending {
    use crate::{
        check_without_prelude, diagnostic::Diagnostic, ty::Ty, type_checker::TypeError,
        type_checking::CheckResult,
    };

    fn check_err(code: &'static str) -> Result<CheckResult, TypeError> {
        check_without_prelude(code)
    }

    fn check(code: &'static str) -> Ty {
        let typed = check_without_prelude(code).unwrap();
        typed.type_for(&typed.root_ids()[0]).unwrap()
    }

    #[test]
    #[ignore = "wip"]
    fn checks_match_exhaustiveness_error() {
        // This should fail type checking due to non-exhaustive match
        let result = std::panic::catch_unwind(|| {
            check(
                "
                enum Bool {
                    case yes, no
                }
                func test(b: Bool) -> Int {
                    match b {
                        .yes -> 1
                    }
                }
                ",
            )
        });

        // Should panic or return error - depends on your error handling
        assert!(result.is_err());
    }

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
            checked.diagnostics().contains(&&Diagnostic::typing(
                checked.root_ids()[0] - 3,
                TypeError::UnexpectedType(Ty::Bool, Ty::Float)
            )),
            "{:?}",
            checked.diagnostics()
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
        assert_eq!(check("-1"), Ty::Int);
    }

    #[test]
    fn checks_binary_expression() {
        assert_eq!(check("1 + 2"), Ty::Int);
        assert_eq!(check("1.1 + 2.1"), Ty::Float);
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

        assert_eq!(checked.diagnostics().len(), 1);
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
        let checked = check_without_prelude(
            "
            enum MyEnum {
                case val(Int)
            }
            func test(e: MyEnum) {
                match e {
                    .val(1) -> 0
                    .val(2) -> 1
                }
            }
            test(.val(1))
        ",
        )
        .unwrap();

        assert_eq!(checked.type_for(&checked.root_ids()[2]).unwrap(), Ty::Int);
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

#[cfg(test)]
mod protocol_tests {
    use crate::{SymbolID, check_without_prelude, environment::TypeDef};

    #[test]
    fn infers_protocol_conformance() {
        let checked = check_without_prelude(
            "
        protocol Aged {
            func getAge() -> Int
        }
        struct Person: Aged {
            func getAge() {
                123
            }
        }
        ",
        )
        .unwrap();

        let Some(TypeDef::Struct(person_def)) = checked.env.lookup_type(&SymbolID(3)) else {
            panic!("didn't get person: {:?}", checked.env.types);
        };

        let Some(TypeDef::Protocol(aged_def)) = checked.env.lookup_type(&SymbolID(1)) else {
            panic!("didn't get aged protocol: {:#?}", checked.env.types);
        };

        assert!(
            person_def.conformances.contains(&aged_def.symbol_id),
            "{:#?}",
            person_def.conformances
        );
    }

    #[test]
    fn infers_protocol_property() {
        let checked = check_without_prelude(
            "
        protocol Aged {
            let age: Int
        }
        struct Person: Aged {
            let age: Int
        }
        func get<T: Aged>(aged: T) {
            aged.age
        }
        ",
        )
        .unwrap();

        let Some(TypeDef::Struct(person_def)) = checked.env.lookup_type(&SymbolID(3)) else {
            panic!("didn't get person: {:?}", checked.env.types);
        };

        let Some(TypeDef::Protocol(aged_def)) = checked.env.lookup_type(&SymbolID(1)) else {
            panic!("didn't get aged protocol: {:#?}", checked.env.types);
        };

        assert!(
            person_def.conformances.contains(&aged_def.symbol_id),
            "{:#?}",
            person_def.conformances
        );
    }
}
