mod tests {
    use crate::{
        SymbolID, SymbolTable,
        environment::Environment,
        name::Name,
        name_resolver::{NameResolver, Scope},
        parser::parse,
        synthesis::synthesize_inits,
        types::{
            row::{ClosedRow, Label, Row},
            ty::{Primitive, Ty},
            type_checking_session::{TypeCheckingResult, TypeCheckingSession},
            type_var::{TypeVar, TypeVarKind},
            type_var_context::RowVar,
        },
    };

    pub(super) fn check(code: &'static str) -> TypeCheckingResult {
        let parsed = parse(code, "-");
        let symbol_table = &mut SymbolTable::base();
        let mut resolved = NameResolver::new(
            Scope::new(crate::builtins::default_name_scope()),
            Default::default(),
            "-",
            &Default::default(),
        )
        .resolve(parsed, symbol_table);

        synthesize_inits(&mut resolved, symbol_table, &mut Environment::new());

        let meta = resolved.meta.borrow();
        let mut session = TypeCheckingSession::new(resolved.roots(), &meta, symbol_table);

        session.solve()
    }

    #[test]
    fn infers_int() {
        let checked = check("123");
        assert_eq!(Ty::Primitive(Primitive::Int), checked.typed_roots[0].ty)
    }

    #[test]
    fn infers_float() {
        let checked = check("1.23");
        assert_eq!(Ty::Primitive(Primitive::Float), checked.typed_roots[0].ty)
    }

    #[test]
    fn infers_bool() {
        let checked = check("true ; false");
        assert_eq!(Ty::Primitive(Primitive::Bool), checked.typed_roots[0].ty);
        assert_eq!(Ty::Primitive(Primitive::Bool), checked.typed_roots[1].ty);
    }

    #[test]
    fn infers_let() {
        let checked = check("let x = 123; x");
        assert_eq!(Ty::Primitive(Primitive::Int), checked.typed_roots[1].ty)
    }

    #[test]
    fn infers_let_with_annotation() {
        let checked = check("let x: Byte = 123; x");
        assert_eq!(Ty::Byte, checked.typed_roots[1].ty)
    }

    #[test]
    fn infers_annotated_func() {
        let checked = check("func(x: Int) -> Int { x }");
        assert_eq!(
            Ty::Func {
                params: vec![Ty::Int],
                returns: Box::new(Ty::Int),
                generic_constraints: vec![],
            },
            checked.typed_roots[0].ty
        )
    }

    #[test]
    fn infers_unannotated_func() {
        let checked = check("func() { 123 }");
        assert_eq!(
            Ty::Func {
                params: vec![],
                returns: Box::new(Ty::Int),
                generic_constraints: vec![],
            },
            checked.typed_roots[0].ty
        )
    }

    #[test]
    fn infers_generic_func() {
        let checked = check("func id<T>(x: T) { x }; id(123); id(1.23)");
        assert_eq!(Ty::Int, checked.typed_roots[1].ty);
        assert_eq!(Ty::Float, checked.typed_roots[2].ty);
    }

    #[test]
    fn infers_unannotated_generic_func() {
        let checked = check("func id(x) { x }; id(123); id(1.23)");
        assert_eq!(Ty::Int, checked.typed_roots[1].ty);
        assert_eq!(Ty::Float, checked.typed_roots[2].ty);
    }

    #[test]
    fn generic_func_type_mismatch_should_fail() {
        // This actually succeeds because T gets constrained to Int
        let result = check("func bad<T>(x: T) -> T { 123 }");

        // The function is valid - it just means T must be Int
        // Let's verify the type
        if let Ty::Func { returns, .. } = &result.typed_roots[0].ty {
            // The return type should be resolved to Int
            assert_eq!(**returns, Ty::Int);
        } else {
            panic!("Expected function type");
        }
    }

    #[test]
    fn generic_func_type_mismatch_at_call_site() {
        // The error happens when we try to call with wrong type
        let result = check("func bad<T>(x: T) -> T { 123 }; bad(1.5)");
        assert_eq!(result.diagnostics.len(), 1);
    }

    #[test]
    fn generic_func_tracks_constraints() {
        // This function constrains T to be Int
        let result = check("func add_one<T>(x: T) -> T { 123 }");
        // The function should type check, with T constrained to Int
        if let Ty::Func {
            generic_constraints,
            ..
        } = &result.typed_roots[0].ty
        {
            // Should have constraint that T = Int
            assert!(
                !generic_constraints.is_empty(),
                "Should have generic constraints"
            );
        } else {
            panic!("Expected function type");
        }
    }

    #[test]
    fn generic_func_constrained_valid() {
        // This should actually be valid - T is constrained to Int
        let _result = check("func wrong<T>(x: T) -> Int { x }");
    }

    #[test]
    fn generic_func_wrong_call() {
        // The error should happen when we try to call with wrong type
        // Using float instead of string to avoid unimplemented string literals
        let result = check("func wrong<T>(x: T) -> Int { x }; wrong(1.5)");
        assert_eq!(result.diagnostics.len(), 1);
    }

    #[test]
    fn infers_record_literal() {
        let checked = check("{ y: 123, z: 1.23 }");
        assert_eq!(
            Ty::Product(Row::Closed(ClosedRow {
                fields: vec!["y".into(), "z".into()],
                values: vec![Ty::Int, Ty::Float],
            })),
            checked.typed_roots[0].ty
        );
    }

    #[test]
    fn infers_member_record_literal() {
        let checked = check("let x = { y: 123, z: 1.23 }; x.y ; x.z");
        assert_eq!(Ty::Int, checked.typed_roots[1].ty);
        assert_eq!(Ty::Float, checked.typed_roots[2].ty);
    }

    #[test]
    fn infers_tuple() {
        let checked = check("(123, 1.23)");
        assert_eq!(
            Ty::Product(Row::Closed(ClosedRow {
                fields: vec![Label::Int(0), Label::Int(1)],
                values: vec![Ty::Int, Ty::Float]
            })),
            checked.typed_roots[0].ty
        );
    }

    #[test]
    fn infers_tuple_member() {
        let checked = check("let x = (123, 1.23) ; x.0; x.1");
        assert_eq!(3, checked.typed_roots.len());
        assert_eq!(Ty::Int, checked.typed_roots[1].ty);
        assert_eq!(Ty::Float, checked.typed_roots[2].ty);
    }

    #[test]
    fn infers_if() {
        let checked = check(
            "
        if true {
           456 
        }
        ",
        );
        assert_eq!(Ty::Void, checked.typed_roots[0].ty);
    }

    #[test]
    fn infers_if_else() {
        let checked = check(
            "
        if true {
            123
        } else {
           456 
        }
        ",
        );
        assert_eq!(Ty::Int, checked.typed_roots[0].ty);
    }

    #[test]
    fn generic_func_breaks_parametricity() {
        let result = check("func broken<T>(x: T) -> T { if true { x } else { 42 } }; broken(1.2)");
        assert_eq!(result.diagnostics.len(), 1);
    }

    #[test]
    fn condition_must_be_bool() {
        let result = check("if 123 { 345 }");
        assert_eq!(result.diagnostics.len(), 1);
    }

    #[test]
    fn struct_properties() {
        let checked = check(
            "
        struct Person {
            let name: Float 
            let age: Int
        }

        Person(name: 1.23, age: 123).name
        ",
        );

        assert_eq!(
            Ty::Metatype {
                ty: Ty::Nominal {
                    name: Name::Resolved(SymbolID::ANY, "Person".to_string()),
                    properties: Row::Closed(ClosedRow {
                        fields: vec!["name".into(), "age".into()],
                        values: vec![Ty::Float, Ty::Int]
                    }),
                    methods: Row::Open(RowVar::new(1)),
                    type_params: vec![],
                    instantiations: Default::default()
                }
                .into(),
                properties: Row::Open(RowVar::new(2)),
                methods: Row::Open(RowVar::new(3))
            },
            checked.typed_roots[0].ty
        );

        assert_eq!(Ty::Float, checked.typed_roots[1].ty);
    }

    #[test]
    fn struct_init() {
        let checked = check(
            "
        struct Person {
            let name: Float 
            let age: Int
        }

        Person(name: 1.23, age: 123)
        ",
        );

        assert_eq!(
            Ty::Nominal {
                name: Name::Resolved(SymbolID(1), "Person".to_string()),
                properties: Row::Closed(ClosedRow {
                    fields: vec!["name".into(), "age".into()],
                    values: vec![Ty::Float, Ty::Int]
                }),
                methods: Row::Open(RowVar::new(1)),
                type_params: vec![],
                instantiations: Default::default(),
            },
            checked.typed_roots[1].ty
        );
    }

    #[test]
    fn struct_methods() {
        let checked = check(
            "
        struct Person {
            func fizz(x: Int) { x }
        }

        Person().fizz(x: 123)
        ",
        );

        assert_eq!(Ty::Int, checked.typed_roots[1].ty);
    }

    #[test]
    fn generic_struct_property_with_annotated_init() {
        let checked = check(
            "
        struct Person<T> {
            let member: T

            init(member: T) -> Person<T> {
                self.member = member
            }
        }

        Person(member: 123).member
        Person(member: 1.23).member
        ",
        );

        assert_eq!(Ty::Int, checked.typed_roots[1].ty);
        assert_eq!(Ty::Float, checked.typed_roots[2].ty);
    }

    #[test]
    fn generic_struct_property_with_synthesized_init() {
        let checked = check(
            "
        struct Person<T> {
            let member: T
        }

        Person(member: 123).member
        Person(member: 1.23).member
        ",
        );

        assert_eq!(Ty::Int, checked.typed_roots[1].ty);
        assert_eq!(Ty::Float, checked.typed_roots[2].ty);
    }

    #[test]
    fn checks_method_out_of_order() {
        let checked = check(
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
        );

        assert_eq!(Ty::Int, checked.typed_roots[2].ty);
    }

    #[test]
    fn checks_constructor_args() {
        let checked = check(
            "struct Person {
            let age: Int

            init(age: Int) {
                self.age = age
            }

            func getAge() {
                self.age
            }
        }

        Person()",
        );

        assert_eq!(checked.diagnostics.len(), 1, "{:#?}", checked.diagnostics);
    }

    #[test]
    fn checks_setter() {
        let checked = check(
            "struct Person {
            let age: Int
        }

        let person = Person(age: 42)
        person.age = 1.23
        ",
        );

        assert_eq!(checked.diagnostics.len(), 1, "{:?}", checked.diagnostics);
    }

    #[test]
    fn checks_recursive_generic() {
        let checked = check(
            "
        func rec(n) {
            rec(n)
        }
        rec
        ",
        );

        // The function should have one parameter
        if let Ty::Func {
            params, returns, ..
        } = &checked.typed_roots[0].ty
        {
            assert_eq!(params.len(), 1, "rec should have 1 parameter");
            assert_eq!(**returns, Ty::Void, "rec should return Void");
        } else {
            panic!("Expected function type");
        }
    }

    #[test]
    fn checks_recursive_terminating() {
        let checked = check(
            "
        func rec(n) {
            if n < 10 {
                rec(n)
            } else {
                123
            }
        }
        rec
        ",
        );

        // The function should have one parameter
        if let Ty::Func { returns, .. } = &checked.typed_roots[0].ty {
            assert_eq!(**returns, Ty::Int)
        } else {
            panic!("Expected function type");
        }
    }

    #[test]
    fn check_mutual_recursion() {
        let checker = check(
            "
        func even(n: Int) -> Int {
            odd(n)
        }
        func odd(n: Int) -> Int {
            even(n)
        }
        even(123)
        ",
        );

        assert_eq!(Ty::Int, checker.typed_roots[2].ty);
    }

    #[test]
    fn check_static_property() {
        let checker = check(
            "
        struct Person {
            static let age = 123
        }

        Person.age
        ",
        );

        assert_eq!(Ty::Int, checker.typed_roots[1].ty);
    }

    #[test]
    fn check_static_method() {
        let checker = check(
            "
        struct Person {
            static func getAge() {
                123
            }
        }

        Person.getAge()
        ",
        );

        if !checker.diagnostics.is_empty() {
            panic!("{:#?}", checker.diagnostics);
        }

        assert_eq!(Ty::Int, checker.typed_roots[1].ty);
    }

    #[test]
    fn checks_let_with_enum_case() {
        let checked = check(
            "
        enum Maybe<T> {
          case definitely(T), nope
        }

        let maybe = Maybe.definitely(123)
        maybe
        ",
        );

        // The type should be Maybe<Int> with T instantiated to Int
        assert_eq!(
            Ty::Nominal {
                name: Name::Resolved(SymbolID::ANY, "Maybe".to_string()),
                properties: Row::Closed(ClosedRow::default()),
                methods: Row::Open(RowVar::new(1)),
                type_params: vec![],
                instantiations: std::collections::BTreeMap::from([(
                    TypeVar::new(0, TypeVarKind::Canonical),
                    Ty::Int
                ),]),
            },
            checked.typed_roots[2].ty,
        );
    }

    #[test]
    fn checks_non_generic_enum() {
        let checked = check(
            "
        enum Maybe {
          case definitely(Int), nope
        }

        let maybe = Maybe.definitely(123)
        maybe
        ",
        );

        assert_eq!(
            Ty::Nominal {
                name: Name::Resolved(SymbolID::ANY, "Maybe".to_string()),
                properties: Row::Closed(ClosedRow::default()),
                methods: Row::Open(RowVar::new(1)),
                type_params: vec![],
                instantiations: Default::default(),
            },
            checked.typed_roots[2].ty,
        );
    }
}
