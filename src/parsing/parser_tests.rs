#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use crate::any_expr;
    use crate::parsed_expr::ParsedExpr;
    use crate::parser::ExprID;
    use crate::{
        Parsed, SourceFile, name::Name, parser::parse_with_comments, token_kind::TokenKind,
    };

    use crate::parsed_expr::Expr::{self, *};

    fn parse(input: &str) -> SourceFile<Parsed> {
        crate::parser::parse(input, PathBuf::from("-"))
    }

    #[test]
    fn parses_literal_expr() {
        let parsed = parse("123");
        assert_eq!(parsed.roots()[0].expr, LiteralInt("123".into()));
    }

    #[test]
    fn parses_string_literal() {
        let parsed = parse("\"hello world\"");
        assert_eq!(parsed.roots()[0].expr, LiteralString("hello world".into()));
    }

    #[test]
    fn handles_semicolons() {
        let parsed = parse("123 ; 456");

        assert_eq!(parsed.roots()[0].expr, LiteralInt("123".into()));
        assert_eq!(parsed.roots()[1].expr, LiteralInt("456".into()));
    }

    #[test]
    fn handles_semicolon_in_body() {
        let parsed = parse("struct Person { ; }");

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: Box::new(any_expr!(Block(vec![]))),
            })
        );
    }

    #[test]
    fn handles_semicolons_infix() {
        let parsed = parse("func() { };()");

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Func {
                name: None,
                generics: vec![],
                params: vec![],
                body: any_expr!(Block(vec![])).into(),
                ret: None,
                captures: vec![]
            })
        );
        assert_eq!(parsed.roots()[1].expr, Tuple(vec![]));
    }

    #[test]
    fn ignores_comments() {
        let parsed = parse_with_comments("// what's up\n123");
        let expr = parsed.roots()[0].expr;

        assert_eq!(expr, LiteralInt("123".into()));
    }

    #[test]
    fn parses_eq() {
        let parsed = parse("1 == 2");
        let expr = parsed.roots()[0];

        assert_eq!(
            expr,
            any_expr!(Expr::Binary(
                any_expr!(Expr::LiteralInt("1".into())).into(),
                TokenKind::EqualsEquals,
                any_expr!(Expr::LiteralInt("2".into())).into()
            ))
        );
    }

    #[test]
    fn stores_expr_meta() {
        let parsed = parse("1 + 2");
        let meta = &parsed.meta.get(&parsed.roots()[0].id).unwrap();

        assert_eq!(meta.start.start, 0);
        assert_eq!(meta.start.end, 1);
        assert_eq!(meta.end.start, 4);
        assert_eq!(meta.end.end, 5);
        assert_eq!(meta.source_range(), 0..5);
    }

    #[test]
    fn parses_not_eq() {
        let parsed = parse("1 != 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::BangEquals,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_greater() {
        let parsed = parse("1 > 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Greater,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_greater_eq() {
        let parsed = parse("1 >= 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::GreaterEquals,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_less() {
        let parsed = parse("1 < 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Less,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_less_eq() {
        let parsed = parse("1 <= 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::LessEquals,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_plus_expr() {
        let parsed = parse("1 + 2");
        let expr = parsed.roots()[0].expr;

        assert_eq!(expr, Expr::Binary(0, TokenKind::Plus, 1,));
    }

    #[test]
    fn parses_minus_expr() {
        let parsed = parse("1 - 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Minus,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_div_expr() {
        let parsed = parse("1 / 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Slash,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_mult_expr() {
        let parsed = parse("1 * 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Star,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_less_expr() {
        let parsed = parse("1 < 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Less,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_less_equals_expr() {
        let parsed = parse("1 <= 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::LessEquals,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_greater_expr() {
        let parsed = parse("1 > 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Greater,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_caret_expr() {
        let parsed = parse("1 ^ 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Caret,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_pipe_expr() {
        let parsed = parse("1 | 2");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Pipe,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
    }

    #[test]
    fn parses_correct_precedence() {
        let parsed = parse("1 + 2 * 2");
        let expr = parsed.roots()[0].expr;

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Plus,
                any_expr!(Binary(
                    any_expr!(LiteralInt("2".into())).into(),
                    TokenKind::Star,
                    any_expr!(LiteralInt("2".into())).into()
                ))
                .into()
            ))
        );
    }

    #[test]
    fn parses_group() {
        let parsed = parse("(1 + 2)");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Tuple(vec![any_expr!(Expr::Binary(
                any_expr!(Expr::LiteralInt("1".into())).into(),
                TokenKind::EqualsEquals,
                any_expr!(Expr::LiteralInt("2".into())).into()
            ))]))
        );
    }

    #[test]
    fn parses_var() {
        let parsed = parse("hello\nworld");
        let hello = parsed.roots()[0].expr;
        let world = parsed.roots()[1].expr;

        assert_eq!(hello, Expr::Variable(Name::Raw("hello".to_string())));
        assert_eq!(world, Expr::Variable(Name::Raw("world".to_string())));
    }

    #[test]
    fn parses_unary_bang() {
        let parsed = parse("!hello");
        let expr = parsed.roots()[0].expr;

        assert_eq!(expr, Expr::Unary(TokenKind::Bang, 0));
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::Variable(Name::Raw("hello".to_string()), None)
        );
    }

    #[test]
    fn parses_unary_minus() {
        let parsed = parse("-1");
        let expr = parsed.roots()[0].expr;
        assert_eq(expr, Unary(TokenKind::Minus, LiteralInt("1".into()).into()));
    }

    #[test]
    fn parses_tuple() {
        let parsed = parse(
            "
        (1, 2, fizz)",
        );
        let expr = parsed.roots()[0].expr;

        assert_eq!(expr, Expr::Tuple(vec![0, 1, 2]));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("1".into()));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("2".into()));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::Variable(Name::Raw("fizz".to_string()), None)
        );
    }

    #[test]
    fn parses_empty_tuple() {
        let parsed = parse("( )");
        let expr = parsed.roots()[0].expr;

        assert_eq!(expr, Expr::Tuple(vec![]));
    }

    #[test]
    fn parses_return() {
        let _parsed = parse("func() { return }");
    }

    #[test]
    fn parses_func_literal_no_name_no_args() {
        let parsed = parse("func() { }");
        let expr = parsed.roots()[0].expr;

        assert_eq!(
            *expr,
            Expr::Func {
                name: None,
                generics: vec![],
                params: vec![],
                body: 0,
                ret: None,
                captures: vec![],
            }
        );
        assert_eq!(*parsed.get(&0).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_literal_with_newlines() {
        let parsed = parse(
            "func greet(a) {
                a
            }",
        );

        let expr = parsed.roots()[0].expr;

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![0],
                body: 2,
                ret: None,
                captures: vec![],
            }
        );
    }

    #[test]
    fn parses_func_literal_name_no_args() {
        let parsed = parse("func greet() { }");
        let expr = parsed.roots()[0].expr;

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![],
                body: 0,
                ret: None,
                captures: vec![],
            }
        );
        assert_eq!(*parsed.get(&0).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_with_generics() {
        let parsed = parse(
            "
        func greet<T>(t) -> T { t }
        ",
        );
        let expr = parsed.roots()[0].expr;

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![0],
                params: vec![1],
                body: 4,
                ret: Some(2),
                captures: vec![],
            }
        );

        assert_eq!(*parsed.get(&1).unwrap(), Expr::Parameter("t".into(), None));
        assert_eq!(*parsed.get(&4).unwrap(), Expr::Block(vec![3]));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::TypeRepr {
                name: "T".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn parses_func_call_with_generics() {
        let parsed = parse("foo<T>()");
        assert_eq!(
            parsed.roots()[0].expr,
            Expr::Call {
                callee: 0,
                type_args: vec![1],
                args: vec![]
            }
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr {
                name: "T".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn parses_multiple_roots() {
        let parsed = parse("func hello() {}\nfunc world() {}");
        assert_eq!(2, parsed.roots().len());
        assert_eq!(
            parsed.roots()[0].expr,
            Expr::Func {
                name: Some(Name::Raw("hello".to_string())),
                generics: vec![],
                params: vec![],
                body: 0,
                ret: None,
                captures: vec![],
            }
        );

        assert_eq!(*parsed.get(&0).unwrap(), Expr::Block(vec![]));
        assert_eq!(
            parsed.roots()[1].expr,
            Expr::Func {
                name: Some(Name::Raw("world".to_string())),
                generics: vec![],
                params: vec![],
                body: 2,
                ret: None,
                captures: vec![],
            }
        );
        assert_eq!(*parsed.get(&2).unwrap(), Expr::Block(vec![]));
    }

    #[test]
    fn parses_func_literal_name_with_args() {
        let parsed = parse("func greet(one, two) { }");
        let expr = parsed.roots()[0].expr;

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![0, 1],
                body: 2,
                ret: None,
                captures: vec![],
            }
        );
    }

    #[test]
    fn parses_param_type() {
        let parsed = parse("func greet(name: Int) {}");
        let expr = parsed.roots()[0].expr;
        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![1],
                body: 2,
                ret: None,
                captures: vec![],
            }
        );

        assert_eq!(
            *parsed.get(&1).unwrap(),
            Parameter(Name::Raw("name".to_string()), Some(0))
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr {
                name: "Int".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn parses_call_no_args() {
        let parsed = parse("fizz()");
        let expr = parsed.roots()[0].expr;

        let Expr::Call {
            callee: callee_id,
            args: args_ids,
            ..
        } = expr
        else {
            panic!("no call found")
        };

        let callee = parsed.get(callee_id).unwrap();
        let args_id: Vec<_> = args_ids.iter().map(|id| parsed.get(id).unwrap()).collect();
        assert_eq!(*callee, Expr::Variable(Name::Raw("fizz".to_string()), None));
        assert_eq!(args_id.len(), 0);
    }

    #[test]
    fn parses_call_with_args() {
        let parsed = parse("fizz(foo: 123)");

        let expr = parsed.roots()[0].expr;

        let Expr::Call {
            callee: callee_id,
            args: args_ids,
            ..
        } = expr
        else {
            panic!("no call found")
        };

        let callee = parsed.get(callee_id).unwrap();
        let args_id: Vec<_> = args_ids.iter().map(|id| parsed.get(id).unwrap()).collect();
        assert_eq!(*callee, Expr::Variable(Name::Raw("fizz".to_string()), None));
        assert_eq!(args_id.len(), 1);
        assert_eq!(
            *args_id[0],
            Expr::CallArg {
                label: Some("foo".into()),
                value: 1
            }
        );

        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("123".into()));
    }

    #[test]
    fn parses_let() {
        let parsed = parse("let fizz");
        let expr = parsed.roots()[0].expr;
        assert_eq!(expr, Expr::Let(Name::Raw("fizz".to_string()), None));
    }

    #[test]
    fn parses_let_with_type() {
        let parsed = parse("let fizz: Int");
        let expr = parsed.roots()[0].expr;
        assert_eq!(expr, Expr::Let(Name::Raw("fizz".to_string()), Some(0)));
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr {
                name: "Int".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn parses_let_with_tuple_type() {
        let parsed = parse("let fizz: (Int, Bool)");
        let expr = parsed.roots()[0].expr;
        assert_eq!(expr, Expr::Let(Name::Raw("fizz".to_string()), Some(2)));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::TupleTypeRepr(vec![0, 1], false)
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr {
                name: "Int".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr {
                name: "Bool".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn parses_return_type_annotation() {
        let parsed = parse("func fizz() -> Int { 123 }");
        let expr = parsed.roots()[0].expr;

        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("fizz".to_string())),
                generics: vec![],
                params: vec![],
                body: 2,
                ret: Some(0),
                captures: vec![],
            }
        );
    }

    #[test]
    fn parses_bools() {
        let parsed = parse("true\nfalse");
        assert_eq!(parsed.roots()[0].expr, Expr::LiteralTrue);
        assert_eq!(parsed.roots()[1].expr, Expr::LiteralFalse);
    }

    #[test]
    fn parses_if() {
        let parsed = parse("if true { 123 }");
        assert_eq!(parsed.roots()[0].expr, Expr::If(0, 2, None));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.get(&2).unwrap(), Expr::Block(vec![1]));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("123".into()));
    }

    #[test]
    fn parses_if_else() {
        let parsed = parse("if true { 123 } else { 456 }");
        assert_eq!(parsed.roots()[0].expr, Expr::If(0, 2, Some(4)));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.get(&2).unwrap(), Expr::Block(vec![1]));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("123".into()));
        assert_eq!(*parsed.get(&4).unwrap(), Expr::Block(vec![3]));
        assert_eq!(*parsed.get(&3).unwrap(), Expr::LiteralInt("456".into()));
    }

    #[test]
    fn parses_loop() {
        let parsed = parse("loop { 123 }");
        assert_eq!(parsed.roots()[0].expr, Expr::Loop(None, 1));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::Block(vec![0]));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("123".into()));
    }

    #[test]
    fn parses_break() {
        let parsed = parse("loop { break }");
        assert_eq!(parsed.roots()[0].expr, Expr::Loop(None, 1));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::Block(vec![0]));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::Break);
    }

    #[test]
    fn parses_loop_with_condition() {
        let parsed = parse("loop true { 123 }");
        assert_eq!(parsed.roots()[0].expr, Expr::Loop(Some(0), 2));
        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralTrue);
        assert_eq!(*parsed.get(&2).unwrap(), Expr::Block(vec![1]));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("123".into()));
    }

    #[test]
    fn parses_loop_with_binary_condition() {
        let parsed = parse("loop i < self.count { 123 }");
        assert_eq!(parsed.roots()[0].expr, Expr::Loop(Some(3), 5));
        assert_eq!(
            *parsed.get(&3).unwrap(),
            Expr::Binary(0, TokenKind::Less, 2)
        );
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::Member(Some(1), "count".into())
        );
        assert_eq!(*parsed.get(&1).unwrap(), Variable("self".into(), None));
    }

    #[test]
    fn parses_empty_enum_decl() {
        let parsed = parse("enum Fizz {}");

        assert_eq!(
            parsed.roots()[0].expr,
            Expr::EnumDecl {
                name: "Fizz".into(),
                generics: vec![],
                conformances: vec![],
                body: 0
            }
        );
    }

    #[test]
    fn parses_empty_enum_instantiation() {
        let parsed = parse("enum Fizz { case foo }\nFizz.foo");

        assert_eq!(parsed.roots()[1].expr, Member(Some(3), "foo".into()));
    }

    #[test]
    fn parses_empty_enum_instantiation_with_value() {
        let parsed = parse("enum Fizz { case foo(Int) }\nFizz.foo(123)");

        assert_eq!(
            parsed.roots()[1].expr,
            Call {
                callee: 5,
                type_args: vec![],
                args: vec![7]
            }
        );
        assert_eq!(*parsed.get(&5).unwrap(), Member(Some(4), "foo".into()));
        assert_eq!(*parsed.get(&4).unwrap(), Variable("Fizz".into(), None));
    }

    #[test]
    fn parses_enum_with_generics() {
        let parsed = parse(
            "enum Fizz<T, Y> {
                case foo(T, Y), bar
            }
            
            enum Buzz<T, Y> {
                case foo(T, Y), bar
            }",
        );
        let expr = parsed.roots()[0].expr;

        assert_eq!(
            *expr,
            Expr::EnumDecl {
                name: "Fizz".into(),
                generics: vec![0, 1],
                conformances: vec![],
                body: 6
            }
        );

        // Check the enum generics
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr {
                name: "T".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: true
            }
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr {
                name: "Y".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: true
            }
        );

        // Check the body
        assert_eq!(*parsed.get(&6).unwrap(), Expr::Block(vec![4, 5]));
        assert_eq!(
            *parsed.get(&4).unwrap(),
            Expr::EnumVariant(Name::Raw("foo".into()), vec![2, 3])
        );
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::TypeRepr {
                name: "T".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
        assert_eq!(
            *parsed.get(&3).unwrap(),
            Expr::TypeRepr {
                name: "Y".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn parses_enum_cases() {
        let parsed = parse(
            "enum Fizz {
                case foo, bar
                case fizz
            }",
        );
        assert_eq!(
            parsed.roots()[0].expr,
            Expr::EnumDecl {
                name: "Fizz".into(),
                generics: vec![],
                conformances: vec![],
                body: 3
            }
        );

        let Expr::Block(exprs) = parsed.get(&3).unwrap() else {
            panic!("didn't get body")
        };

        assert_eq!(exprs.len(), 3);
        assert_eq!(
            *parsed.get(&exprs[0]).unwrap(),
            Expr::EnumVariant(Name::Raw("foo".to_string()), vec![])
        );
        assert_eq!(
            *parsed.get(&exprs[1]).unwrap(),
            Expr::EnumVariant(Name::Raw("bar".to_string()), vec![])
        );
        assert_eq!(
            *parsed.get(&exprs[2]).unwrap(),
            Expr::EnumVariant(Name::Raw("fizz".to_string()), vec![])
        );
    }

    #[test]
    fn parses_enum_cases_with_associated_values() {
        let parsed = parse(
            "enum Fizz {
                case foo(Int, Float), bar(Float, Int)
            }",
        );
        assert_eq!(
            parsed.roots()[0].expr,
            Expr::EnumDecl {
                name: "Fizz".into(),
                generics: vec![],
                conformances: vec![],
                body: 6
            }
        );

        let Expr::Block(exprs) = parsed.get(&6).unwrap() else {
            panic!("didn't get body")
        };

        assert_eq!(exprs.len(), 2);
        assert_eq!(
            *parsed.get(&exprs[0]).unwrap(),
            Expr::EnumVariant("foo".into(), vec![0, 1])
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr {
                name: "Int".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr {
                name: "Float".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );

        assert_eq!(
            *parsed.get(&exprs[1]).unwrap(),
            Expr::EnumVariant(Name::Raw("bar".into()), vec![3, 4])
        );
        assert_eq!(
            *parsed.get(&3).unwrap(),
            Expr::TypeRepr {
                name: "Float".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
        assert_eq!(
            *parsed.get(&4).unwrap(),
            Expr::TypeRepr {
                name: "Int".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn parses_match() {
        let parsed = parse(
            "match fizz {
                .foo(name) -> name
                .bar -> fizz
            }",
        );

        assert_eq!(parsed.roots()[0].expr, Expr::Match(0, vec![4, 7]));
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Variable(Name::Raw("fizz".to_string()), None)
        );

        assert_eq!(*parsed.get(&4).unwrap(), MatchArm(2, 3));
        assert_eq!(*parsed.get(&7).unwrap(), MatchArm(5, 6));
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Pattern(crate::expr::Pattern::Variant {
                enum_name: None,
                variant_name: "foo".into(),
                fields: vec![1]
            })
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Pattern(crate::expr::Pattern::Bind(Name::Raw("name".into())))
        );
        assert_eq!(
            *parsed.get(&5).unwrap(),
            Pattern(crate::expr::Pattern::Variant {
                enum_name: None,
                variant_name: "bar".into(),
                fields: vec![]
            })
        );
    }

    #[test]
    fn parses_fn_type_repr() {
        let parsed = parse(
            "
        func greet(using: (T) -> Y) {}
        ",
        );
        let expr = parsed.roots()[0].expr;
        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![3],
                body: 4,
                ret: None,
                captures: vec![],
            }
        );

        assert_eq!(
            *parsed.get(&3).unwrap(),
            Expr::Parameter("using".into(), Some(2))
        );

        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::FuncTypeRepr(vec![0], 1, false)
        );

        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr {
                name: "T".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );

        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr {
                name: "Y".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn converts_question_to_optional_for_type_repr() {
        let parsed = parse("func greet(name: Int?) {}");
        let expr = parsed.roots()[0].expr;
        assert_eq!(
            *expr,
            Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![2],
                body: 3,
                ret: None,
                captures: vec![],
            }
        );

        assert_eq!(
            *parsed.get(&2).unwrap(),
            Parameter(Name::Raw("name".to_string()), Some(1))
        );
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::TypeRepr {
                name: "Optional".into(),
                generics: vec![0],
                conformances: vec![],
                introduces_type: false
            }
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr {
                name: "Int".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn parses_enum_methods() {
        let parsed = parse(
            "
            enum MyEnum {
                case val(Int), nope

                func fizz() {
                    123
                }
            }
        ",
        );

        assert_eq!(
            parsed.roots()[0].expr,
            Expr::EnumDecl {
                name: "MyEnum".into(),
                generics: vec![],
                conformances: vec![],
                body: 6
            }
        );

        let Expr::Block(exprs) = parsed.get(&6).unwrap() else {
            panic!("didn't get block: {:?}", parsed.get(&3));
        };

        assert_eq!(3, exprs.len());
        assert_eq!(
            *parsed.get(&exprs[2]).unwrap(),
            Expr::Func {
                name: Some(Name::Raw("fizz".into())),
                generics: vec![],
                params: vec![],
                body: 4,
                ret: None,
                captures: vec![],
            }
        )
    }

    #[test]
    fn parses_variable_assignment() {
        let parsed = parse(
            "
            foo = 123
            ",
        );

        assert_eq!(parsed.roots()[0].expr, Expr::Assignment(0, 1));
    }
}

#[cfg(test)]
mod pattern_parsing_tests {
    use crate::compiling::compilation_session::SharedCompilationSession;
    use crate::{environment::Environment, expr::Pattern, lexer::Lexer, name::Name};

    use crate::parser::Parser;

    fn parse_pattern(input: &'static str) -> Pattern {
        let lexer = Lexer::new(input);
        let session = SharedCompilationSession::default();
        let mut env = Environment::default();
        let mut parser = Parser::new(session, lexer, "-".into(), &mut env);
        parser.advance();
        parser.advance();
        parser.parse_match_pattern().unwrap()
    }

    #[test]
    fn parses_wildcard() {
        assert_eq!(parse_pattern("_ "), Pattern::Wildcard);
    }

    #[test]
    fn parses_literal_int() {
        assert_eq!(parse_pattern("123"), Pattern::LiteralInt("123".into()));
    }

    #[test]
    fn parses_literal_float() {
        assert_eq!(
            parse_pattern("123.0"),
            Pattern::LiteralFloat("123.0".into())
        );
    }

    #[test]
    fn parses_literal_bools() {
        assert_eq!(parse_pattern("true"), Pattern::LiteralTrue);
        assert_eq!(parse_pattern("false"), Pattern::LiteralFalse);
    }

    #[test]
    fn parses_variant_pattern() {
        assert_eq!(
            parse_pattern("Fizz.buzz"),
            Pattern::Variant {
                enum_name: Some(Name::Raw("Fizz".into())),
                variant_name: "buzz".into(),
                fields: vec![]
            }
        );

        assert_eq!(
            parse_pattern(".foo"),
            Pattern::Variant {
                enum_name: None,
                variant_name: "foo".into(),
                fields: vec![]
            }
        );
    }
}

#[cfg(test)]
mod arrays {
    use crate::{
        expr::Expr,
        filler::FullExpr,
        name::Name,
        parser::{parse, parse_fill},
    };

    #[test]
    fn parses_array_literal() {
        let parsed = parse("[1, 2, 3]", "-".into());
        assert_eq!(parsed.roots()[0].expr, Expr::LiteralArray(vec!(0, 1, 2)));

        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("1".into()));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("2".into()));
        assert_eq!(*parsed.get(&2).unwrap(), Expr::LiteralInt("3".into()));
    }

    #[test]
    fn parses_array_literal_with_newlines() {
        let parsed = parse(
            "[
          1
          ,
        2, 3
        ]",
            "-".into(),
        );
        assert_eq!(parsed.roots()[0].expr, Expr::LiteralArray(vec!(0, 1, 2)));
    }

    #[test]
    fn parses_extensions() {
        let parsed = parse_fill(
            "
        extend Person: Something<String> {
            func foo() {}
        }
        ",
        );

        use FullExpr::*;
        assert_eq!(
            parsed[0],
            Extend {
                name: Name::Raw("Person".into()),
                generics: vec![],
                conformances: vec![TypeRepr {
                    name: Name::Raw("Something".into()),
                    generics: vec![TypeRepr {
                        name: Name::Raw("String".into()),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    }],
                    conformances: vec![],
                    introduces_type: false
                }],
                body: Block(vec![Func {
                    name: Some("foo".into()),
                    generics: vec![],
                    params: vec![],
                    body: Block(vec![]).into(),
                    ret: None.into(),
                    captures: vec![]
                }])
                .into()
            }
        )
    }
}

#[cfg(test)]
mod structs {
    use crate::{
        diagnostic::Diagnostic,
        expr::Expr,
        filler::{Filler, FullExpr},
        name::Name,
        parser::{parse, parse_with_session},
        token::Token,
        token_kind::TokenKind,
    };
    use std::path::PathBuf;

    #[test]
    fn parses_empty_struct_def() {
        let parsed = parse(
            "
        struct Person {}
        ",
            "-".into(),
        );

        assert_eq!(
            parsed.roots()[0].expr,
            Expr::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: 0
            }
        );
    }

    #[test]
    fn parses_struct_properties() {
        let parsed = parse(
            "
        struct Person {
            let age: Int
            let count: Int = 123
            let height = 456
        }
        ",
            "-".into(),
        );

        assert_eq!(
            parsed.roots()[0].expr,
            Expr::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: 7
            }
        );
        assert_eq!(*parsed.get(&7).unwrap(), Expr::Block(vec![1, 4, 6]));
        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::Property {
                name: "age".into(),
                type_repr: Some(0),
                default_value: None
            }
        );
        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr {
                name: "Int".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );

        assert_eq!(
            *parsed.get(&4).unwrap(),
            Expr::Property {
                name: "count".into(),
                type_repr: Some(2),
                default_value: Some(3)
            }
        );
        assert_eq!(
            *parsed.get(&2).unwrap(),
            Expr::TypeRepr {
                name: "Int".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
        assert_eq!(*parsed.get(&3).unwrap(), Expr::LiteralInt("123".into()));

        assert_eq!(
            *parsed.get(&6).unwrap(),
            Expr::Property {
                name: "height".into(),
                type_repr: None,
                default_value: Some(5)
            }
        );
        assert_eq!(*parsed.get(&5).unwrap(), Expr::LiteralInt("456".into()));
    }

    #[test]
    fn parses_init() {
        let parsed = parse(
            "
        struct Person {
            let age: Int
            
            init(age: Int) {
                self.age = age
            }
        }
        ",
            "-".into(),
        );

        assert_eq!(
            parsed.roots()[0].expr,
            Expr::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: 11
            }
        );

        let Some(Expr::Block(items)) = parsed.get(&11) else {
            unreachable!()
        };

        let Some(Expr::Init(None, func_id)) = parsed.get(&items[1]) else {
            unreachable!()
        };

        let Some(Expr::Func {
            name,
            generics,
            params,
            body,
            ret,
            captures,
        }) = parsed.get(func_id)
        else {
            unreachable!()
        };

        assert_eq!(&Some(Name::Raw("init".into())), name);
        assert!(generics.is_empty());
        assert_eq!(&vec![3], params);
        assert_eq!(&None, ret);
        assert_eq!(&8, body);
        assert!(captures.is_empty());
    }

    #[test]
    fn handles_unclosed_paren() {
        let (_, session) = parse_with_session("(", "-".into());
        let session = session.lock().unwrap();
        let diagnostics = session.diagnostics_for(&PathBuf::from("-"));
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics.contains(&Diagnostic::parser(
            PathBuf::from("-"),
            Token {
                kind: TokenKind::LeftParen,
                col: 1,
                line: 0,
                start: 0,
                end: 1,
            },
            crate::parser::ParserError::UnexpectedEndOfInput(None)
        )))
    }

    #[test]
    fn handles_unclosed_brace() {
        let (_, session) = parse_with_session("func foo() {", "-".into());
        let session = session.lock().unwrap();
        let diagnostics = session.diagnostics_for(&PathBuf::from("-"));
        assert_eq!(diagnostics.len(), 1);
        assert!(
            diagnostics.contains(&Diagnostic::parser(
                PathBuf::from("-"),
                Token {
                    kind: TokenKind::EOF,
                    col: 12,
                    line: 0,
                    start: 12,
                    end: 12,
                },
                crate::parser::ParserError::UnexpectedEndOfInput(None)
            )),
            "{:?}",
            session._diagnostics()
        )
    }

    #[test]
    fn recovers() {
        let (parsed, session) = parse_with_session("func foo() {\n\nfunc fizz() {}", "-".into());
        let session = session.lock().unwrap();
        let diagnostics = session.diagnostics_for(&PathBuf::from("-"));
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert!(diagnostics.contains(&Diagnostic::parser(
            PathBuf::from("-"),
            Token {
                kind: TokenKind::EOF,
                col: 14,
                line: 2,
                start: 28,
                end: 28,
            },
            crate::parser::ParserError::UnexpectedEndOfInput(None)
        )));

        assert_eq!(
            *parsed.get(&1).unwrap(),
            Expr::Func {
                name: Some("fizz".into()),
                body: 0,
                ret: None,
                params: vec![],
                generics: vec![],
                captures: vec![]
            }
        )
    }

    #[test]
    fn parses_protocol() {
        let parsed = parse(
            "
        protocol Aged<T>: X {
          let age: Int
          func getAge() -> Int
        }
        ",
            "-".into(),
        );

        let Expr::ProtocolDecl {
            name,
            associated_types,
            body,
            conformances,
        } = parsed.get(&parsed.root_ids()[0]).unwrap()
        else {
            panic!("didn't get protocol");
        };

        assert_eq!(*name, Name::Raw("Aged".into()));

        let Expr::TypeRepr {
            name: t_name,
            introduces_type: true,
            ..
        } = parsed.get(&associated_types[0]).unwrap()
        else {
            panic!(
                "Didn't get type repr: {:?}",
                parsed.get(&associated_types[0]).unwrap()
            );
        };
        assert_eq!(*t_name, Name::Raw("T".into()));

        let Expr::TypeRepr {
            name: Name::Raw(x_name),
            ..
        } = parsed.get(&conformances[0]).unwrap()
        else {
            panic!(
                "didn't get conformance: {:?}",
                parsed.get(&conformances[0]).unwrap()
            );
        };
        assert_eq!(x_name, "X");

        let Expr::Block(ids) = parsed.get(body).unwrap() else {
            panic!("didn't get body")
        };

        // Not doing any further asserting on the property because it's the same
        // handling as the other stuff
        let Expr::Property { .. } = parsed.get(&ids[0]).unwrap() else {
            panic!("did not get property");
        };

        let Expr::FuncSignature {
            name,
            params,
            generics,
            ret,
        } = parsed.get(&ids[1]).unwrap()
        else {
            panic!("didn't get func requirement");
        };

        assert_eq!(*name, Name::Raw("getAge".into()));
        assert!(params.is_empty());
        assert!(generics.is_empty());
        assert_eq!(
            *parsed.get(ret).unwrap(),
            Expr::TypeRepr {
                name: Name::Raw("Int".into()),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            },
        );
    }

    #[test]
    fn parses_protocol_conformance() {
        let parsed = parse(
            "
        struct Person: Aged {}
    ",
            "-".into(),
        );

        let Some(Expr::Struct {
            name: Name::Raw(name),
            ..
        }) = parsed.get(&parsed.root_ids()[0])
        else {
            panic!("didn't get struct");
        };

        assert_eq!(name, "Person");
    }

    #[test]
    fn parses_type_repr_conformance() {
        let parsed = parse(
            "
        func foo<T: Fizz>(x) -> T { x }
    ",
            "-".into(),
        );

        let filler = Filler::new(parsed);
        let filled = filler.fill_root();

        use FullExpr::*;
        assert_eq!(
            filled[0],
            Func {
                name: Some(Name::Raw("foo".into())),
                generics: vec![TypeRepr {
                    name: Name::Raw("T".into()),
                    conformances: vec![TypeRepr {
                        name: Name::Raw("Fizz".into()),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    }],
                    generics: vec![],
                    introduces_type: true
                }],
                params: vec![Parameter(Name::Raw("x".into()), None.into())],
                body: Block(vec![Variable(Name::Raw("x".into()), None.into())]).into(),
                ret: Some(TypeRepr {
                    name: Name::Raw("T".into()),
                    conformances: vec![],
                    generics: vec![],
                    introduces_type: false
                })
                .into(),
                captures: vec![]
            }
        );
    }
}

#[cfg(test)]
mod incompleteness_tests {
    use crate::{
        filler::{FilledIncomplete, FullExpr},
        name::Name,
        parser::parse_fill,
    };

    #[test]
    fn parses_incomplete_member_expr() {
        let parsed = parse_fill(
            "
        foo.
        ",
        );

        use FullExpr::*;
        assert_eq!(
            parsed[0],
            Incomplete(FilledIncomplete::Member(Some(
                Variable(Name::Raw("foo".into()), None.into()).into()
            )))
        )
    }

    #[test]
    fn parses_incomplete_func_expr() {
        use FullExpr::*;
        assert_eq!(
            parse_fill(
                "
            func
            ",
            )[0],
            Incomplete(FilledIncomplete::Func {
                name: None,
                params: None,
                generics: None,
                ret: None,
                body: None
            })
        )
    }

    #[test]
    fn parses_incomplete_func_expr_with_name() {
        use FullExpr::*;
        assert_eq!(
            parse_fill(
                "
            func foo
            ",
            )[0],
            Incomplete(FilledIncomplete::Func {
                name: Some(Name::Raw("foo".into())),
                params: None,
                generics: None,
                ret: None,
                body: None
            })
        )
    }

    #[test]
    fn parses_incomplete_func_expr_with_name_and_open_paren() {
        use FullExpr::*;
        assert_eq!(
            parse_fill(
                "
            func foo(
            ",
            )[0],
            Incomplete(FilledIncomplete::Func {
                name: Some(Name::Raw("foo".into())),
                params: Some(vec![]),
                generics: None,
                ret: None,
                body: None
            })
        )
    }

    #[test]
    fn parses_incomplete_func_expr_with_name_and_open_paren_and_param() {
        use FullExpr::*;
        assert_eq!(
            parse_fill(
                "
            func foo(fizz
            ",
            )[0],
            Incomplete(FilledIncomplete::Func {
                name: Some(Name::Raw("foo".into())),
                params: Some(vec![Parameter(Name::Raw("fizz".into()), None.into())]),
                generics: None,
                ret: None,
                body: None
            })
        )
    }

    #[test]
    fn parses_incomplete_func_expr_without_body() {
        use FullExpr::*;
        assert_eq!(
            parse_fill(
                "
            func foo(fizz) 
            ",
            )[0],
            Incomplete(FilledIncomplete::Func {
                name: Some(Name::Raw("foo".into())),
                params: Some(vec![Parameter(Name::Raw("fizz".into()), None.into())]),
                generics: Some(vec![]),
                ret: None,
                body: None
            })
        )
    }

    #[test]
    fn parses_incomplete_func_expr_with_incomplete_body() {
        use FullExpr::*;
        assert_eq!(
            parse_fill(
                "
            func foo(fizz) {
            ",
            )[0],
            Incomplete(FilledIncomplete::Func {
                name: Some(Name::Raw("foo".into())),
                params: Some(vec![Parameter(Name::Raw("fizz".into()), None.into())]),
                generics: Some(vec![]),
                ret: None,
                body: None
            })
        )
    }
}
