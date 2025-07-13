#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use crate::any_expr;
    use crate::compiling::compilation_session::SharedCompilationSession;
    use crate::diagnostic::Diagnostic;
    use crate::environment::Environment;
    use crate::lexer::Lexer;
    use crate::parsed_expr::{IncompleteExpr, ParsedExpr, Pattern};
    use crate::parser::{ExprID, Parser, parse_with_session};
    use crate::token::Token;
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
        assert_eq!(parsed.roots()[1].expr, any_expr!(Expr::Tuple(vec![])));
    }

    #[test]
    fn ignores_comments() {
        let parsed = parse_with_comments("// what's up\n123");
        assert_eq!(parsed.roots()[0], any_expr!(Expr::LiteralInt("123".into())));
    }

    #[test]
    fn parses_eq() {
        let parsed = parse("1 == 2");
        assert_eq!(
            parsed.roots()[0],
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

        assert_eq!(
            expr,
            any_expr!(Expr::Binary(
                any_expr!(LiteralInt("1".into())).into(),
                TokenKind::Plus,
                any_expr!(LiteralInt("2".into())).into(),
            ))
        );
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

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Variable(Name::Raw("hello".to_string())))
        );
        assert_eq!(
            parsed.roots()[1],
            any_expr!(Expr::Variable(Name::Raw("world".to_string())))
        );
    }

    #[test]
    fn parses_unary_bang() {
        let parsed = parse("!hello");

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Unary(
                TokenKind::Bang,
                any_expr!(LiteralInt("1".into())).into()
            ))
        );
    }

    #[test]
    fn parses_unary_minus() {
        let parsed = parse("-1");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Unary(
                TokenKind::Minus,
                any_expr!(LiteralInt("1".into())).into()
            ))
        );
    }

    #[test]
    fn parses_tuple() {
        let parsed = parse(
            "
        (1, 2, fizz)",
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Tuple(vec![
                any_expr!(LiteralInt("1".into())).into(),
                any_expr!(LiteralInt("2".into())).into(),
                any_expr!(LiteralInt("fizz".into())).into(),
            ]))
        );
    }

    #[test]
    fn parses_empty_tuple() {
        let parsed = parse("( )");
        assert_eq!(parsed.roots()[0], any_expr!(Expr::Tuple(vec![])));
    }

    #[test]
    fn parses_return() {
        let _parsed = parse("func() { return }");
    }

    #[test]
    fn parses_func_literal_no_name_no_args() {
        let parsed = parse("func() { }");

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: None,
                generics: vec![],
                params: vec![],
                body: any_expr!(Block(vec![])).into(),
                ret: None,
                captures: vec![],
            })
        );
    }

    #[test]
    fn parses_func_literal_with_newlines() {
        let parsed = parse(
            "func greet(a) {
                a
            }",
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![any_expr!(Parameter("a".into(), None)).into()],
                body: any_expr!(
                    Block(vec![any_expr!(Return(Some(
                        any_expr!(Variable("a".into())).into()
                    )))])
                    .into()
                ),
                ret: None,
                captures: vec![],
            })
        );
    }

    #[test]
    fn parses_func_literal_name_no_args() {
        let parsed = parse("func greet() { }");

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![],
                body: any_expr!(Block(vec![])).into(),
                ret: None,
                captures: vec![],
            })
        );
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
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![any_expr!(TypeRepr {
                    name: "T".into(),
                    generics: vec![],
                    conformances: vec![],
                    introduces_type: false
                })],
                params: vec![any_expr!(Parameter("t".into(), None))],
                body: any_expr!(
                    Block(vec![any_expr!(Return(Some(
                        any_expr!(Variable("t".into())).into()
                    )))])
                    .into()
                ),
                ret: Some(
                    any_expr!(TypeRepr {
                        name: "T".into(),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    })
                    .into()
                ),
                captures: vec![],
            })
        );
    }

    #[test]
    fn parses_func_call_with_generics() {
        let parsed = parse("foo<T>()");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Call {
                callee: any_expr!(Variable("foo".into())).into(),
                type_args: vec![any_expr!(TypeRepr {
                    name: "T".into(),
                    generics: vec![],
                    conformances: vec![],
                    introduces_type: false
                })],
                args: vec![]
            })
        );
    }

    #[test]
    fn parses_multiple_roots() {
        let parsed = parse("func hello() {}\nfunc world() {}");
        assert_eq!(2, parsed.roots().len());
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("hello".to_string())),
                generics: vec![],
                params: vec![],
                body: any_expr!(Block(vec![])).into(),
                ret: None,
                captures: vec![],
            })
        );

        assert_eq!(
            parsed.roots()[1],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("world".to_string())),
                generics: vec![],
                params: vec![],
                body: any_expr!(Block(vec![])).into(),
                ret: None,
                captures: vec![],
            })
        );
    }

    #[test]
    fn parses_func_literal_name_with_args() {
        let parsed = parse("func greet(one, two) { }");

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![
                    any_expr!(Parameter("one".into(), None)).into(),
                    any_expr!(Parameter("two".into(), None)).into(),
                ],
                body: any_expr!(Block(vec![])).into(),
                ret: None,
                captures: vec![],
            })
        );
    }

    #[test]
    fn parses_param_type() {
        let parsed = parse("func greet(name: Int) {}");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("greet".to_string())),
                generics: vec![],
                params: vec![any_expr!(Parameter(
                    "name".into(),
                    Some(
                        any_expr!(TypeRepr {
                            name: "Int".into(),
                            generics: vec![],
                            conformances: vec![],
                            introduces_type: false
                        })
                        .into()
                    )
                )),],
                body: any_expr!(Block(vec![])).into(),
                ret: None,
                captures: vec![],
            })
        );
    }

    #[test]
    fn parses_call_no_args() {
        let parsed = parse("fizz()");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Call {
                callee: any_expr!(Variable("fizz".into())).into(),
                type_args: vec![],
                args: vec![]
            })
        );
    }

    #[test]
    fn parses_call_with_args() {
        let parsed = parse("fizz(foo: 123)");

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Call {
                callee: any_expr!(Variable("fizz".into())).into(),
                type_args: vec![],
                args: vec![any_expr!(CallArg {
                    label: Some("foo".into()),
                    value: any_expr!(LiteralInt("123".into())).into()
                })]
            })
        );
    }

    #[test]
    fn parses_let() {
        let parsed = parse("let fizz");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Let(Name::Raw("fizz".to_string()), None))
        );
    }

    #[test]
    fn parses_let_with_type() {
        let parsed = parse("let fizz: Int");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Let(
                Name::Raw("fizz".to_string()),
                Some(
                    any_expr!(TypeRepr {
                        name: "Int".into(),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    })
                    .into()
                )
            ))
        );
    }

    #[test]
    fn parses_let_with_tuple_type() {
        let parsed = parse("let fizz: (Int, Bool)");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Let(
                Name::Raw("fizz".to_string()),
                Some(
                    any_expr!(TupleTypeRepr(
                        vec![
                            any_expr!(TypeRepr {
                                name: "Int".into(),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                            .into(),
                            any_expr!(TypeRepr {
                                name: "Bool".into(),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                            .into()
                        ],
                        false
                    ))
                    .into()
                )
            ))
        );
    }

    #[test]
    fn parses_return_type_annotation() {
        let parsed = parse("func fizz() -> Int { 123 }");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("fizz".to_string())),
                generics: vec![],
                params: vec![],
                body: any_expr!(
                    Block(vec![any_expr!(Return(Some(
                        any_expr!(LiteralInt("123".into())).into()
                    )))])
                    .into()
                ),
                ret: Some(
                    any_expr!(TypeRepr {
                        name: "Int".into(),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    })
                    .into()
                ),
                captures: vec![],
            })
        );
    }

    #[test]
    fn parses_bools() {
        let parsed = parse("true\nfalse");
        assert_eq!(parsed.roots()[0], any_expr!(Expr::LiteralTrue));
        assert_eq!(parsed.roots()[1], any_expr!(Expr::LiteralFalse));
    }

    #[test]
    fn parses_if() {
        let parsed = parse("if true { 123 }");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::If(
                any_expr!(Expr::LiteralTrue).into(),
                any_expr!(
                    Expr::Block(vec![any_expr!(Return(Some(
                        any_expr!(LiteralInt("123".into())).into()
                    )))])
                    .into()
                )
                .into(),
                None
            ))
        );
    }

    #[test]
    fn parses_if_else() {
        let parsed = parse("if true { 123 } else { 456 }");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::If(
                any_expr!(Expr::LiteralTrue).into(),
                any_expr!(
                    Expr::Block(vec![any_expr!(Return(Some(
                        any_expr!(LiteralInt("123".into())).into()
                    )))])
                    .into()
                )
                .into(),
                Some(
                    any_expr!(
                        Expr::Block(vec![any_expr!(Return(Some(
                            any_expr!(LiteralInt("456".into())).into()
                        )))])
                        .into()
                    )
                    .into()
                )
            ))
        );
    }

    #[test]
    fn parses_loop() {
        let parsed = parse("loop { 123 }");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Loop(
                None,
                any_expr!(
                    Expr::Block(vec![any_expr!(Return(Some(
                        any_expr!(LiteralInt("123".into())).into()
                    )))])
                    .into()
                )
                .into()
            ))
        );
    }

    #[test]
    fn parses_break() {
        let parsed = parse("loop { break }");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Loop(
                None,
                any_expr!(Expr::Block(vec![any_expr!(Break)]).into()).into()
            ))
        );
    }

    #[test]
    fn parses_loop_with_condition() {
        let parsed = parse("loop true { 123 }");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Loop(
                Some(any_expr!(LiteralTrue).into()),
                any_expr!(
                    Expr::Block(vec![any_expr!(Return(Some(
                        any_expr!(LiteralInt("123".into())).into()
                    )))])
                    .into()
                )
                .into()
            ))
        );
    }

    #[test]
    fn parses_loop_with_binary_condition() {
        let parsed = parse("loop i < self.count { 123 }");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Loop(
                Some(
                    any_expr!(Binary(
                        any_expr!(Variable("i".into())).into(),
                        TokenKind::Less,
                        any_expr!(Member(
                            Some(any_expr!(Variable("self".into())).into()),
                            "count".into()
                        ))
                        .into()
                    ))
                    .into()
                ),
                any_expr!(
                    Expr::Block(vec![any_expr!(Return(Some(
                        any_expr!(LiteralInt("123".into())).into()
                    )))])
                    .into()
                )
                .into()
            ))
        );
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
                body: any_expr!(Block(vec![])).into()
            }
        );
    }

    #[test]
    fn parses_empty_enum_instantiation() {
        let parsed = parse("enum Fizz { case foo }\nFizz.foo");

        assert_eq!(
            parsed.roots()[1],
            any_expr!(Expr::Member(
                Some(any_expr!(Variable("Fizz".into())).into()),
                "foo".into()
            ))
        );
    }

    #[test]
    fn parses_empty_enum_instantiation_with_value() {
        let parsed = parse("enum Fizz { case foo(Int) }\nFizz.foo(123)");

        assert_eq!(
            parsed.roots()[1],
            any_expr!(Expr::Call {
                callee: any_expr!(Variable("Fizz".into())).into(),
                type_args: vec![],
                args: vec![any_expr!(CallArg {
                    label: Some("foo".into()),
                    value: any_expr!(LiteralInt("123".into())).into()
                })]
            })
        );
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

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::EnumDecl {
                name: "Fizz".into(),
                generics: vec![
                    any_expr!(TypeRepr {
                        name: "T".into(),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    }),
                    any_expr!(TypeRepr {
                        name: "Y".into(),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    }),
                ],
                conformances: vec![],
                body: any_expr!(Block(vec![any_expr!(EnumVariant(
                    Name::Raw("foo".into()),
                    vec![
                        any_expr!(TypeRepr {
                            name: "T".into(),
                            generics: vec![],
                            conformances: vec![],
                            introduces_type: false
                        })
                        .into(),
                        any_expr!(TypeRepr {
                            name: "Y".into(),
                            generics: vec![],
                            conformances: vec![],
                            introduces_type: false
                        })
                    ]
                )),]))
                .into()
            })
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
                body: any_expr!(Block(vec![
                    any_expr!(EnumVariant(Name::Raw("foo".into()), vec![])),
                    any_expr!(EnumVariant(Name::Raw("bar".into()), vec![])),
                    any_expr!(EnumVariant(Name::Raw("fizz".into()), vec![])),
                ]))
                .into()
            }
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
                body: any_expr!(Block(vec![
                    any_expr!(EnumVariant(
                        Name::Raw("foo".into()),
                        vec![
                            any_expr!(TypeRepr {
                                name: "Int".into(),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            }),
                            any_expr!(TypeRepr {
                                name: "Float".into(),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                        ]
                    )),
                    any_expr!(EnumVariant(
                        Name::Raw("bar".into()),
                        vec![
                            any_expr!(TypeRepr {
                                name: "Float".into(),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            }),
                            any_expr!(TypeRepr {
                                name: "Int".into(),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                        ]
                    )),
                ]))
                .into()
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

        assert_eq!(
            parsed.roots()[0].expr,
            Expr::Match(
                any_expr!(Variable("fizz".into())).into(),
                vec![
                    any_expr!(MatchArm(
                        any_expr!(ParsedPattern(Pattern::Variant {
                            enum_name: None,
                            variant_name: "foo".into(),
                            fields: vec![any_expr!(ParsedPattern(Pattern::Bind("name".into())))]
                        }))
                        .into(),
                        any_expr!(Variable("name".into())).into()
                    )),
                    any_expr!(MatchArm(
                        any_expr!(ParsedPattern(Pattern::Variant {
                            enum_name: None,
                            variant_name: "bar".into(),
                            fields: vec![]
                        }))
                        .into(),
                        any_expr!(Variable("fizz".into())).into()
                    ))
                ]
            )
        );
    }

    #[test]
    fn parses_fn_type_repr() {
        let parsed = parse(
            "
        func greet(using: (T) -> Y) {}
        ",
        );

        assert_eq!(
            parsed.roots()[0].expr,
            any_expr!(Expr::Func {
                name: Some(Name::Raw("greet".into())),
                generics: vec![],
                params: vec![any_expr!(Parameter(
                    Name::Raw("using".into()),
                    Some(
                        any_expr!(TypeRepr {
                            name: "T".into(),
                            generics: vec![],
                            conformances: vec![],
                            introduces_type: false
                        })
                        .into()
                    )
                ))],
                body: any_expr!(Block(vec![any_expr!(Return(None))])).into(),
                ret: None,
                captures: vec![],
            })
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
                body: any_expr!(Block(vec![
                    any_expr!(EnumVariant(
                        Name::Raw("val".into()),
                        vec![any_expr!(TypeRepr {
                            name: "Int".into(),
                            generics: vec![],
                            conformances: vec![],
                            introduces_type: false
                        })]
                    )),
                    any_expr!(EnumVariant(Name::Raw("nope".into()), vec![])),
                    any_expr!(Func {
                        name: Some(Name::Raw("fizz".into())),
                        generics: vec![],
                        params: vec![],
                        body: any_expr!(Block(vec![any_expr!(Return(None))])).into(),
                        ret: None,
                        captures: vec![],
                    })
                    .into()
                ]))
                .into()
            }
        );
    }

    #[test]
    fn parses_variable_assignment() {
        let parsed = parse(
            "
            foo = 123
            ",
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Assignment(
                any_expr!(Variable("foo".into())).into(),
                any_expr!(LiteralInt("123".into())).into()
            ))
        );
    }

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

    #[test]
    fn parses_array_literal() {
        let parsed = parse("[1, 2, 3]");
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::LiteralArray(vec![
                any_expr!(Expr::LiteralInt("1".into())),
                any_expr!(Expr::LiteralInt("2".into())),
                any_expr!(Expr::LiteralInt("3".into())),
            ]))
        );
    }

    #[test]
    fn parses_array_literal_with_newlines() {
        let parsed = parse(
            "[
          1
          ,
        2, 3
        ]",
        );
        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::LiteralArray(vec![
                any_expr!(Expr::LiteralInt("1".into())),
                any_expr!(Expr::LiteralInt("2".into())),
                any_expr!(Expr::LiteralInt("3".into())),
            ]))
        );
    }

    #[test]
    fn parses_extensions() {
        let parsed = parse(
            "
        extend Person: Something<String> {
            func foo() {}
        }
        ",
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Extend {
                name: Name::Raw("Person".into()),
                generics: vec![],
                conformances: vec![any_expr!(TypeRepr {
                    name: Name::Raw("Something".into()),
                    generics: vec![any_expr!(TypeRepr {
                        name: Name::Raw("String".into()),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    })],
                    conformances: vec![],
                    introduces_type: false
                })],
                body: any_expr!(Block(vec![any_expr!(Func {
                    name: Some("foo".into()),
                    generics: vec![],
                    params: vec![],
                    body: any_expr!(Block(vec![])).into(),
                    ret: None,
                    captures: vec![]
                })]))
                .into()
            })
        );
    }

    #[test]
    fn parses_empty_struct_def() {
        let parsed = parse(
            "
        struct Person {}
        ",
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_expr!(Block(vec![])).into()
            })
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
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_expr!(Block(vec![
                    any_expr!(Property {
                        name: Name::Raw("age".into()),
                        type_repr: Some(
                            any_expr!(TypeRepr {
                                name: Name::Raw("Int".into()),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                            .into()
                        ),
                        default_value: None
                    }),
                    any_expr!(Property {
                        name: Name::Raw("count".into()),
                        type_repr: Some(
                            any_expr!(TypeRepr {
                                name: Name::Raw("Int".into()),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                            .into()
                        ),
                        default_value: Some(any_expr!(LiteralInt("123".into())).into()),
                    }),
                    any_expr!(Property {
                        name: Name::Raw("height".into()),
                        type_repr: None,
                        default_value: Some(any_expr!(LiteralInt("456".into())).into()),
                    }),
                ]))
                .into()
            })
        );
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
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_expr!(Block(vec![
                    any_expr!(Property {
                        name: Name::Raw("age".into()),
                        type_repr: Some(
                            any_expr!(TypeRepr {
                                name: Name::Raw("Int".into()),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                            .into()
                        ),
                        default_value: None
                    }),
                    any_expr!(Property {
                        name: Name::Raw("age".into()),
                        type_repr: Some(
                            any_expr!(TypeRepr {
                                name: Name::Raw("Int".into()),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                            .into()
                        ),
                        default_value: Some(any_expr!(LiteralInt("456".into())).into()),
                    }),
                ]))
                .into()
            })
        );
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
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("fizz".into())),
                generics: vec![],
                params: vec![],
                body: any_expr!(Block(vec![])).into(),
                ret: None,
                captures: vec![]
            })
        );
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
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::ProtocolDecl {
                name: "Aged".into(),
                associated_types: vec![],
                body: any_expr!(
                    Block(vec![
                        any_expr!(Property {
                            name: Name::Raw("age".into()),
                            type_repr: Some(
                                any_expr!(TypeRepr {
                                    name: Name::Raw("Int".into()),
                                    generics: vec![],
                                    conformances: vec![],
                                    introduces_type: false
                                })
                                .into()
                            ),
                            default_value: None
                        }),
                        any_expr!(FuncSignature {
                            name: Name::Raw("getAge".into()),
                            params: vec![],
                            generics: vec![],
                            ret: any_expr!(TypeRepr {
                                name: Name::Raw("Int".into()),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                            .into()
                        })
                    ])
                    .into()
                ),
                conformances: vec![],
            })
        );
    }

    #[test]
    fn parses_protocol_conformance() {
        let parsed = parse(
            "
        struct Person: Aged {}
    ",
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![
                    any_expr!(TypeRepr {
                        name: Name::Raw("Aged".into()),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    })
                    .into()
                ],
                body: any_expr!(Block(vec![])).into()
            })
        );
    }

    #[test]
    fn parses_type_repr_conformance() {
        let parsed = parse(
            "
        func foo<T: Fizz>(x) -> T { x }
    ",
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Func {
                name: Some(Name::Raw("foo".into())),
                generics: vec![
                    any_expr!(TypeRepr {
                        name: Name::Raw("T".into()),
                        generics: vec![],
                        conformances: vec![
                            any_expr!(TypeRepr {
                                name: Name::Raw("Fizz".into()),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false
                            })
                            .into()
                        ],
                        introduces_type: false
                    })
                    .into()
                ],
                params: vec![any_expr!(Parameter(Name::Raw("x".into()), None.into()))],
                body: any_expr!(Block(vec![
                    any_expr!(Variable(Name::Raw("x".into()))).into()
                ]))
                .into(),
                ret: Some(
                    any_expr!(TypeRepr {
                        name: Name::Raw("T".into()),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    })
                    .into()
                ),
                captures: vec![]
            })
        );
    }

    #[test]
    fn parses_incomplete_member_expr() {
        let parsed = parse(
            "
        foo.
        ",
        );

        assert_eq!(
            parsed.roots()[0],
            any_expr!(Expr::Incomplete(IncompleteExpr::Member(Some(
                any_expr!(Variable(Name::Raw("foo".into()))).into()
            ))))
        )
    }

    #[test]
    fn parses_incomplete_func_expr() {
        assert_eq!(
            parse(
                "
            func
            ",
            )
            .roots()[0],
            any_expr!(Expr::Incomplete(IncompleteExpr::Func {
                name: None,
                params: None,
                generics: None,
                ret: None,
                body: None
            }))
        )
    }

    #[test]
    fn parses_incomplete_func_expr_with_name() {
        assert_eq!(
            parse(
                "
            func foo
            ",
            )
            .roots()[0],
            any_expr!(Expr::Incomplete(IncompleteExpr::Func {
                name: Some(Name::Raw("foo".into())),
                params: None,
                generics: None,
                ret: None,
                body: None
            }))
        )
    }

    #[test]
    fn parses_incomplete_func_expr_with_name_and_open_paren() {
        assert_eq!(
            parse(
                "
            func foo(
            ",
            )
            .roots()[0],
            any_expr!(Expr::Incomplete(IncompleteExpr::Func {
                name: Some(Name::Raw("foo".into())),
                params: Some(vec![]),
                generics: None,
                ret: None,
                body: None
            }))
        )
    }

    #[test]
    fn parses_incomplete_func_expr_with_name_and_open_paren_and_param() {
        assert_eq!(
            parse(
                "
            func foo(fizz
            ",
            )
            .roots()[0],
            any_expr!(Expr::Incomplete(IncompleteExpr::Func {
                name: Some(Name::Raw("foo".into())),
                params: Some(vec![any_expr!(Parameter(
                    Name::Raw("fizz".into()),
                    None.into()
                ))]),
                generics: None,
                ret: None,
                body: None
            }))
        )
    }

    #[test]
    fn parses_incomplete_func_expr_without_body() {
        assert_eq!(
            parse(
                "
            func foo(fizz) 
            ",
            )
            .roots()[0],
            any_expr!(Expr::Incomplete(IncompleteExpr::Func {
                name: Some(Name::Raw("foo".into())),
                params: Some(vec![any_expr!(Parameter(
                    Name::Raw("fizz".into()),
                    None.into()
                ))]),
                generics: Some(vec![]),
                ret: None,
                body: None
            }))
        )
    }

    #[test]
    fn parses_incomplete_func_expr_with_incomplete_body() {
        assert_eq!(
            parse(
                "
            func foo(fizz) {
            ",
            )
            .roots()[0],
            any_expr!(Expr::Incomplete(IncompleteExpr::Func {
                name: Some(Name::Raw("foo".into())),
                params: Some(vec![any_expr!(Parameter(
                    Name::Raw("fizz".into()),
                    None.into()
                ))]),
                generics: Some(vec![]),
                ret: None,
                body: None
            }))
        )
    }
}
