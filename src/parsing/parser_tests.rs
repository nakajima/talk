#[cfg(test)]
pub mod tests {
    use std::assert_matches::assert_matches;

    use crate::{
        any_block, any_expr,
        ast::{AST, Parsed},
        id_generator::IDGenerator,
        label::Label,
        lexer::Lexer,
        name::Name,
        node::Node,
        node_kinds::{
            block::Block,
            call_arg::CallArg,
            decl::{Decl, DeclKind},
            expr::{Expr, ExprKind},
            func::Func,
            generic_decl::GenericDecl,
            match_arm::MatchArm,
            parameter::Parameter,
            pattern::{Pattern, PatternKind},
            stmt::{Stmt, StmtKind},
            type_annotation::{TypeAnnotation, TypeAnnotationKind},
        },
        parser::Parser,
        span::Span,
        token_kind::TokenKind,
    };

    use crate::node_id::NodeID;

    #[macro_export]
    macro_rules! expr {
        ($expr:pat) => {
            Expr {
                id: _,
                span: _,
                kind: $expr,
            }
        };
    }

    #[macro_export]
    macro_rules! expr_stmt {
        ($expr:pat) => {
            Stmt {
                id: _,
                span: _,
                kind: StmtKind::Expr(Expr {
                    id: _,
                    span: _,
                    kind: $expr,
                }),
            }
        };
    }

    #[macro_export]
    macro_rules! any_expr_stmt {
        ($expr:expr) => {
            $crate::node_kinds::stmt::Stmt {
                id: $crate::node_id::NodeID::ANY,
                span: $crate::parsing::span::Span::ANY,
                kind: $crate::node_kinds::stmt::StmtKind::Expr(Expr {
                    id: $crate::node_id::NodeID::ANY,
                    span: $crate::parsing::span::Span::ANY,
                    kind: $expr,
                }),
            }
            .into()
        };
    }

    #[macro_export]
    macro_rules! any_decl {
        ($expr:expr) => {
            $crate::node_kinds::decl::Decl {
                id: NodeID::ANY,
                span: $crate::parsing::span::Span::ANY,
                kind: $expr,
            }
        };
    }

    #[macro_export]
    macro_rules! annotation {
        ($expr:expr) => {
            TypeAnnotation {
                id: NodeID::ANY,
                span: $crate::parsing::span::Span::ANY,
                kind: $expr,
            }
        };
    }

    #[macro_export]
    macro_rules! any_stmt {
        ($expr:expr) => {
            $crate::node_kinds::stmt::Stmt {
                id: NodeID::ANY,
                kind: $expr,
                span: $crate::parsing::span::Span::ANY,
            }
        };
    }

    pub fn parse(code: &'static str) -> AST<Parsed> {
        let lexer = Lexer::new(code);
        let ids = &mut IDGenerator::default();
        let parser = Parser::new("-", ids, lexer);
        parser.parse().unwrap()
    }

    fn parse_pattern(input: &'static str) -> Pattern {
        let lexer = Lexer::new(input);
        let ids = &mut IDGenerator::default();
        let mut parser = Parser::new("-", ids, lexer);
        parser.advance();
        parser.advance();
        parser.parse_pattern().unwrap()
    }

    #[test]
    fn parses_literal_expr() {
        let parsed = parse("123");

        assert_matches!(
            parsed.roots[0],
            Node::Stmt(Stmt {
                kind: StmtKind::Expr(Expr {
                    kind: ExprKind::LiteralInt(_),
                    ..
                },),
                ..
            })
        );
    }

    #[test]
    fn parses_string_literal() {
        let parsed = parse("\"hello world\"");
        assert_matches!(
            parsed.roots[0].as_stmt().kind,
            StmtKind::Expr(Expr {
                kind: ExprKind::LiteralString(_),
                ..
            },)
        );
    }

    #[test]
    fn handles_semicolons() {
        let parsed = parse("123 ; 456");
        assert_matches!(
            parsed.roots[0].as_stmt().kind,
            StmtKind::Expr(Expr {
                kind: ExprKind::LiteralInt(_),
                ..
            },)
        );
        assert_matches!(
            parsed.roots[1].as_stmt().kind,
            StmtKind::Expr(Expr {
                kind: ExprKind::LiteralInt(_),
                ..
            },)
        );
    }

    #[test]
    fn handles_semicolon_in_body() {
        let parsed = parse("struct Person { ; }");

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![])
            })
        );
    }

    // #[test]
    // fn handles_semicolons_infix() {
    //     let parsed = parse("func() { };()");

    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Func {
    //             name: None,
    //             generics: vec![],
    //             params: vec![],
    //             body: any_expr!(Block(vec![])).into(),
    //             ret: None,
    //             captures: vec![],
    //             attributes: vec![],
    //         })
    //     );
    //     assert_eq!(parsed.roots()[1], any_expr!(Expr::Tuple(vec![])));
    // }

    #[test]
    fn parses_eq() {
        let parsed = parse("1 == 2");
        assert_matches!(
            parsed.roots[0].as_stmt().kind,
            StmtKind::Expr(Expr {
                kind: ExprKind::Binary(_, _, _),
                ..
            })
        );
    }

    #[test]
    fn stores_expr_meta() {
        let parsed = parse("1 + 2");
        let meta = &parsed.meta;
        let meta = meta.get(&parsed.roots[0].as_stmt().id).unwrap();

        assert_eq!(meta.start.start, 0);
        assert_eq!(meta.start.end, 1);
        assert_eq!(meta.end.start, 4);
        assert_eq!(meta.end.end, 5);
        assert_eq!(meta.source_range(), 0..5);
    }

    #[test]
    fn parses_not_eq() {
        let parsed = parse("1 != 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::BangEquals,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_greater() {
        let parsed = parse("1 > 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Greater,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_greater_eq() {
        let parsed = parse("1 >= 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::GreaterEquals,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_less() {
        let parsed = parse("1 < 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Less,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_less_eq() {
        let parsed = parse("1 <= 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::LessEquals,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_plus_expr() {
        let parsed = parse("1 + 2");

        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Plus,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_minus_expr() {
        let parsed = parse("1 - 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Minus,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_div_expr() {
        let parsed = parse("1 / 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Slash,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_mult_expr() {
        let parsed = parse("1 * 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Star,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_greater_expr() {
        let parsed = parse("1 > 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Greater,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_caret_expr() {
        let parsed = parse("1 ^ 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Caret,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_pipe_expr() {
        let parsed = parse("1 | 2");
        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Pipe,
                    box expr!(ExprKind::LiteralInt(_)),
                )
            )
        );
    }

    #[test]
    fn parses_correct_precedence() {
        let parsed = parse("1 + 2 * 2");

        assert_matches!(
            parsed.roots[0].as_stmt(),
            expr_stmt!(
                ExprKind::Binary(
                    box expr!(ExprKind::LiteralInt(_)),
                    TokenKind::Plus,
                    box expr!(
                        ExprKind::Binary(
                            box expr!(ExprKind::LiteralInt(_)),
                            TokenKind::Star,
                            box expr!(ExprKind::LiteralInt(_)),
                        )
                    ),
                )
            )
        );
    }

    #[test]
    fn parses_group() {
        let parsed = parse("(1 + 2)");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Tuple(vec![any_expr!(ExprKind::Binary(
                any_expr!(ExprKind::LiteralInt("1".into())).into(),
                TokenKind::Plus,
                any_expr!(ExprKind::LiteralInt("2".into())).into()
            ))]))
        );
    }

    #[test]
    fn parses_var() {
        let parsed = parse("hello\nworld");

        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Variable(Name::Raw("hello".to_string())))
        );

        assert_eq!(
            *parsed.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Variable(Name::Raw("world".to_string())))
        );
    }

    #[test]
    fn parses_unary_bang() {
        let parsed = parse("!hello");

        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Unary(
                TokenKind::Bang,
                any_expr!(ExprKind::Variable("hello".into())).into()
            ))
        );
    }

    #[test]
    fn parses_unary_minus() {
        let parsed = parse("-1");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Unary(
                TokenKind::Minus,
                any_expr!(ExprKind::LiteralInt("1".into())).into()
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
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Tuple(vec![
                any_expr!(ExprKind::LiteralInt("1".into())),
                any_expr!(ExprKind::LiteralInt("2".into())),
                any_expr!(ExprKind::Variable("fizz".into())),
            ]))
        );
    }

    #[test]
    fn parses_empty_tuple() {
        let parsed = parse("( )");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Tuple(vec![]))
        );
    }

    // #[test]
    // fn parses_return() {
    //     let _parsed = parse("func() { return }");
    // }

    #[test]
    fn parses_func_literal_no_name_no_args() {
        let parsed = parse("func foo() { }");

        assert_eq!(
            *parsed.roots[0].as_decl(),
            Decl {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: DeclKind::Func(Func {
                    id: NodeID::ANY,
                    name: "foo".into(),
                    generics: vec![],
                    params: vec![],
                    body: Block {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        args: vec![],
                        body: vec![],
                    },
                    ret: None,
                    attributes: vec![]
                })
            }
        );
    }

    #[test]
    fn parses_func_with_generic_param() {
        let parsed = parse("func c(a: Array<Int>) { a }");
        let DeclKind::Func(Func { params, .. }) = &parsed.roots[0].as_decl().kind else {
            panic!("didn't get func");
        };

        assert_eq!(params.len(), 1);
        assert_eq!(params[0].name, "a".into());
        assert_eq!(
            params[0].type_annotation.clone().unwrap().kind,
            TypeAnnotationKind::Nominal {
                name: "Array".into(),
                generics: vec![TypeAnnotation {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: TypeAnnotationKind::Nominal {
                        name: "Int".into(),
                        generics: vec![]
                    }
                }]
            }
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
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Func(Func {
                id: NodeID::ANY,
                name: Name::Raw("greet".to_string()),
                generics: vec![],
                params: vec![Parameter {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    name: "a".into(),
                    type_annotation: None
                }],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![any_expr_stmt!(ExprKind::Variable("a".into()))],
                },
                ret: None,
                attributes: vec![],
            }))
        );
    }

    #[test]
    fn parses_func_with_generics() {
        let parsed = parse(
            "
        func greet<T>(t) -> T { t }
        ",
        );

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Func(Func {
                id: NodeID::ANY,
                name: Name::Raw("greet".to_string()),
                generics: vec![GenericDecl {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    name: "T".into(),
                    generics: vec![],
                    conformances: vec![],
                }],
                params: vec![Parameter::new(NodeID::ANY, "t".into(), None, Span::ANY)],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![any_expr_stmt!(ExprKind::Variable("t".into()))],
                },
                ret: Some(TypeAnnotation {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: TypeAnnotationKind::Nominal {
                        name: "T".into(),
                        generics: vec![]
                    }
                }),
                attributes: vec![],
            }))
        );
    }

    #[test]
    fn parses_func_call_with_generics() {
        let parsed = parse("foo<T>()");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Call {
                callee: any_expr!(ExprKind::Variable("foo".into())).into(),
                type_args: vec![TypeAnnotation {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: TypeAnnotationKind::Nominal {
                        name: "T".into(),
                        generics: vec![]
                    }
                }],
                args: vec![]
            })
        );
    }

    #[test]
    fn parses_multiple_roots() {
        let parsed = parse("func hello() {}\nfunc world() {}");
        assert_eq!(2, parsed.roots.len());
        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Func(Func {
                id: NodeID::ANY,
                name: Name::Raw("hello".to_string()),
                generics: vec![],
                params: vec![],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![],
                },
                ret: None,
                attributes: vec![],
            }))
        );

        assert_eq!(
            *parsed.roots[1].as_decl(),
            any_decl!(DeclKind::Func(Func {
                id: NodeID::ANY,
                name: Name::Raw("world".to_string()),
                generics: vec![],
                params: vec![],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![],
                },
                ret: None,
                attributes: vec![],
            }))
        );
    }

    #[test]
    fn parses_func_literal_name_with_args() {
        let parsed = parse("func greet(one, two) { }");

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Func(Func {
                id: NodeID::ANY,
                name: Name::Raw("greet".to_string()),
                generics: vec![],
                params: vec![
                    Parameter {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: "one".into(),
                        type_annotation: None,
                    },
                    Parameter {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: "two".into(),
                        type_annotation: None,
                    },
                ],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![],
                },
                ret: None,
                attributes: vec![],
            }))
        );
    }

    #[test]
    fn parses_param_type() {
        let parsed = parse("func greet(name: Int) {}");
        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Func(Func {
                id: NodeID::ANY,
                name: Name::Raw("greet".to_string()),
                generics: vec![],
                params: vec![Parameter {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    name: "name".into(),
                    type_annotation: Some(TypeAnnotation {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: TypeAnnotationKind::Nominal {
                            name: "Int".into(),
                            generics: vec![]
                        }
                    }),
                }],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![],
                },
                ret: None,
                attributes: vec![],
            }))
        );
    }

    #[test]
    fn parses_call_no_args() {
        let parsed = parse("fizz()");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Call {
                callee: any_expr!(ExprKind::Variable("fizz".into())).into(),
                type_args: vec![],
                args: vec![]
            })
        );
    }

    #[test]
    fn parses_call_with_args() {
        let parsed = parse("fizz(foo: 123)");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Call {
                callee: any_expr!(ExprKind::Variable("fizz".into())).into(),
                type_args: vec![],
                args: vec![CallArg {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    label: "foo".into(),
                    value: any_expr!(ExprKind::LiteralInt("123".into()))
                }]
            })
        );
    }

    #[test]
    fn parses_let() {
        let parsed = parse("let fizz");
        assert_eq!(
            *parsed.roots[0].as_decl(),
            Decl {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: DeclKind::Let {
                    lhs: Pattern {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: PatternKind::Bind("fizz".into())
                    },
                    type_annotation: None,
                    value: None
                }
            }
        );
    }

    #[test]
    fn parses_let_with_type() {
        let parsed = parse("let fizz: Int");
        assert_eq!(
            *parsed.roots[0].as_decl(),
            Decl {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: DeclKind::Let {
                    lhs: Pattern {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: PatternKind::Bind("fizz".into())
                    },
                    type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                        name: "Int".into(),
                        generics: vec![]
                    })),
                    value: None
                }
            }
        );
    }

    #[test]
    fn parses_let_with_tuple_type() {
        let parsed = parse("let fizz: (Int, Bool)");
        assert_eq!(
            *parsed.roots[0].as_decl(),
            Decl {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: DeclKind::Let {
                    lhs: Pattern {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: PatternKind::Bind("fizz".into())
                    },
                    type_annotation: Some(TypeAnnotation {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: TypeAnnotationKind::Tuple(vec![
                            TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "Int".into(),
                                    generics: vec![]
                                },
                            },
                            TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "Bool".into(),
                                    generics: vec![]
                                },
                            },
                        ])
                    }),
                    value: None
                }
            }
        );
    }

    #[test]
    fn parses_return_type_annotation() {
        let parsed = parse("func fizz() -> Int { 123 }");
        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Func(Func {
                id: NodeID::ANY,
                name: Name::Raw("fizz".to_string()),
                generics: vec![],
                params: vec![],
                body: Block {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    args: vec![],
                    body: vec![any_expr_stmt!(ExprKind::LiteralInt("123".into()))]
                },
                ret: Some(TypeAnnotation {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: TypeAnnotationKind::Nominal {
                        name: "Int".into(),
                        generics: vec![]
                    }
                }),
                attributes: vec![],
            }))
        );
    }

    #[test]
    fn parses_bools() {
        let parsed = parse("true\nfalse");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::LiteralTrue)
        );
        assert_eq!(
            *parsed.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::LiteralFalse)
        );
    }

    #[test]
    fn parses_if() {
        let parsed = parse("if true { 123 }");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            Stmt {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: StmtKind::If(
                    any_expr!(ExprKind::LiteralTrue),
                    Block {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        args: vec![],
                        body: vec![any_expr_stmt!(ExprKind::LiteralInt("123".into()))]
                    }
                )
            }
        );
    }

    #[test]
    fn parses_if_else() {
        let parsed = parse("if true { 123 } else { 456 }");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::If(
                any_expr!(ExprKind::LiteralTrue).into(),
                any_block!(vec![any_expr_stmt!(ExprKind::LiteralInt("123".into()))]),
                any_block!(vec![any_expr_stmt!(ExprKind::LiteralInt("456".into()))]),
            ))
        );
    }

    #[test]
    fn parses_loop() {
        let parsed = parse("loop { 123 }");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            Stmt {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: StmtKind::Loop(
                    None,
                    any_block!(vec![any_expr_stmt!(ExprKind::LiteralInt("123".into()))])
                )
            }
        );
    }

    #[test]
    fn parses_break() {
        let parsed = parse("loop { break }");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            Stmt {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: StmtKind::Loop(
                    None,
                    any_block!(vec![
                        Stmt {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: StmtKind::Break
                        }
                        .into()
                    ])
                )
            }
        );
    }

    #[test]
    fn parses_loop_with_condition() {
        let parsed = parse("loop true { 123 }");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            Stmt {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: StmtKind::Loop(
                    Some(any_expr!(ExprKind::LiteralTrue)),
                    any_block!(vec![any_expr_stmt!(ExprKind::LiteralInt("123".into()))])
                )
            }
        );
    }

    #[test]
    fn parses_loop_with_binary_condition() {
        let parsed = parse("loop i < self.count { 123 }");
        assert_eq!(
            *parsed.roots[0].as_stmt(),
            Stmt {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: StmtKind::Loop(
                    Some(any_expr!(ExprKind::Binary(
                        Box::new(any_expr!(ExprKind::Variable("i".into()))),
                        TokenKind::Less,
                        Box::new(any_expr!(ExprKind::Member(
                            Some(Box::new(any_expr!(ExprKind::Variable("self".into())))),
                            "count".into()
                        )))
                    ))),
                    any_block!(vec![any_expr_stmt!(ExprKind::LiteralInt("123".into()))])
                )
            }
        );
    }

    #[test]
    fn parses_empty_enum_decl() {
        let parsed = parse("enum Fizz {}");

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Enum {
                name: "Fizz".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![])
            })
        );
    }

    #[test]
    fn parses_empty_enum_instantiation() {
        let parsed = parse("enum Fizz { case foo }\nFizz.foo");

        assert_eq!(
            *parsed.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Member(
                Some(any_expr!(ExprKind::Variable("Fizz".into())).into()),
                "foo".into()
            ))
        );
    }

    #[test]
    fn parses_empty_enum_instantiation_with_value() {
        let parsed = parse("enum Fizz { case foo(Int) }\nFizz.foo(123)");

        assert_eq!(
            *parsed.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Call {
                callee: any_expr!(ExprKind::Member(
                    Some(any_expr!(ExprKind::Variable("Fizz".into())).into()),
                    "foo".into()
                ))
                .into(),
                type_args: vec![],
                args: vec![CallArg {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    label: Label::Positional(0),
                    value: any_expr!(ExprKind::LiteralInt("123".into()))
                }]
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
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Enum {
                name: "Fizz".into(),
                generics: vec![
                    GenericDecl {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: "T".into(),
                        generics: vec![],
                        conformances: vec![]
                    },
                    GenericDecl {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: "Y".into(),
                        generics: vec![],
                        conformances: vec![]
                    },
                ],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::EnumVariant(
                        Name::Raw("foo".into()),
                        vec![
                            TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "T".into(),
                                    generics: vec![]
                                }
                            },
                            TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "Y".into(),
                                    generics: vec![]
                                }
                            }
                        ]
                    ))
                    .into(),
                    any_decl!(DeclKind::EnumVariant(Name::Raw("bar".into()), vec![])).into()
                ])
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
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Enum {
                name: "Fizz".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(
                    (vec![
                        any_decl!(DeclKind::EnumVariant(Name::Raw("foo".into()), vec![])).into(),
                        any_decl!(DeclKind::EnumVariant(Name::Raw("bar".into()), vec![])).into(),
                        any_decl!(DeclKind::EnumVariant(Name::Raw("fizz".into()), vec![])).into(),
                    ])
                )
            })
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
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Enum {
                name: "Fizz".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::EnumVariant(
                        Name::Raw("foo".into()),
                        vec![
                            TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "Int".into(),
                                    generics: vec![]
                                },
                            },
                            TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "Float".into(),
                                    generics: vec![]
                                },
                            },
                        ]
                    ))
                    .into(),
                    any_decl!(DeclKind::EnumVariant(
                        Name::Raw("bar".into()),
                        vec![
                            TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "Float".into(),
                                    generics: vec![]
                                },
                            },
                            TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "Int".into(),
                                    generics: vec![]
                                },
                            },
                        ]
                    ))
                    .into(),
                ])
            })
        );
    }

    #[test]
    fn parses_basic_match() {
        let parsed = parse(
            "match fizz {
                1 -> true,
                0 -> false
            }",
        );

        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Match(
                any_expr!(ExprKind::Variable("fizz".into())).into(),
                vec![
                    MatchArm {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        pattern: Pattern {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: PatternKind::LiteralInt("1".into())
                        },
                        body: any_block!(vec![Node::Stmt(any_expr_stmt!(ExprKind::LiteralTrue))])
                    },
                    MatchArm {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        pattern: Pattern {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: PatternKind::LiteralInt("0".into())
                        },
                        body: any_block!(vec![Node::Stmt(any_expr_stmt!(ExprKind::LiteralFalse))])
                    },
                ]
            ))
        );
    }

    #[test]
    fn parses_basic_match_with_braces() {
        let parsed = parse(
            "match fizz {
                1 -> { true }
                0 -> { false }
            }",
        );

        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Match(
                any_expr!(ExprKind::Variable("fizz".into())).into(),
                vec![
                    MatchArm {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        pattern: Pattern {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: PatternKind::LiteralInt("1".into())
                        },
                        body: any_block!(vec![Node::Stmt(any_expr_stmt!(ExprKind::LiteralTrue))])
                    },
                    MatchArm {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        pattern: Pattern {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: PatternKind::LiteralInt("0".into())
                        },
                        body: any_block!(vec![Node::Stmt(any_expr_stmt!(ExprKind::LiteralFalse))])
                    },
                ]
            ))
        );
    }

    #[test]
    fn parses_match() {
        let parsed = parse(
            "match fizz {
                .foo(name) -> name,
                .bar -> fizz
            }",
        );

        assert_eq!(
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Match(
                any_expr!(ExprKind::Variable("fizz".into())).into(),
                vec![
                    MatchArm {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        pattern: Pattern {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: PatternKind::Variant {
                                enum_name: None,
                                variant_name: "foo".into(),
                                fields: vec![Pattern {
                                    id: NodeID::ANY,
                                    span: Span::ANY,
                                    kind: PatternKind::Bind("name".into())
                                }]
                            }
                        },
                        body: any_block!(vec![Node::Stmt(any_expr_stmt!(ExprKind::Variable(
                            "name".into()
                        )))])
                    },
                    MatchArm {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        pattern: Pattern {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: PatternKind::Variant {
                                enum_name: None,
                                variant_name: "bar".into(),
                                fields: vec![]
                            }
                        },
                        body: any_block!(vec![any_expr_stmt!(ExprKind::Variable("fizz".into()))])
                    }
                ]
            ))
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
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Func(Func {
                id: NodeID::ANY,
                name: Name::Raw("greet".into()),
                generics: vec![],
                params: vec![Parameter {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    name: Name::Raw("using".into()),
                    type_annotation: Some(TypeAnnotation {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: TypeAnnotationKind::Func {
                            params: vec![TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "T".into(),
                                    generics: vec![]
                                }
                            }],
                            returns: Box::new(TypeAnnotation {
                                id: NodeID::ANY,
                                span: Span::ANY,
                                kind: TypeAnnotationKind::Nominal {
                                    name: "Y".into(),
                                    generics: vec![]
                                }
                            })
                        }
                    })
                }],
                body: any_block!(vec![]),
                ret: None,
                attributes: vec![],
            }))
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
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Enum {
                name: "MyEnum".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::EnumVariant(
                        Name::Raw("val".into()),
                        vec![TypeAnnotation {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: TypeAnnotationKind::Nominal {
                                name: "Int".into(),
                                generics: vec! {}
                            }
                        }]
                    ))
                    .into(),
                    any_decl!(DeclKind::EnumVariant(Name::Raw("nope".into()), vec![])).into(),
                    any_decl!(DeclKind::Method {
                        is_static: false,
                        func: Box::new(any_decl!(DeclKind::Func(Func {
                            id: NodeID::ANY,
                            name: Name::Raw("fizz".into()),
                            generics: vec![],
                            params: vec![],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::LiteralInt(
                                "123".into()
                            ))]),
                            ret: None,
                            attributes: vec![],
                        })))
                    })
                    .into()
                ])
            })
        )
    }

    #[test]
    fn parses_let_decl_assignment() {
        let parsed = parse(
            "
            let foo = 123
            ",
        );

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind("foo".into())
                },
                type_annotation: None,
                value: Some(any_expr!(ExprKind::LiteralInt("123".into())))
            })
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
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Assignment(
                any_expr!(ExprKind::Variable("foo".into())),
                any_expr!(ExprKind::LiteralInt("123".into()))
            ))
        );
    }

    #[test]
    fn parses_wildcard() {
        assert_eq!(parse_pattern("_ ").kind, PatternKind::Wildcard);
    }

    #[test]
    fn parses_literal_int() {
        assert_eq!(
            parse_pattern("123").kind,
            PatternKind::LiteralInt("123".into())
        );
    }

    #[test]
    fn parses_literal_float() {
        assert_eq!(
            parse_pattern("123.0").kind,
            PatternKind::LiteralFloat("123.0".into())
        );
    }

    #[test]
    fn parses_literal_bools() {
        assert_eq!(parse_pattern("true").kind, PatternKind::LiteralTrue);
        assert_eq!(parse_pattern("false").kind, PatternKind::LiteralFalse);
    }

    #[test]
    fn parses_variant_pattern() {
        assert_eq!(
            parse_pattern("Fizz.buzz").kind,
            PatternKind::Variant {
                enum_name: Some(Name::Raw("Fizz".into())),
                variant_name: "buzz".into(),
                fields: vec![]
            }
        );

        assert_eq!(
            parse_pattern(".foo").kind,
            PatternKind::Variant {
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
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::LiteralArray(vec![
                any_expr!(ExprKind::LiteralInt("1".into())),
                any_expr!(ExprKind::LiteralInt("2".into())),
                any_expr!(ExprKind::LiteralInt("3".into())),
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
            *parsed.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::LiteralArray(vec![
                any_expr!(ExprKind::LiteralInt("1".into())),
                any_expr!(ExprKind::LiteralInt("2".into())),
                any_expr!(ExprKind::LiteralInt("3".into())),
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
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Extend {
                name: Name::Raw("Person".into()),
                generics: vec![],
                conformances: vec![TypeAnnotation {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: TypeAnnotationKind::Nominal {
                        name: "Something".into(),
                        generics: vec![TypeAnnotation {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            kind: TypeAnnotationKind::Nominal {
                                name: "String".into(),
                                generics: vec![]
                            }
                        }]
                    }
                }],
                body: any_block!(vec![
                    any_decl!(DeclKind::Method {
                        func: Box::new(any_decl!(DeclKind::Func(Func {
                            id: NodeID::ANY,
                            name: "foo".into(),
                            generics: vec![],
                            params: vec![],
                            body: any_block!(vec![]),
                            ret: None,
                            attributes: vec![],
                        }))),
                        is_static: false
                    })
                    .into()
                ])
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
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![])
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
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::Property {
                        name: Name::Raw("age".into()),
                        is_static: false,
                        default_value: None,
                        type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                            name: "Int".into(),
                            generics: vec![],
                        }))
                    })
                    .into(),
                    any_decl!(DeclKind::Property {
                        name: Name::Raw("count".into()),
                        is_static: false,
                        default_value: Some(any_expr!(ExprKind::LiteralInt("123".into()))),
                        type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                            name: "Int".into(),
                            generics: vec![],
                        }))
                    })
                    .into(),
                    any_decl!(DeclKind::Property {
                        name: Name::Raw("height".into()),
                        is_static: false,
                        default_value: Some(any_expr!(ExprKind::LiteralInt("456".into()))),
                        type_annotation: None
                    })
                    .into(),
                ])
            })
        );
    }

    #[test]
    fn parses_static_struct_properties() {
        let parsed = parse(
            "
        struct Person {
            static let age: Int
            static let count: Int = 123
            static let height = 456
        }
        ",
        );

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::Property {
                        name: Name::Raw("age".into()),
                        is_static: true,
                        default_value: None,
                        type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                            name: "Int".into(),
                            generics: vec![],
                        }))
                    })
                    .into(),
                    any_decl!(DeclKind::Property {
                        name: Name::Raw("count".into()),
                        is_static: true,
                        default_value: Some(any_expr!(ExprKind::LiteralInt("123".into()))),
                        type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                            name: "Int".into(),
                            generics: vec![],
                        }))
                    })
                    .into(),
                    any_decl!(DeclKind::Property {
                        name: Name::Raw("height".into()),
                        is_static: true,
                        default_value: Some(any_expr!(ExprKind::LiteralInt("456".into()))),
                        type_annotation: None
                    })
                    .into(),
                ])
            })
        );
    }

    #[test]
    fn parses_static_struct_methods() {
        let parsed = parse(
            "
        struct Person {
            static func getAge() {
                123
            }
        }
        ",
        );

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::Method {
                        is_static: true,
                        func: any_decl!(DeclKind::Func(Func {
                            id: NodeID::ANY,
                            name: "getAge".into(),
                            generics: vec![],
                            params: vec![],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::LiteralInt(
                                "123".into()
                            ))]),
                            ret: None,
                            attributes: vec![]
                        }))
                        .into()
                    })
                    .into()
                ])
            })
        );
    }

    #[test]
    fn parses_instance_struct_methods() {
        let parsed = parse(
            "
        struct Person {
            func getAge() {
                123
            }
        }
        ",
        );

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::Method {
                        is_static: false,
                        func: any_decl!(DeclKind::Func(Func {
                            id: NodeID::ANY,
                            name: "getAge".into(),
                            generics: vec![],
                            params: vec![],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::LiteralInt(
                                "123".into()
                            ))]),
                            ret: None,
                            attributes: vec![]
                        }))
                        .into()
                    })
                    .into()
                ])
            })
        );
    }

    #[test]
    fn parses_init() {
        let parsed = parse(
            "
        struct Person {
            init(age: Int) {
                self.age = age
            }
        }
        ",
        );

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::Init {
                        params: vec![Parameter {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            name: Name::Raw("age".into()),
                            type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                                name: "Int".into(),
                                generics: vec![]
                            }))
                        }],
                        body: any_block!(vec![
                            any_stmt!(StmtKind::Assignment(
                                any_expr!(ExprKind::Member(
                                    Some(any_expr!(ExprKind::Variable("self".into())).into()),
                                    "age".into()
                                )),
                                any_expr!(ExprKind::Variable("age".into()))
                            ))
                            .into()
                        ]),
                    })
                    .into()
                ])
            })
        );
    }

    #[test]
    fn parses_empty_protocol_def() {
        let parsed = parse(
            "
        protocol Person {}
        ",
        );

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Protocol {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![])
            })
        );
    }

    #[test]
    fn parses_protocol_method_req() {
        let parsed = parse(
            "
        protocol Person {
            func me() -> Person
        }
        ",
        );

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Protocol {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::Method {
                        is_static: false,
                        func: any_decl!(DeclKind::FuncSignature {
                            name: "me".into(),
                            params: vec![],
                            generics: vec![],
                            ret: annotation!(TypeAnnotationKind::Nominal {
                                name: "Person".into(),
                                generics: vec![]
                            })
                            .into()
                        })
                        .into()
                    })
                    .into()
                ])
            })
        );
    }

    #[test]
    fn parses_protocol_associated_type() {
        let parsed = parse(
            "
        protocol Person {
            associated T
        }
        ",
        );

        assert_eq!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Protocol {
                name: "Person".into(),
                generics: vec![],
                conformances: vec![],
                body: any_block!(vec![
                    any_decl!(DeclKind::Associated {
                        generic: GenericDecl {
                            id: NodeID::ANY,
                            name: "T".into(),
                            generics: vec![],
                            conformances: vec![],
                            span: Span::ANY
                        }
                    })
                    .into()
                ])
            })
        );
    }

    // #[test]
    // fn handles_unclosed_paren() {
    //     let parsed = parse("func foo(");
    //     assert_eq!(parsed.diagnostics.len(), 1);
    // }

    // #[test]
    // fn handles_unclosed_brace() {
    //     let parsed = parse("func foo() {");
    //     assert_eq!(parsed.diagnostics.len(), 1);
    //     assert!(
    //         parsed.diagnostics.contains(&Diagnostic::parser(
    //             PathBuf::from("-"),
    //             (12, 12),
    //             crate::parser::ParserError::UnexpectedEndOfInput(None)
    //         )),
    //         "{:?}",
    //         parsed.diagnostics
    //     )
    // }

    // #[test]
    // fn recovers() {
    //     let parsed = parse("func foo() {\n\nfunc fizz() {}");
    //     let diagnostics = &parsed.diagnostics;
    //     assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    //     assert!(
    //         diagnostics.contains(&Diagnostic::parser(
    //             PathBuf::from("-"),
    //             (28, 28),
    //             crate::parser::ParserError::UnexpectedEndOfInput(None)
    //         )),
    //         "{diagnostics:?}"
    //     );

    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Expr::Incomplete(IncompleteExpr::Func {
    //             name: Some(Name::Raw("foo".into())),
    //             params: Some(vec![]),
    //             generics: Some(vec![]),
    //             ret: None,
    //             body: None
    //         }))
    //     );
    // }

    // #[test]
    // fn parses_protocol() {
    //     let parsed = parse(
    //         "
    //     protocol Aged<T>: X {
    //       let age: Int
    //       func getAge() -> Int
    //     }
    //     ",
    //     );

    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Expr::ProtocolDecl {
    //             name: "Aged".into(),
    //             associated_types: vec![any_expr!(TypeRepr {
    //                 name: Name::Raw("T".into()),
    //                 generics: vec![],
    //                 conformances: vec![],
    //                 introduces_type: true
    //             })],
    //             body: any_expr!(Block(vec![
    //                 any_expr!(Property {
    //                     name: Name::Raw("age".into()),
    //                     is_static: false,
    //                     type_repr: Some(
    //                         any_expr!(TypeRepr {
    //                             name: Name::Raw("Int".into()),
    //                             generics: vec![],
    //                             conformances: vec![],
    //                             introduces_type: false
    //                         })
    //                         .into()
    //                     ),
    //                     default_value: None
    //                 }),
    //                 any_expr!(FuncSignature {
    //                     name: Name::Raw("getAge".into()),
    //                     params: vec![],
    //                     generics: vec![],
    //                     ret: any_expr!(TypeRepr {
    //                         name: Name::Raw("Int".into()),
    //                         generics: vec![],
    //                         conformances: vec![],
    //                         introduces_type: false
    //                     })
    //                     .into()
    //                 })
    //             ]))
    //             .into(),
    //             conformances: vec![any_expr!(TypeRepr {
    //                 name: Name::Raw("X".into()),
    //                 generics: vec![],
    //                 conformances: vec![],
    //                 introduces_type: false
    //             })],
    //         })
    //     );
    // }

    // #[test]
    // fn parses_protocol_conformance() {
    //     let parsed = parse(
    //         "
    //     struct Person: Aged {}
    // ",
    //     );

    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Expr::Struct {
    //             name: "Person".into(),
    //             generics: vec![],
    //             conformances: vec![any_expr!(TypeRepr {
    //                 name: Name::Raw("Aged".into()),
    //                 generics: vec![],
    //                 conformances: vec![],
    //                 introduces_type: false
    //             })],
    //             body: any_expr!(Block(vec![])).into()
    //         })
    //     );
    // }

    // #[test]
    // fn parses_type_repr_conformance() {
    //     let parsed = parse(
    //         "
    //     func foo<T: Fizz>(x) -> T { x }
    // ",
    //     );

    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Expr::Func {
    //             name: Some(Name::Raw("foo".into())),
    //             generics: vec![any_expr!(TypeRepr {
    //                 name: Name::Raw("T".into()),
    //                 generics: vec![],
    //                 conformances: vec![any_expr!(TypeRepr {
    //                     name: Name::Raw("Fizz".into()),
    //                     generics: vec![],
    //                     conformances: vec![],
    //                     introduces_type: false
    //                 })],
    //                 introduces_type: true
    //             })],
    //             params: vec![any_expr!(Parameter(Name::Raw("x".into()), None))],
    //             body: any_expr!(Block(vec![any_expr!(Variable(Name::Raw("x".into())))])).into(),
    //             ret: Some(
    //                 any_expr!(TypeRepr {
    //                     name: Name::Raw("T".into()),
    //                     generics: vec![],
    //                     conformances: vec![],
    //                     introduces_type: false
    //                 })
    //                 .into()
    //             ),
    //             captures: vec![],
    //             attributes: vec![],
    //         })
    //     );
    // }

    // #[test]
    // fn parses_incomplete_member_expr() {
    //     let parsed = parse(
    //         "
    //     foo.
    //     ",
    //     );

    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Expr::Incomplete(IncompleteExpr::Member(Some(
    //             any_expr!(Variable(Name::Raw("foo".into()))).into()
    //         ))))
    //     )
    // }

    // #[test]
    // fn parses_incomplete_func_expr() {
    //     assert_eq!(
    //         parse(
    //             "
    //         func
    //         ",
    //         )
    //         .roots()[0],
    //         any_expr!(Expr::Incomplete(IncompleteExpr::Func {
    //             name: None,
    //             params: None,
    //             generics: None,
    //             ret: None,
    //             body: None
    //         }))
    //     )
    // }

    // #[test]
    // fn parses_incomplete_func_expr_with_name() {
    //     assert_eq!(
    //         parse(
    //             "
    //         func foo
    //         ",
    //         )
    //         .roots()[0],
    //         any_expr!(Expr::Incomplete(IncompleteExpr::Func {
    //             name: Some(Name::Raw("foo".into())),
    //             params: None,
    //             generics: None,
    //             ret: None,
    //             body: None
    //         }))
    //     )
    // }

    // #[test]
    // fn parses_incomplete_func_expr_with_name_and_open_paren() {
    //     assert_eq!(
    //         parse(
    //             "
    //         func foo(
    //         ",
    //         )
    //         .roots()[0],
    //         any_expr!(Expr::Incomplete(IncompleteExpr::Func {
    //             name: Some(Name::Raw("foo".into())),
    //             params: Some(vec![]),
    //             generics: None,
    //             ret: None,
    //             body: None
    //         }))
    //     )
    // }

    // #[test]
    // fn parses_incomplete_func_expr_with_name_and_open_paren_and_param() {
    //     assert_eq!(
    //         parse(
    //             "
    //         func foo(fizz
    //         ",
    //         )
    //         .roots()[0],
    //         any_expr!(Expr::Incomplete(IncompleteExpr::Func {
    //             name: Some(Name::Raw("foo".into())),
    //             params: Some(vec![any_expr!(Parameter(Name::Raw("fizz".into()), None))]),
    //             generics: None,
    //             ret: None,
    //             body: None
    //         }))
    //     )
    // }

    // #[test]
    // fn parses_incomplete_func_expr_without_body() {
    //     assert_eq!(
    //         parse(
    //             "
    //         func foo(fizz)
    //         ",
    //         )
    //         .roots()[0],
    //         any_expr!(Expr::Incomplete(IncompleteExpr::Func {
    //             name: Some(Name::Raw("foo".into())),
    //             params: Some(vec![any_expr!(Parameter(Name::Raw("fizz".into()), None))]),
    //             generics: Some(vec![]),
    //             ret: None,
    //             body: None
    //         }))
    //     )
    // }

    // #[test]
    // fn parses_incomplete_func_expr_with_incomplete_body() {
    //     assert_eq!(
    //         parse(
    //             "
    //         func foo(fizz) {
    //         ",
    //         )
    //         .roots()[0],
    //         any_expr!(Expr::Incomplete(IncompleteExpr::Func {
    //             name: Some(Name::Raw("foo".into())),
    //             params: Some(vec![any_expr!(Parameter(Name::Raw("fizz".into()), None))]),
    //             generics: Some(vec![]),
    //             ret: None,
    //             body: None
    //         }))
    //     )
    // }

    // #[test]
    // fn parses_import() {
    //     let parsed = parse(
    //         "
    //         import Foo
    //         import Bar
    //         ",
    //     );
    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Expr::Import("Foo".to_string()))
    //     );
    //     assert_eq!(
    //         parsed.roots()[1],
    //         any_expr!(Expr::Import("Bar".to_string()))
    //     );
    // }

    // #[test]
    // fn parses_func_attributes() {
    //     let parsed = parse(
    //         "
    //         @foo
    //         @bar func fizz() {}
    //         ",
    //     );

    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Expr::Func {
    //             name: Some(Name::Raw("fizz".into())),
    //             generics: vec![],
    //             params: vec![],
    //             body: any_expr!(Block(vec![])).into(),
    //             ret: None,
    //             captures: vec![],
    //             attributes: vec![
    //                 any_expr!(Expr::Attribute(Name::Raw("foo".into()))),
    //                 any_expr!(Expr::Attribute(Name::Raw("bar".into())))
    //             ],
    //         })
    //     );
    // }

    // #[test]
    // fn parses_record_literal() {
    //     let parsed = parse("{x: 1, y: 2}");
    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Expr::RecordLiteral(vec![
    //             any_expr!(Expr::RecordField {
    //                 label: Name::Raw("x".into()),
    //                 value: any_expr!(Expr::LiteralInt("1".into())).into()
    //             }),
    //             any_expr!(Expr::RecordField {
    //                 label: Name::Raw("y".into()),
    //                 value: any_expr!(Expr::LiteralInt("2".into())).into()
    //             })
    //         ]))
    //     );
    // }

    // #[test]
    // fn parses_empty_braces_as_block() {
    //     let parsed = parse("{}");
    //     assert_eq!(parsed.roots()[0], any_expr!(Expr::Block(vec![])));
    // }

    // #[test]
    // fn parses_record_literal_with_spread() {
    //     let parsed = parse("{...obj, x: 1}");
    //     assert_eq!(
    //         parsed.roots()[0],
    //         any_expr!(Expr::RecordLiteral(vec![
    //             any_expr!(Expr::Spread(
    //                 any_expr!(Expr::Variable(Name::Raw("obj".into()))).into()
    //             )),
    //             any_expr!(Expr::RecordField {
    //                 label: Name::Raw("x".into()),
    //                 value: any_expr!(Expr::LiteralInt("1".into())).into()
    //             })
    //         ]))
    //     );
    // }

    // #[test]
    // fn parses_record_type() {
    //     let parsed = parse("let x: {x: Int, y: String}");
    //     let Expr::Let(_, Some(type_expr)) = &parsed.roots()[0].expr else {
    //         panic!("Expected Let with type annotation");
    //     };
    //     assert_eq!(
    //         **type_expr,
    //         any_expr!(Expr::RecordTypeRepr {
    //             fields: vec![
    //                 any_expr!(Expr::RecordTypeField {
    //                     label: Name::Raw("x".into()),
    //                     ty: any_expr!(Expr::TypeRepr {
    //                         name: Name::Raw("Int".into()),
    //                         generics: vec![],
    //                         conformances: vec![],
    //                         introduces_type: false
    //                     })
    //                     .into()
    //                 }),
    //                 any_expr!(Expr::RecordTypeField {
    //                     label: Name::Raw("y".into()),
    //                     ty: any_expr!(Expr::TypeRepr {
    //                         name: Name::Raw("String".into()),
    //                         generics: vec![],
    //                         conformances: vec![],
    //                         introduces_type: false
    //                     })
    //                     .into()
    //                 })
    //             ],
    //             row_var: None,
    //             introduces_type: false
    //         })
    //     );
    // }

    // #[test]
    // fn parses_record_type_with_row_var() {
    //     let parsed = parse("let x: {x: Int, ..R}");
    //     let Expr::Let(_, Some(type_expr)) = &parsed.roots()[0].expr else {
    //         panic!("Expected Let with type annotation");
    //     };

    //     let Expr::RecordTypeRepr {
    //         fields, row_var, ..
    //     } = &type_expr.expr
    //     else {
    //         panic!("Expected RecordTypeRepr");
    //     };

    //     assert_eq!(fields.len(), 1);
    //     assert!(row_var.is_some());

    //     if let Some(row) = row_var {
    //         assert_eq!(**row, any_expr!(Expr::RowVariable(Name::Raw("R".into()))));
    //     }
    // }

    // #[test]
    // fn parses_struct_pattern_with_named_type() {
    //     let parsed = parse(
    //         "
    //         match point {
    //             Point { x, y } -> x,
    //         }
    //         ",
    //     );

    //     let Match(_, arms) = &parsed.roots()[0].expr else {
    //         panic!("Expected match expression");
    //     };

    //     let MatchArm(pattern_expr, _) = &arms[0].expr else {
    //         panic!("Expected match arm");
    //     };

    //     let ParsedPattern(pattern) = &pattern_expr.expr else {
    //         panic!("Expected parsed pattern");
    //     };

    //     match pattern {
    //         Pattern::Struct {
    //             struct_name,
    //             fields,
    //             field_names,
    //             rest,
    //         } => {
    //             assert_eq!(struct_name, &Some(Name::Raw("Point".into())));
    //             assert_eq!(fields.len(), 2);
    //             assert_eq!(field_names.len(), 2);
    //             assert!(!(*rest));

    //             // Check field patterns
    //             assert_eq!(&field_names[0], &Name::Raw("x".into()));
    //             let ParsedPattern(Pattern::Bind(bind_name)) = &fields[0].expr else {
    //                 panic!("Expected bind pattern for field x");
    //             };
    //             assert_eq!(bind_name, &Name::Raw("x".into()));

    //             assert_eq!(&field_names[1], &Name::Raw("y".into()));
    //             let ParsedPattern(Pattern::Bind(bind_name)) = &fields[1].expr else {
    //                 panic!("Expected bind pattern for field y");
    //             };
    //             assert_eq!(bind_name, &Name::Raw("y".into()));
    //         }
    //         _ => panic!("Expected struct pattern"),
    //     }
    // }

    // #[test]
    // fn parses_struct_pattern_with_explicit_bindings() {
    //     let parsed = parse(
    //         "
    //         match point {
    //             Point { x: px, y: py } -> px,
    //         }
    //         ",
    //     );

    //     let Match(_, arms) = &parsed.roots()[0].expr else {
    //         panic!("Expected match expression");
    //     };

    //     let MatchArm(pattern_expr, _) = &arms[0].expr else {
    //         panic!("Expected match arm");
    //     };

    //     let ParsedPattern(pattern) = &pattern_expr.expr else {
    //         panic!("Expected parsed pattern");
    //     };

    //     match pattern {
    //         Pattern::Struct {
    //             struct_name,
    //             fields,
    //             field_names,
    //             rest,
    //         } => {
    //             assert_eq!(struct_name, &Some(Name::Raw("Point".into())));
    //             assert_eq!(fields.len(), 2);
    //             assert_eq!(field_names.len(), 2);
    //             assert!(!(*rest));

    //             // Check field patterns with explicit bindings
    //             assert_eq!(&field_names[0], &Name::Raw("x".into()));
    //             let ParsedPattern(Pattern::Bind(bind_name)) = &fields[0].expr else {
    //                 panic!("Expected bind pattern for field x");
    //             };
    //             assert_eq!(bind_name, &Name::Raw("px".into()));

    //             assert_eq!(&field_names[1], &Name::Raw("y".into()));
    //             let ParsedPattern(Pattern::Bind(bind_name)) = &fields[1].expr else {
    //                 panic!("Expected bind pattern for field y");
    //             };
    //             assert_eq!(bind_name, &Name::Raw("py".into()));
    //         }
    //         _ => panic!("Expected struct pattern"),
    //     }
    // }

    // #[test]
    // fn parses_struct_pattern_with_rest() {
    //     let parsed = parse(
    //         "
    //         match person {
    //             Person { name, .. } -> name
    //         }
    //         ",
    //     );

    //     let Match(_, arms) = &parsed.roots()[0].expr else {
    //         panic!("Expected match expression");
    //     };

    //     let MatchArm(pattern_expr, _) = &arms[0].expr else {
    //         panic!("Expected match arm");
    //     };

    //     let ParsedPattern(pattern) = &pattern_expr.expr else {
    //         panic!("Expected parsed pattern");
    //     };

    //     match pattern {
    //         Pattern::Struct {
    //             struct_name,
    //             fields,
    //             field_names,
    //             rest,
    //         } => {
    //             assert_eq!(struct_name, &Some(Name::Raw("Person".into())));
    //             assert_eq!(fields.len(), 1);
    //             assert_eq!(field_names.len(), 1);
    //             assert!(*rest);

    //             assert_eq!(&field_names[0], &Name::Raw("name".into()));
    //             let ParsedPattern(Pattern::Bind(bind_name)) = &fields[0].expr else {
    //                 panic!("Expected bind pattern for field name");
    //             };
    //             assert_eq!(bind_name, &Name::Raw("name".into()));
    //         }
    //         _ => panic!("Expected struct pattern"),
    //     }
    // }

    // #[test]
    // fn parses_unqualified_struct_pattern() {
    //     let parsed = parse(
    //         "
    //         match value {
    //             { x, y } -> x,
    //         }
    //         ",
    //     );

    //     let Match(_, arms) = &parsed.roots()[0].expr else {
    //         panic!("Expected match expression");
    //     };

    //     let MatchArm(pattern_expr, _) = &arms[0].expr else {
    //         panic!("Expected match arm");
    //     };

    //     let ParsedPattern(pattern) = &pattern_expr.expr else {
    //         panic!("Expected parsed pattern");
    //     };

    //     match pattern {
    //         Pattern::Struct {
    //             struct_name,
    //             fields,
    //             field_names,
    //             rest,
    //         } => {
    //             assert_eq!(struct_name, &None);
    //             assert_eq!(fields.len(), 2);
    //             assert_eq!(field_names.len(), 2);
    //             assert!(!*rest);
    //         }
    //         _ => panic!("Expected struct pattern"),
    //     }
    // }

    // #[test]
    // fn parses_struct_pattern_with_nested_patterns() {
    //     let parsed = parse(
    //         "
    //         match rect {
    //             Rectangle { topLeft: Point { x: 0, y: 0 }, bottomRight } -> bottomRight
    //         }
    //         ",
    //     );

    //     let Match(_, arms) = &parsed.roots()[0].expr else {
    //         panic!("Expected match expression");
    //     };

    //     let MatchArm(pattern_expr, _) = &arms[0].expr else {
    //         panic!("Expected match arm");
    //     };

    //     let ParsedPattern(pattern) = &pattern_expr.expr else {
    //         panic!("Expected parsed pattern");
    //     };

    //     match pattern {
    //         Pattern::Struct {
    //             struct_name,
    //             fields,
    //             field_names,
    //             rest,
    //         } => {
    //             assert_eq!(struct_name, &Some(Name::Raw("Rectangle".into())));
    //             assert_eq!(fields.len(), 2);
    //             assert_eq!(field_names.len(), 2);
    //             assert!(!*rest);

    //             // Check nested pattern
    //             assert_eq!(&field_names[0], &Name::Raw("topLeft".into()));

    //             let ParsedPattern(nested_pattern) = &fields[0].expr else {
    //                 panic!("Expected parsed pattern for topLeft");
    //             };

    //             match nested_pattern {
    //                 Pattern::Struct {
    //                     struct_name: nested_struct_name,
    //                     fields: nested_fields,
    //                     field_names: nested_field_names,
    //                     ..
    //                 } => {
    //                     assert_eq!(nested_struct_name, &Some(Name::Raw("Point".into())));
    //                     assert_eq!(nested_fields.len(), 2);
    //                     assert_eq!(nested_field_names.len(), 2);
    //                 }
    //                 _ => panic!("Expected nested struct pattern"),
    //             }
    //         }
    //         _ => panic!("Expected struct pattern"),
    //     }
    // }

    // #[test]
    // fn test_member_access_parsing() {
    //     // Test simple member access
    //     let source = "x.0";
    //     let parsed = parse(source);

    //     for (i, root) in parsed.roots().iter().enumerate() {
    //         println!("Root {}: {:?}", i, root.expr);
    //     }

    //     assert_eq!(
    //         parsed.roots().len(),
    //         1,
    //         "Should have exactly one root expression"
    //     );

    //     // Check that the root is a member access expression
    //     match &parsed.roots()[0].expr {
    //         Expr::Member(Some(lhs), label) => {
    //             println!("Member access found: lhs={:?}, label={:?}", lhs.expr, label);
    //         }
    //         expr => {
    //             panic!("Expected Member expression, got: {expr:?}");
    //         }
    //     }
    // }

    // #[test]
    // fn test_tuple_member_access() {
    //     // Test tuple with member access
    //     let source = "(1, 2).0";
    //     let parsed = parse(source);

    //     println!("Number of roots: {}", parsed.roots().len());
    //     for (i, root) in parsed.roots().iter().enumerate() {
    //         println!("Root {}: {:?}", i, root.expr);
    //     }

    //     assert_eq!(
    //         parsed.roots().len(),
    //         1,
    //         "Should have exactly one root expression"
    //     );
    // }

    // #[test]
    // fn test_multiple_expressions_with_member_access() {
    //     // Test multiple expressions, one with member access
    //     let source = "let x = (1, 2)\nx.0";
    //     let parsed = parse(source);

    //     println!("Number of roots: {}", parsed.roots().len());
    //     for (i, root) in parsed.roots().iter().enumerate() {
    //         println!("Root {}: {:?}", i, root.expr);
    //     }

    //     // This should have 2 roots: the let expression and the member access
    //     assert_eq!(
    //         parsed.roots().len(),
    //         2,
    //         "Should have exactly two root expressions"
    //     );
    // }

    // #[test]
    // fn test_chained_member_access() {
    //     // Test chained member access
    //     let source = "x.y.z";
    //     let parsed = parse(source);

    //     println!("Number of roots: {}", parsed.roots().len());
    //     for (i, root) in parsed.roots().iter().enumerate() {
    //         println!("Root {}: {:?}", i, root.expr);
    //     }

    //     assert_eq!(
    //         parsed.roots().len(),
    //         1,
    //         "Should have exactly one root expression"
    //     );
    // }
}
