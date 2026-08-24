    use talk::any_block;
    use talk::any_body;
    use talk::any_expr;
    use crate::any_decl;
    use crate::parser_tests::tests::parse;
    use talk_front::desugar::lower_funcs_to_lets::LowerFuncsToLets;
    use talk_front::name::Name;
    use talk_front::node_id::FileID;
    use talk_front::node_id::NodeID;
    use talk_front::node_kinds::decl::DeclKind;
    use talk_front::node_kinds::decl::ReceiverMode;
    use talk_front::node_kinds::expr::ExprKind;
    use talk_front::node_kinds::func::Func;
    use talk_front::node_kinds::func::FuncOrigin;
    use talk_front::node_kinds::pattern::Pattern;
    use talk_front::node_kinds::pattern::PatternKind;
    use talk_front::span::Span;

    #[test]
    fn lowers_func_decl() {
        let mut parsed = parse(
            "
        func fizz() {}
        ",
        );

        LowerFuncsToLets::run(&mut parsed);

        crate::fixture_eq_args!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID(FileID(0), 5),
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Raw("fizz".into()))
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    origin: FuncOrigin::Decl,
                    id: NodeID::ANY,
                    name: Name::Raw("fizz".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    captures: vec![],
                    where_clause: None,
                    params: vec![],
                    body: any_block!(vec![]),
                    effects: Default::default(),
                    ret: None,
                    attributes: vec![]
                })))
            })
        )
    }

    #[test]
    fn preserves_named_callable_origin() {
        // ADR 0041: a lowered `func` decl stays a named callable; a `let`
        // whose value is a closure never becomes one.
        let mut parsed = parse(
            "
        func fizz(x) {}
        let buzz = func named(y) {}
        ",
        );

        LowerFuncsToLets::run(&mut parsed);

        for (index, expected) in [(0, FuncOrigin::Decl), (1, FuncOrigin::Expr)] {
            let DeclKind::Let { rhs: Some(rhs), .. } = &parsed.roots[index].as_decl().kind else {
                panic!("expected let, got {:?}", parsed.roots[index]);
            };
            let ExprKind::Func(func) = &rhs.kind else {
                panic!("expected func rhs");
            };
            assert_eq!(func.origin, expected);
        }
    }

    #[test]
    fn ignores_methods() {
        let mut parsed = parse(
            "
            struct Person { func fizz() {} }
        ",
        );

        LowerFuncsToLets::run(&mut parsed);

        crate::fixture_eq_args!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                linear: false,
                heap: false,
                name: "Person".into(),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![any_decl!(DeclKind::Method {
                    func: Box::new(Func {
                        origin: FuncOrigin::Decl,
                        id: NodeID::ANY,
                        name: "fizz".into(),
                        name_span: Span::ANY,
                        generics: vec![],
                        captures: vec![],
                        where_clause: None,
                        params: vec![],
                        body: any_block!(vec![]),
                        effects: Default::default(),
                        ret: None,
                        attributes: vec![]
                    }),
                    is_static: false,
                    receiver_mode: ReceiverMode::None
                })])
            })
        )
    }
