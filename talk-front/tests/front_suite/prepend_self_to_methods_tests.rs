    use talk::any_block;
    use talk::any_body;
    use crate::annotation;
    use crate::any_decl;
    use crate::parser_tests::tests::parse;
    use talk_front::desugar::prepend_self_to_methods::PrependSelfToMethods;
    use talk_front::node_id::NodeID;
    use talk_front::node_kinds::decl::DeclKind;
    use talk_front::node_kinds::decl::ReceiverMode;
    use talk_front::node_kinds::func::Func;
    use talk_front::node_kinds::func::FuncOrigin;
    use talk_front::node_kinds::parameter::Parameter;
    use talk_front::node_kinds::type_annotation::TypeAnnotationKind;
    use talk_front::span::Span;

    #[test]
    fn prepends_self_to_methods() {
        let mut parsed = parse(
            "
        struct Person {
          func fizz(x) {
          }
        }
        ",
        );

        PrependSelfToMethods::run(&mut parsed);

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
                        effects: Default::default(),
                        params: vec![
                            Parameter {
                                label: None,
                                label_span: None,
                                mode: None,
                                mode_span: None,
                                id: NodeID::ANY,
                                span: Span::ANY,
                                name: "self".into(),
                                name_span: Span::ANY,
                                type_annotation: Some(annotation!(TypeAnnotationKind::Borrow {
                                    mutable: false,
                                    inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                        "Self".into()
                                    )))
                                }))
                            },
                            Parameter {
                                label: None,
                                label_span: None,
                                mode: None,
                                mode_span: None,
                                id: NodeID::ANY,
                                span: Span::ANY,
                                name: "x".into(),
                                name_span: Span::ANY,
                                type_annotation: None
                            }
                        ],
                        body: any_block!(vec![]),
                        ret: None,
                        attributes: vec![]
                    }),
                    is_static: false,
                    receiver_mode: ReceiverMode::None
                })])
            })
        )
    }

    #[test]
    fn prepends_mutable_self_to_mut_methods() {
        let mut parsed = parse(
            "
        struct Person {
          mut func fizz(x) {
          }
        }
        ",
        );

        PrependSelfToMethods::run(&mut parsed);

        let DeclKind::Struct { body, .. } = &parsed.roots[0].as_decl().kind else {
            panic!("expected struct");
        };
        let DeclKind::Method { func, .. } = &body.decls[0].kind else {
            panic!("expected method");
        };
        crate::fixture_eq_args!(
            func.params[0].type_annotation.clone().unwrap().kind,
            TypeAnnotationKind::Borrow {
                mutable: true,
                inner: Box::new(annotation!(TypeAnnotationKind::SelfType("Self".into())))
            }
        );
    }

    #[test]
    fn init_requirements_get_self_return_and_no_receiver() {
        let mut parsed = parse(
            "
        protocol FromPair {
            init(lower: Int, upper: Int)
        }
        ",
        );

        PrependSelfToMethods::run(&mut parsed);

        let DeclKind::Protocol { body, .. } = &parsed.roots[0].as_decl().kind else {
            panic!("expected protocol");
        };
        let DeclKind::InitRequirement { signature } = &body.decls[0].kind else {
            panic!("expected init requirement");
        };
        assert_eq!(signature.params.len(), 2, "no self receiver is prepended");
        assert_eq!(
            signature.ret.as_ref().unwrap().kind,
            TypeAnnotationKind::SelfType("Self".into())
        );
    }

    #[test]
    fn prepends_self_to_inits() {
        let mut parsed = parse(
            "
        struct Person {
            init() {}
        }
        ",
        );

        PrependSelfToMethods::run(&mut parsed);

        crate::fixture_eq_args!(
            *parsed.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                linear: false,
                heap: false,
                name: "Person".into(),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![any_decl!(DeclKind::Init {
                    name: "init".into(),
                    params: vec![Parameter {
                        label: None,
                        label_span: None,
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: "self".into(),
                        name_span: Span::ANY,
                        type_annotation: Some(annotation!(TypeAnnotationKind::SelfType(
                            "Self".into()
                        )))
                    },],
                    body: any_block!(vec![]),
                })])
            })
        )
    }
