    use talk_front::node::Node;
    use talk_front::node_kinds::decl::Decl;
    use talk_front::node_kinds::decl::DeclKind;
    use talk_front::node_kinds::parameter::ParamMode;

    #[test]
    fn stamps_extension_method_params() {
        let mut ast = crate::parser_tests::tests::parse(
            "struct Wrap {}\nextend Wrap {\n\tfunc poke(t: Token) -> Int { 0 }\n}",
        );
        talk_front::desugar::desugar(std::slice::from_mut(&mut ast));
        let Node::Decl(Decl {
            kind: DeclKind::Extend { body, .. },
            ..
        }) = &ast.roots[1]
        else {
            panic!("expected extend, got {:?}", ast.roots[1]);
        };
        let Decl {
            kind: DeclKind::Method { func, .. },
            ..
        } = &body.decls[0]
        else {
            panic!("expected method, got {:?}", body.decls[0]);
        };
        // params[0] is the prepended self; the user param follows.
        assert_eq!(func.params[1].mode, Some(ParamMode::Borrow));
    }

    #[test]
    fn stamps_init_requirement_params_consume() {
        let mut ast = crate::parser_tests::tests::parse(
            "protocol FromPair {\n\tinit(lower: Int, upper: Int)\n}",
        );
        talk_front::desugar::desugar(std::slice::from_mut(&mut ast));
        let Node::Decl(Decl {
            kind: DeclKind::Protocol { body, .. },
            ..
        }) = &ast.roots[0]
        else {
            panic!("expected protocol, got {:?}", ast.roots[0]);
        };
        let Decl {
            kind: DeclKind::InitRequirement { signature },
            ..
        } = &body.decls[0]
        else {
            panic!("expected init requirement, got {:?}", body.decls[0]);
        };
        assert_eq!(signature.params[0].mode, Some(ParamMode::Consume));
        assert_eq!(signature.params[1].mode, Some(ParamMode::Consume));
    }
