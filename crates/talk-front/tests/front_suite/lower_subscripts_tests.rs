    use crate::parser_tests::tests::parse;
    use talk_front::desugar::lower_subscripts::LowerSubscripts;
    use talk_front::node_kinds::expr::ExprKind;
    use talk_front::node_kinds::stmt::StmtKind;

    #[test]
    fn lowers_read_subscript_to_protocol_call() {
        let mut parsed = parse("a[1]");
        LowerSubscripts::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call");
        };
        let ExprKind::Member(Some(protocol), label, _) = &callee.kind else {
            panic!("expected protocol member");
        };
        assert!(
            matches!(protocol.kind, ExprKind::Variable(ref name) if name.name_str() == "SubscriptRead")
        );
        assert_eq!(label.to_string(), "subscript_read");
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn lowers_write_subscript_to_protocol_call() {
        let mut parsed = parse("a[1] = 123");
        LowerSubscripts::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call");
        };
        let ExprKind::Member(Some(protocol), label, _) = &callee.kind else {
            panic!("expected protocol member");
        };
        assert!(
            matches!(protocol.kind, ExprKind::Variable(ref name) if name.name_str() == "SubscriptWrite")
        );
        assert_eq!(label.to_string(), "subscript_write");
        assert_eq!(args.len(), 3);
    }
