    use talk::any_expr;
    use crate::any_stmt;
    use crate::invocation;
    use crate::parser_tests::tests::parse;
    use talk_front::desugar::lower_operators::LowerOperators;
    use talk_front::label::Label;
    use talk_front::node_id::NodeID;
    use talk_front::node_kinds::call_arg::CallArg;
    use talk_front::node_kinds::call_arg::CallArgOrigin;
    use talk_front::node_kinds::expr::ExprKind;
    use talk_front::node_kinds::stmt::StmtKind;
    use talk_front::span::Span;

    #[test]
    fn folds_negative_integer_literals_before_operator_lowering() {
        let mut parsed = parse("-9_223_372_036_854_775_808");
        LowerOperators::run(&mut parsed);

        crate::fixture_eq_args!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(any_expr!(ExprKind::LiteralInt(
                "-9_223_372_036_854_775_808".into()
            ))))
        )
    }

    #[test]
    fn lowers_plus() {
        let mut parsed = parse("1 + 2");
        LowerOperators::run(&mut parsed);

        crate::fixture_eq_args!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(invocation!(
                ExprKind::Variable("Add".into()),
                "add",
                vec![
                    CallArg {
                        origin: CallArgOrigin::Synthesized,
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        origin: CallArgOrigin::Synthesized,
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(1),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("2".into())),
                        span: Span::ANY,
                    }
                ]
            )))
        )
    }

    #[test]
    fn lowers_minus() {
        let mut parsed = parse("1 - 2");
        LowerOperators::run(&mut parsed);

        crate::fixture_eq_args!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(invocation!(
                ExprKind::Variable("Subtract".into()),
                "minus",
                vec![
                    CallArg {
                        origin: CallArgOrigin::Synthesized,
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        origin: CallArgOrigin::Synthesized,
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(1),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("2".into())),
                        span: Span::ANY,
                    }
                ]
            )))
        )
    }

    #[test]
    fn lowers_times() {
        let mut parsed = parse("1 * 2");
        LowerOperators::run(&mut parsed);

        crate::fixture_eq_args!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(invocation!(
                ExprKind::Variable("Multiply".into()),
                "multiply",
                vec![
                    CallArg {
                        origin: CallArgOrigin::Synthesized,
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        origin: CallArgOrigin::Synthesized,
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(1),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("2".into())),
                        span: Span::ANY,
                    }
                ]
            )))
        )
    }

    #[test]
    fn lowers_divide() {
        let mut parsed = parse("1 / 2");
        LowerOperators::run(&mut parsed);

        crate::fixture_eq_args!(
            *parsed.roots[0].as_stmt(),
            any_stmt!(StmtKind::Expr(invocation!(
                ExprKind::Variable("Divide".into()),
                "divide",
                vec![
                    CallArg {
                        origin: CallArgOrigin::Synthesized,
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(0),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("1".into())),
                        span: Span::ANY,
                    },
                    CallArg {
                        origin: CallArgOrigin::Synthesized,
                        mode: None,
                        mode_span: None,
                        id: NodeID::ANY,
                        label: Label::Positional(1),
                        label_span: Span::ANY,
                        value: any_expr!(ExprKind::LiteralInt("2".into())),
                        span: Span::ANY,
                    }
                ]
            )))
        )
    }

    fn assert_lowers_range_literal(source: &'static str, expected_type: &str) {
        let mut parsed = parse(source);
        LowerOperators::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call, got {:?}", expr.kind);
        };
        let ExprKind::Variable(range_type) = &callee.kind else {
            panic!("expected range constructor callee, got {:?}", callee.kind);
        };

        assert_eq!(range_type.name_str(), expected_type);
        assert_eq!(args.len(), 2);
        assert_eq!(args[0].label, Label::Named("lower".into()));
        assert_eq!(args[1].label, Label::Named("upper".into()));
    }

    #[test]
    fn lowers_inclusive_range_literal() {
        assert_lowers_range_literal("1..3", "ClosedRange");
    }

    #[test]
    fn lowers_half_open_range_literal() {
        assert_lowers_range_literal("1..<3", "Range");
    }

    #[test]
    fn range_binds_tighter_than_equality_looser_than_addition() {
        let mut parsed = parse("0..n - 1 == r");
        LowerOperators::run(&mut parsed);

        // `(0..(n - 1)) == r`: the equality callee receives the range
        // construction as its first argument.
        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call, got {:?}", expr.kind);
        };
        let ExprKind::Member(Some(receiver), Label::Named(method), _) = &callee.kind else {
            panic!("expected equality callee, got {:?}", callee.kind);
        };
        assert!(
            matches!(&receiver.kind, ExprKind::Variable(name) if name.name_str() == "Equatable")
        );
        assert_eq!(method, "equals");
        let ExprKind::Call { callee, .. } = &args[0].value.kind else {
            panic!(
                "expected range construction lhs, got {:?}",
                args[0].value.kind
            );
        };
        assert!(
            matches!(&callee.kind, ExprKind::Variable(name) if name.name_str() == "ClosedRange")
        );
    }

    fn assert_lowers_binary(source: &'static str, expected_protocol: &str, expected_method: &str) {
        let mut parsed = parse(source);
        LowerOperators::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call, got {:?}", expr.kind);
        };
        let ExprKind::Member(Some(receiver), Label::Named(method), _) = &callee.kind else {
            panic!("expected protocol method callee, got {:?}", callee.kind);
        };
        let ExprKind::Variable(protocol) = &receiver.kind else {
            panic!("expected protocol receiver, got {:?}", receiver.kind);
        };

        assert_eq!(protocol.name_str(), expected_protocol);
        assert_eq!(method, expected_method);
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn lowers_bitwise_binary_operators() {
        for (source, protocol, method) in [
            ("1 & 2", "BitwiseAnd", "bitAnd"),
            ("1 | 2", "BitwiseOr", "bitOr"),
            ("1 ^ 2", "BitwiseXor", "bitXor"),
            ("1 << 2", "ShiftLeft", "shiftLeft"),
            ("1 >> 2", "ShiftRight", "shiftRight"),
        ] {
            assert_lowers_binary(source, protocol, method);
        }
    }

    #[test]
    fn lowers_bitwise_complement() {
        let mut parsed = parse("~1");
        LowerOperators::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected call, got {:?}", expr.kind);
        };
        let ExprKind::Member(Some(receiver), Label::Named(method), _) = &callee.kind else {
            panic!("expected complement method callee, got {:?}", callee.kind);
        };

        assert_eq!(method, "complement");
        assert!(matches!(receiver.kind, ExprKind::LiteralInt(_)));
        assert!(args.is_empty());
    }
