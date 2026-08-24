    use crate::parser_tests::tests::parse;
    use talk_front::desugar::lower_unreachable::LowerUnreachable;
    use talk_front::node_kinds::expr::ExprKind;
    use talk_front::node_kinds::stmt::StmtKind;

    #[test]
    fn lowers_to_the_panic_effect() {
        let mut parsed = parse("unreachable");
        LowerUnreachable::run(&mut parsed);

        let StmtKind::Expr(expr) = &parsed.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::CallEffect {
            effect_name, args, ..
        } = &expr.kind
        else {
            panic!("expected panic perform");
        };
        assert_eq!(effect_name.name_str(), "panic");
        assert!(matches!(
            args.as_slice(),
            [arg] if matches!(arg.value.kind, ExprKind::LiteralString(ref message) if message == "reached unreachable")
        ));
    }
