    use crate::parser_tests::tests::parse;
    use talk_front::desugar::lower_if_to_match::LowerIfToMatch;
    use talk_front::node_kinds::expr::ExprKind;
    use talk_front::node_kinds::pattern::PatternKind;

    #[test]
    fn desugars_if_expression_to_match() {
        let mut parsed = parse("let x = if 1 < 2 { 1 } else { 2 }");
        LowerIfToMatch::run(&mut parsed);

        let decl = parsed.roots[0].as_decl();
        let talk_front::node_kinds::decl::DeclKind::Let { rhs: Some(rhs), .. } = &decl.kind else {
            panic!("expected a let binding");
        };
        let ExprKind::Match(_, arms) = &rhs.kind else {
            panic!(
                "expected the if expression to lower to a match, got {:?}",
                rhs.kind
            );
        };
        assert_eq!(arms.len(), 2);
        assert!(matches!(arms[0].pattern.kind, PatternKind::LiteralTrue));
        assert!(matches!(arms[1].pattern.kind, PatternKind::LiteralFalse));
    }

    #[test]
    fn leaves_statement_if_alone() {
        // Only expression-`if` collapses. A statement-`if` in a branch keeps its
        // own (non-unifying, divergence-aware) form; the parser distinguishes the
        // two, so the outer expression-`if` becomes a `match` while the inner
        // statement-`if` stays a `StmtKind::If`.
        let mut parsed = parse("let x = if 1 < 2 { if 3 < 4 { 5 } else { 6 } } else { 7 }");
        LowerIfToMatch::run(&mut parsed);

        let decl = parsed.roots[0].as_decl();
        let talk_front::node_kinds::decl::DeclKind::Let { rhs: Some(rhs), .. } = &decl.kind else {
            panic!("expected a let binding");
        };
        let ExprKind::Match(_, arms) = &rhs.kind else {
            panic!("expected the outer if expression to lower to a match");
        };
        let talk_front::node::Node::Stmt(stmt) = arms[0].body.body.last().expect("non-empty then block")
        else {
            panic!("expected the then block to hold a statement");
        };
        assert!(
            matches!(stmt.kind, talk_front::node_kinds::stmt::StmtKind::If(..)),
            "expected the nested statement-if to be left alone, got {:?}",
            stmt.kind
        );
    }
