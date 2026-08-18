    use talk_front::desugar::lower_trailing_blocks::LowerTrailingBlocks;
    use talk_front::node_kinds::call_arg::{CallArg, CallArgOrigin};
    use talk_front::node_kinds::expr::{Expr, ExprKind};
    use talk_front::node_kinds::func::FuncOrigin;

    #[test]
    fn trailing_blocks_become_anonymous_func_arguments() {
        let (mut ast, _) = talk::compiling::frontend::parse_ast(
            "foo(1) { x in x }\nbar { $0 }\nbaz {}\n'foo(1) { x in x }\n'bar { $0 }\n",
            talk_front::node_id::FileID(0),
            "-",
        )
        .expect("parse");
        LowerTrailingBlocks::run(&mut ast);

        let mut calls = 0;
        for root in &ast.roots {
            let talk_front::node::Node::Stmt(stmt) = root else {
                panic!("expected statements, got {root:?}");
            };
            let talk_front::node_kinds::stmt::StmtKind::Expr(expr) = &stmt.kind else {
                panic!("expected expression statements");
            };
            let (args, trailing_block) = match &expr.kind {
                ExprKind::Call {
                    args,
                    trailing_block,
                    ..
                }
                | ExprKind::CallEffect {
                    args,
                    trailing_block,
                    ..
                } => (args, trailing_block),
                _ => panic!("expected calls or effect performs"),
            };
            assert!(trailing_block.is_none(), "trailing block must desugar");
            let Some(CallArg {
                origin,
                value:
                    Expr {
                        kind: ExprKind::Func(func),
                        ..
                    },
                ..
            }) = args.last()
            else {
                panic!("expected a trailing func argument");
            };
            // ADR 0041: the label exception keys off this origin, never the
            // synthesized function name or span.
            assert_eq!(*origin, CallArgOrigin::TrailingBlock);
            assert_eq!(func.origin, FuncOrigin::Expr);
            for arg in &args[..args.len() - 1] {
                assert_eq!(arg.origin, CallArgOrigin::Written);
            }
            calls += 1;
            match calls {
                // `{ x in x }` carries its named parameter.
                1 | 4 => assert_eq!(func.params[0].name.name_str(), "x"),
                // `{ $0 }` carries the parser-synthesized positional.
                2 | 5 => assert_eq!(func.params[0].name.name_str(), "$0"),
                // `{}` is a zero-parameter closure.
                _ => assert!(func.params.is_empty()),
            }
        }
        assert_eq!(calls, 5);
    }
