    use std::collections::HashMap;

    use derive_visitor::Drive;

    use crate::parser_tests::tests::parse;
    use talk_front::macro_expansion::MacroError;
    use talk_front::macro_expansion::expand_macros_with_sources;
    use talk_front::node::Node;
    use talk_front::node_id::FileID;
    use talk_front::node_kinds::decl::Decl;
    use talk_front::node_kinds::decl::DeclKind;
    use talk_front::node_kinds::expr::ExprKind;
    use talk_front::node_kinds::stmt::StmtKind;

    #[test]
    fn parser_captures_non_talk_macro_token_trees() {
        let ast = parse("let page = @html { div class=@card { <not talk> } }");
        let Node::Decl(decl) = &ast.roots[0] else {
            panic!("expected a let declaration");
        };
        let DeclKind::Let {
            rhs: Some(expr), ..
        } = &decl.kind
        else {
            panic!("expected a let with a value");
        };
        let ExprKind::MacroCall {
            name,
            input_span,
            args,
            ..
        } = &expr.kind
        else {
            panic!("expected macro call");
        };
        assert_eq!(name, "html");
        assert_eq!(
            &"let page = @html { div class=@card { <not talk> } }"
                [input_span.start as usize..input_span.end as usize],
            "{ div class=@card { <not talk> } }"
        );
        assert!(args.is_empty());
    }

    #[test]
    fn parser_captures_item_position_macro_invocations() {
        let ast = parse("@html { div class=@card { <not talk> } }");
        let Node::Decl(decl) = &ast.roots[0] else {
            panic!("expected an item-position macro invocation");
        };
        let DeclKind::MacroCall {
            name, input_span, ..
        } = &decl.kind
        else {
            panic!("expected a declaration macro call");
        };
        assert_eq!(name, "html");
        assert_eq!(
            &"@html { div class=@card { <not talk> } }"
                [input_span.start as usize..input_span.end as usize],
            "{ div class=@card { <not talk> } }"
        );
    }

    #[test]
    fn parser_captures_wrapper_markers_with_nesting() {
        let source = "#[outer]\n#[logged(level: \"debug\")]\npub func loud() -> Int { 1 }";
        let ast = parse(source);
        let Node::Decl(decl) = &ast.roots[0] else {
            panic!("expected a wrapper declaration");
        };
        let DeclKind::Wrapper {
            name,
            input_tokens,
            target_tokens,
            target,
            ..
        } = &decl.kind
        else {
            panic!("expected the outer wrapper");
        };
        assert_eq!(name, "outer");
        assert!(input_tokens.is_empty(), "the bare form captures no tokens");
        assert!(!target_tokens.is_empty());
        let DeclKind::Wrapper {
            name: inner_name,
            input_span,
            input_tokens: inner_tokens,
            target: inner_target,
            ..
        } = &target.kind
        else {
            panic!("expected the inner wrapper");
        };
        assert_eq!(inner_name, "logged");
        assert_eq!(
            &source[input_span.start as usize..input_span.end as usize],
            "(level: \"debug\")"
        );
        assert!(!inner_tokens.is_empty());
        let DeclKind::Func(func) = &inner_target.kind else {
            panic!("expected the wrapped function");
        };
        assert_eq!(
            inner_target.visibility,
            talk_front::node_kinds::decl::Visibility::Public,
            "the target keeps its own visibility"
        );
        assert_eq!(func.name.name_str(), "loud");
    }

    #[test]
    fn wrappers_reject_imports_and_macro_definitions_as_targets() {
        let error =
            talk::compiling::frontend::parse_ast("#[w]\nuse foo::{ bar }", FileID(0), "-")
                .expect_err("a wrapped import must fail to parse");
        assert!(error.to_string().contains("import"), "{error}");
        let error =
            talk::compiling::frontend::parse_ast("#[w]\nmacro m($x) { $x }", FileID(0), "-")
                .expect_err("a wrapped macro definition must fail to parse");
        assert!(error.to_string().contains("macro definition"), "{error}");
    }

    #[test]
    fn visibility_before_a_wrapper_marker_is_rejected() {
        let error =
            talk::compiling::frontend::parse_ast("pub #[x] func f() -> Int { 1 }", FileID(0), "-")
                .expect_err("`pub` before a marker must fail to parse");
        let rendered = error.to_string();
        assert!(rendered.contains("wrapper marker first"), "{rendered}");
    }

    #[test]
    fn parser_captures_expression_quote_tokens_and_splices() {
        let ast = parse("quote { helper(value: $item) }");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::SyntaxQuote {
            tokens, splices, ..
        } = &expr.kind
        else {
            panic!("expected syntax quote");
        };
        assert_eq!(splices, &["item"]);
        assert_eq!(tokens.first().map(|token| token.span_start), Some(6));
        assert_eq!(tokens.last().map(|token| token.span_end), Some(30));
    }

    #[test]
    fn assert_expands_with_the_asserted_source_text() {
        let source = "@assert(left == \"right\")";
        let mut ast = parse(source);
        let invocation_id = ast.roots[0].node_id();
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");

        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected assertion function call");
        };
        assert_ne!(expr.id, invocation_id);
        assert!(matches!(
            &callee.kind,
            ExprKind::Variable(talk_front::name::Name::Raw(name))
                if name == "testing::assert_message"
        ));
        assert!(matches!(
            &args[1].value.kind,
            ExprKind::LiteralString(message)
                if message == "assertion failed: left == \\\"right\\\""
        ));
    }

    #[test]
    fn expands_expression_template_and_removes_definition() {
        let source = "macro choose($condition, $yes, $no) { if $condition { $yes } else { $no } }\n@choose(true, 1, 2)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(ast.roots.len(), 1);
        let StmtKind::If(..) = &ast.roots[0].as_stmt().kind else {
            panic!("expected an if statement, got {:?}", ast.roots[0]);
        };
    }

    #[test]
    fn expanded_nodes_carry_the_invocation_span() {
        // Expansion parses a virtual source; the resulting nodes must not
        // keep spans into it, or diagnostics render at unrelated offsets in
        // the real file. Every expanded node borrows the invocation span.
        let source = "macro choose($condition, $yes, $no) { if $condition { $yes } else { $no } }\n@choose(true, 1, 2)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let invocation_span = talk_front::parsing::span::Span {
            file_id: ast.file_id,
            start: source.find("@choose").unwrap() as u32,
            end: source.len() as u32,
        };
        assert_eq!(ast.roots[0].span(), invocation_span);
        let mut spans = Vec::new();
        let mut collect =
            derive_visitor::visitor_enter_fn(|expr: &talk_front::node_kinds::expr::Expr| {
                spans.push(expr.span)
            });
        for root in &ast.roots {
            root.drive(&mut collect);
        }
        drop(collect);
        assert!(spans.len() > 1);
        assert!(
            spans.iter().all(|span| *span == invocation_span),
            "{spans:?}"
        );
    }

    #[test]
    fn nested_expansions_carry_the_outer_invocation_span() {
        let source =
            "macro inner($value) { $value }\nmacro outer($value) { @inner($value) }\n@outer(7)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let invocation_span = talk_front::parsing::span::Span {
            file_id: ast.file_id,
            start: source.find("@outer").unwrap() as u32,
            end: source.len() as u32,
        };
        assert_eq!(ast.roots[0].span(), invocation_span);
    }

    #[test]
    fn selects_rules_by_arity() {
        let source = "macro pick($one) { $one }\nmacro pick($one, $two) { $two }\n@pick(1, 2)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        assert!(matches!(&expr.kind, ExprKind::LiteralInt(value) if value == "2"));
    }

    #[test]
    fn recursively_expands_macros_emitted_by_templates() {
        let source =
            "macro inner($value) { $value }\nmacro outer($value) { @inner($value) }\n@outer(7)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        assert!(matches!(&expr.kind, ExprKind::LiteralInt(value) if value == "7"));
    }

    #[test]
    fn template_bodies_may_contain_binders_and_free_identifiers() {
        // The unified template model: bodies are unparsed token templates, so
        // binders, type names, and definition-site references are all allowed.
        let source = "macro once($value) { let y = $value\ny + y }\n@once(21)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        // At item position the expansion's items splice directly into the
        // root list: the template's `let` and its trailing expression become
        // two roots.
        assert_eq!(ast.roots.len(), 2, "{:?}", ast.roots);
        assert!(matches!(
            &ast.roots[0],
            Node::Decl(Decl {
                kind: DeclKind::Let { .. },
                ..
            })
        ));
        assert!(matches!(&ast.roots[1], Node::Stmt(_)));
    }

    #[test]
    fn template_names_receive_an_expansion_context() {
        let source = "macro call_it($value) { helper($value) }\n@call_it(1)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected a call");
        };
        // The template-written callee carries a hygienic context...
        assert!(matches!(
            &callee.kind,
            ExprKind::Variable(talk_front::name::Name::Syntax(name, context))
                if name == "helper" && context.has_expansion_scope()
        ));
        // ...while the spliced argument keeps its use-site name.
        assert!(matches!(
            &args[0].value.kind,
            ExprKind::LiteralInt(value) if value == "1"
        ));
    }

    #[test]
    fn reports_arity_mismatch() {
        let source = "macro one($value) { $value }\n@one(1, 2)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            talk_front::diagnostic::AnyDiagnostic::Macro(talk_front::diagnostic::Diagnostic {
                kind: MacroError::MacroArityMismatch { .. },
                ..
            })
        )));
    }

    #[test]
    fn bounds_recursive_expansion() {
        let source = "macro recurse($value) { @recurse($value) }\n@recurse(1)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            talk_front::diagnostic::AnyDiagnostic::Macro(talk_front::diagnostic::Diagnostic {
                kind: MacroError::MacroExpansionLimit { .. },
                ..
            })
        )));
    }

    #[test]
    fn expands_before_the_existing_frontend_pipeline() {
        use talk::compiling::driver::{Driver, DriverConfig, Source};

        let driver = Driver::new_bare(
            vec![Source::from(
                "macro choose($condition, $yes, $no) { if $condition { $yes } else { $no } }\nlet answer = @choose(true, 1, 2)",
            )],
            DriverConfig::new("MacroTest"),
        );
        let typed = driver
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve")
            .type_check();
        assert!(
            typed.phase.diagnostics.is_empty(),
            "{:?}",
            typed.phase.diagnostics
        );
    }

    /// Compile and run a whole program, returning captured stdout.
    #[cfg(not(target_arch = "wasm32"))]
    fn run_program(source: &str) -> String {
        use talk::compiling::driver::{Driver, DriverConfig, Source};

        let typed = Driver::new(vec![Source::from(source)], DriverConfig::new("MacroTest"))
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve")
            .type_check();
        assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
        let executable = typed.compile_executable(None).expect("compile");
        let mut io = talk_vm::io::CaptureIO::default();
        executable.run(&mut io).expect("run");
        String::from_utf8_lossy(&io.out).into_owned()
    }

    #[test]
    #[cfg(not(target_arch = "wasm32"))]
    fn declaration_macros_generate_named_types() {
        let output = run_program(
            "macro point($name) {\n\
            \x20   struct $name {\n\
            \x20       let x: Float\n\
            \x20       let y: Float\n\
            \x20   }\n\
            }\n\
            @point(Point)\n\
            func main() {\n\
            \x20   let p = Point(x: 1.5, y: 2.5)\n\
            \x20   print(p.x + p.y)\n\
            }",
        );
        assert_eq!(output.trim(), "4.0");
    }

    #[test]
    #[cfg(not(target_arch = "wasm32"))]
    fn declaration_macros_hide_template_helpers() {
        // The template-written helper resolves inside the expansion but is
        // invisible to caller code; the spliced name is the public surface.
        let typed_ok = run_program(
            "macro with_helper($name) {\n\
            \x20   func hidden_helper() -> Int { 41 }\n\
            \x20   func $name() -> Int { hidden_helper() + 1 }\n\
            }\n\
            @with_helper(answer)\n\
            func main() { print(answer()) }",
        );
        assert_eq!(typed_ok.trim(), "42");

        use talk::compiling::driver::{Driver, DriverConfig, Source};
        let typed = Driver::new(
            vec![Source::from(
                "macro with_helper($name) {\n\
                \x20   func hidden_helper() -> Int { 41 }\n\
                \x20   func $name() -> Int { hidden_helper() + 1 }\n\
                }\n\
                @with_helper(answer)\n\
                func main() { print(hidden_helper()) }",
            )],
            DriverConfig::new("MacroTest"),
        )
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
        assert!(typed.has_errors(), "the helper must stay hidden");
    }

    #[test]
    #[cfg(not(target_arch = "wasm32"))]
    fn pattern_macros_expand_in_match_arms() {
        let output = run_program(
            "macro pair($a, $b) { ($a, $b) }\n\
            func main() {\n\
            \x20   match (1, 2) {\n\
            \x20       @pair(x, y) -> print(x + y),\n\
            \x20       _ -> print(0)\n\
            \x20   }\n\
            }",
        );
        assert_eq!(output.trim(), "3");
    }

    #[test]
    #[cfg(not(target_arch = "wasm32"))]
    fn type_macros_expand_in_signatures() {
        let output = run_program(
            "macro pair_of($t) { ($t, $t) }\n\
            func sum(p: @pair_of(Int)) -> Int { p.0 + p.1 }\n\
            func main() { print(sum(p: (3, 4))) }",
        );
        assert_eq!(output.trim(), "7");
    }

    #[test]
    #[cfg(not(target_arch = "wasm32"))]
    fn member_macros_expand_in_nominal_bodies() {
        let output = run_program(
            "macro getter($field, $ty) {\n\
            \x20   func get() -> $ty { self.$field }\n\
            }\n\
            struct Box {\n\
            \x20   let value: Int\n\
            \x20   @getter(value, Int)\n\
            }\n\
            func main() { print(Box(value: 42).get()) }",
        );
        assert_eq!(output.trim(), "42");
    }

    #[test]
    #[cfg(not(target_arch = "wasm32"))]
    fn expression_splices_group_multi_token_arguments() {
        // `0 - $x` with `1 - 2` must read `0 - (1 - 2)`, not `0 - 1 - 2`.
        let output = run_program("macro neg($x) { 0 - $x }\nfunc main() { print(@neg(1 - 2)) }");
        assert_eq!(output.trim(), "1");
    }

    #[test]
    fn gives_each_template_node_a_fresh_id() {
        let source = "macro one($value) { 1 + $value }\n(@one(2), @one(3))";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(
            std::slice::from_mut(&mut ast),
            &sources,
            &talk::procedural_macros::ToolchainMacroHost { procedural: None },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Tuple(items) = &expr.kind else {
            panic!("expected tuple");
        };
        assert_ne!(items[0].id, items[1].id);
    }
