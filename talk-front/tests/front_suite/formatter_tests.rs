    use talk_front::ast::{AST, Parsed};
    use talk::compiling::frontend::{format_string, format_string_with_width};
    use talk_front::node_id::FileID;

    fn parse(code: &str) -> AST<Parsed> {
        talk::compiling::frontend::parse_ast(code, FileID(0), "-")
            .unwrap()
            .0
    }

    fn format_code(input: &str, width: usize) -> String {
        // The parse-free public half; empty comment ranges match the old
        // inline helper exactly.
        talk_front::parsing::formatter::format_parsed(&parse(input), width, &[], input)
    }

    #[test]
    fn match_arm_macro_body_is_stable() {
        // A macro call arm body gets wrapped in braces; the same tokens parse
        // as Decl(MacroCall) inside a block vs Stmt(Expr(MacroCall)) in arm
        // position, and both must format to the same stable output.
        let stable = "match foo {\n\t_ -> {\n\t\t@html { (\"\") }\n\t}\n}";
        assert_eq!(
            format_code("match foo {\n\t_ -> @html { (\"\") }\n}", 80),
            stable
        );
        assert_eq!(format_code(stable, 80), stable);
    }

    #[test]
    fn wrapper_markers_are_stable() {
        let stable = "#[outer]\n#[logged(level: \"debug\")]\npub func loud() -> Int { 1 }";
        assert_eq!(format_code(stable, 80), stable);
        assert_eq!(
            format_code(
                "#[logged(level: \"debug\")]  pub func loud() -> Int { 1 }",
                80
            ),
            "#[logged(level: \"debug\")]\npub func loud() -> Int { 1 }"
        );
        let member = "struct Holder {\n\t#[memo]\n\tfunc cached() -> Int { 2 }\n}";
        assert_eq!(format_code(member, 80), member);
    }

    #[test]
    fn protocol_extension_heads_with_binders_and_arguments_are_stable() {
        let stable = "extend<T> Into<[T]> {\n\tconsuming func first_converted() -> T? { .none }\n}";
        assert_eq!(format_code(stable, 80), stable);
        let stable = "extend Into<Int> {\n\tconsuming func doubled() -> Int {\n\t\tself.into() * 2\n\t}\n}";
        assert_eq!(format_code(stable, 80), stable);
    }

    #[test]
    fn formats_postfix_force_unwrap() {
        assert_eq!(format_code("let x=value !", 80), "let x = value!");
        assert_eq!(format_code("!value!", 80), "!value!");
    }

    #[test]
    fn formats_specialized_type_references() {
        // Explicit head args on a type reference round-trip, for member
        // access, per-segment specialization, and qualified pattern heads.
        let member = "let x = Opt<Int>.none";
        assert_eq!(format_code(member, 80), member);
        let call = "let x = Res<Int>.A.one(1)";
        assert_eq!(format_code(call, 80), call);
        let segments = "let x = Res<Int>.A<Bool>.pair(1, true)";
        assert_eq!(format_code(segments, 80), segments);
        let bare = "let x = Opt<Int>";
        assert_eq!(format_code(bare, 80), bare);
        let pattern = "match x {\n\tRes.A.one(v) -> v,\n\tRes.A.none -> 0\n}";
        assert_eq!(format_code(pattern, 80), pattern);
        let pattern_args = "match x {\n\tOpt<Int>.some(v) -> v,\n\tOpt.none -> 0\n}";
        assert_eq!(format_code(pattern_args, 80), pattern_args);
        let struct_pattern = "match x {\n\tOuter<Int>.Inner { item } -> item\n}";
        assert_eq!(format_code(struct_pattern, 80), struct_pattern);
    }

    #[test]
    fn formats_unreachable_as_a_keyword_expression() {
        assert_eq!(
            format_code("func f()->Int{unreachable}", 80),
            "func f() -> Int { unreachable }"
        );
    }

    #[test]
    fn inserts_blank_line_after_imports() {
        assert_eq!(
            format_code("use package::foo\nlet value=1", 80),
            "use package::foo\n\nlet value = 1"
        );
        assert_eq!(
            format_code(
                "use package::foo::{ Foo }\nuse package::bar::{ Bar }\nFoo()",
                80
            ),
            "use package::foo::{ Foo }\nuse package::bar::{ Bar }\n\nFoo()"
        );
        assert_eq!(
            format_string("use package::foo\n// The first value.\nlet value=1"),
            "use package::foo\n\n// The first value.\nlet value = 1"
        );
    }

    #[test]
    fn collapses_duplicate_import_statements() {
        let input = "use package::foo::{ Foo, Shared }\n\
use package::bar::{ Bar }\n\
use package::foo::{ Baz, Shared, Foo as OtherFoo }\n\
use package::all\n\
use package::all\n\
let value=Foo()";
        let expected = "use package::foo::{ Foo, Shared, Baz, Foo as OtherFoo }\n\
use package::bar::{ Bar }\n\
use package::all\n\n\
let value = Foo()";
        assert_eq!(format_code(input, 80), expected);
    }

    #[test]
    fn preserves_separate_imports_when_they_have_comments() {
        let input = "use package::foo::{ Foo }\n\
// Keep this import documented.\n\
use package::foo::{ Bar }\n\
let value=Foo()";
        let expected = "use package::foo::{ Foo }\n\
// Keep this import documented.\n\
use package::foo::{ Bar }\n\n\
let value = Foo()";
        assert_eq!(format_string(input), expected);
    }

    #[test]
    fn formats_parameter_modes_and_argument_markers() {
        // ADR 0018 spellings round-trip.
        assert_eq!(
            format_code(
                "func f(consume a: A, mut b: B, borrow c: C, consume mut d: D) {}",
                100
            ),
            "func f(consume a: A, mut b: B, borrow c: C, consume mut d: D) {\n}"
        );
        let call = "f(consume a, copy b, borrow c, mut d, label: consume e)";
        assert_eq!(format_code(call, 100), call);
        assert_eq!(
            format_code("func f(fn: (Foo, mut Bar, consume [Baz]) -> Void) {}", 100),
            "func f(fn: (Foo, mut Bar, consume [Baz]) -> Void) {\n}"
        );
        // Legacy borrow spellings canonicalize in function-type position.
        assert_eq!(
            format_code("func f(fn: (&Foo, &mut Bar) -> Void) {}", 100),
            "func f(fn: (Foo, mut Bar) -> Void) {}"
        );
    }

    #[test]
    fn formats_parameter_labels() {
        // ADR 0041 spellings round-trip: bare positional, same-name labeled,
        // two-name labeled, and explicit `_` forms.
        assert_eq!(format_code("func bare(x) {}", 100), "func bare(x) {}");
        assert_eq!(
            format_code("func inferred_label(x:) {}", 100),
            "func inferred_label(x:) {}"
        );
        assert_eq!(
            format_code("func typed_label(x: Int) {}", 100),
            "func typed_label(x: Int) {}"
        );
        assert_eq!(
            format_code("func split(foo fizz) {}", 100),
            "func split(foo fizz) {}"
        );
        assert_eq!(
            format_code("func positional(_ value) {}", 100),
            "func positional(_ value) {}"
        );
        assert_eq!(
            format_code("func store(consume value item: Item) {}", 100),
            "func store(consume value item: Item) {}"
        );
        assert_eq!(
            format_code("func update(mut _ item: Item) {}", 100),
            "func update(mut _ item: Item) {}"
        );
        // A written `_:` call label survives formatting for the LSP to remove.
        assert_eq!(format_code("id(_: 123)", 100), "id(_: 123)");
    }

    #[test]
    fn formats_extend_heads_without_sugar() {
        // ADR 0036: an extension head is a nominal application and never
        // prints via annotation sugar; `[T]` stays legal inside the args.
        let head = "extend<Element> Array<Element>: Iterable {}";
        assert_eq!(format_code(head, 100), head);
        let bounded = "extend<Element: Showable> Array<Element>: Showable {}";
        assert_eq!(format_code(bounded, 100), bounded);
        let arg_sugar = "extend<T> Dict<[T]> {}";
        assert_eq!(format_code(arg_sugar, 100), arg_sugar);
    }

    #[test]
    fn formats_static_generics() {
        // ADR 0035 spellings round-trip.
        assert_eq!(
            format_code("let values: [Int; 3] = [1, 2, 3]", 100),
            "let values: [Int; 3] = [1, 2, 3]"
        );
        let decl = "struct Grid<static Count: Int, Element> {}";
        assert_eq!(format_code(decl, 100), decl);
        let func = "func first<static Count: Int, Element>(values: [Element; Count]) -> Element where 0 < Count {\n}";
        assert_eq!(format_code(func, 120), func);
        let args = "func c<static N: Int, T>(a: [T; 2 * N + 1]) {\n}";
        assert_eq!(format_code(args, 100), args);
        let le = "func f<static N: Int, static M: Int>() where N <= M {\n}";
        assert_eq!(format_code(le, 100), le);
    }

    #[test]
    fn test_literal_formatting() {
        assert_eq!(format_code("123", 80), "123");
        assert_eq!(format_code("123.45", 80), "123.45");
        assert_eq!(format_code("true", 80), "true");
        assert_eq!(format_code("false", 80), "false");
    }

    #[test]
    fn test_binary_expressions() {
        assert_eq!(format_code("1 + 2", 80), "1 + 2");
        assert_eq!(format_code("1+2", 80), "1 + 2");
        assert_eq!(format_code("1 * 2 + 3", 80), "1 * 2 + 3");
        assert_eq!(format_code("1 == 2", 80), "1 == 2");
        assert_eq!(format_code("1 != 2", 80), "1 != 2");
        assert_eq!(format_code("1 < 2", 80), "1 < 2");
        assert_eq!(format_code("1 <= 2", 80), "1 <= 2");
        assert_eq!(format_code("1 > 2", 80), "1 > 2");
        assert_eq!(format_code("1 >= 2", 80), "1 >= 2");
    }

    #[test]
    fn test_unary_expressions() {
        assert_eq!(format_code("-1", 80), "-1");
        assert_eq!(format_code("!true", 80), "!true");
        assert_eq!(format_code("- 1", 80), "-1");
        assert_eq!(format_code("! true", 80), "!true");
    }

    #[test]
    fn test_variable_and_member_access() {
        assert_eq!(format_code("foo", 80), "foo");
        assert_eq!(format_code("foo.bar", 80), "foo.bar");
        assert_eq!(format_code("foo . bar", 80), "foo.bar");
        assert_eq!(format_code(".bar", 80), ".bar");
    }

    #[test]
    fn test_array_formatting() {
        assert_eq!(format_code("[]", 80), "[]");
        assert_eq!(format_code("[1]", 80), "[1]");
        assert_eq!(format_code("[1, 2, 3]", 80), "[1, 2, 3]");

        // Test line breaking for long arrays
        let long_array = "[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]";
        let formatted = format_code(long_array, 30);
        assert!(formatted.contains('\n'));
    }

    #[test]
    fn test_tuple_formatting() {
        assert_eq!(format_code("()", 80), "()");
        assert_eq!(format_code("(1)", 80), "(1)");
        assert_eq!(format_code("(1, 2)", 80), "(1, 2)");
        assert_eq!(format_code("(1, 2, 3)", 80), "(1, 2, 3)");
        assert_eq!(format_code("(.none,.none,)", 80), "(.none, .none)");
    }

    #[test]
    fn test_function_declarations() {
        // assert_eq!(format_code("func() {}", 80), "func() {}");
        assert_eq!(format_code("func foo() {}", 80), "func foo() {}");
        assert_eq!(format_code("func foo(a) {}", 80), "func foo(a) {}");
        assert_eq!(format_code("func foo(a, b) {}", 80), "func foo(a, b) {}");

        // With return type
        assert_eq!(
            format_code("func foo() -> Int {}", 80),
            "func foo() -> Int {}"
        );

        // With type parameters
        assert_eq!(
            format_code("func foo(a: Int) {}", 80),
            "func foo(a: Int) {}"
        );
        assert_eq!(
            format_code("func foo(a: Int, b: Bool) {}", 80),
            "func foo(a: Int, b: Bool) {}"
        );

        // With generics
        assert_eq!(format_code("func foo<T>() {}", 80), "func foo<T>() {}");
        assert_eq!(
            format_code("func foo<T, U>() {}", 80),
            "func foo<T, U>() {}"
        );
    }

    #[test]
    fn wraps_long_function_parameter_lists() {
        let source = "pub func passthrough(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult { .replace(target) }";
        let expected = "pub func passthrough(\n\tinput: MacroInput?,\n\tconsume target: Syntax<Decl>,\n\tdeclaration: DeclContext,\n\tuse_site: SyntaxContext,\n\tcontext: QuoteContext\n) -> DeclWrapperResult {\n\t.replace(target)\n}";

        let formatted = format_code(source, 80);
        assert_eq!(formatted, expected);
        assert_eq!(format_code(&formatted, 80), formatted);
    }

    #[test]
    fn test_capture_spec_formatting() {
        assert_eq!(
            format_code(
                "let f = func() { [copy a, consuming b, &c, &mut d] in }",
                80,
            ),
            "let f = func() { [a, consuming b, &c, &mut d] in\n}"
        );
        assert_eq!(
            format_code("func values() { [value] }", 80),
            "func values() { [value] }"
        );
    }

    #[test]
    fn test_function_bodies() {
        assert_eq!(format_code("func foo() { 123 }", 80), "func foo() { 123 }");

        assert_eq!(
            format_code("func foo() {\n123\n456\n}", 80),
            "func foo() {\n\t123\n\t456\n}"
        );
    }

    #[test]
    fn test_func_bodies_with_multiple_exprs_with_call() {
        assert_eq!(
            format_code("func foo() {1+1 2+2}()", 80),
            "func foo() {\n\t1 + 1\n\t2 + 2\n}()"
        );
    }

    #[test]
    fn test_doesnt_insert_too_many_newlines_at_root() {
        assert_eq!(
            format_code("let x = 1\nlet y = 2", 80),
            "let x = 1\nlet y = 2"
        );
    }

    #[test]
    fn test_doesnt_insert_too_many_newlines_nested() {
        assert_eq!(
            format_code("func() {let x = 1\nlet y = 2 }", 80),
            "func() {\n\tlet x = 1\n\tlet y = 2\n}"
        );
    }

    #[test]
    fn test_respects_newlines() {
        assert_eq!(
            format_code(
                "let maybe = Maybe.definitely(123)\n\nmatch maybe {\n\t.definitely(x) -> x\n}",
                80
            ),
            "let maybe = Maybe.definitely(123)\n\nmatch maybe {\n\t.definitely(x) -> x\n}"
        );
    }

    #[test]
    fn preserves_blank_line_that_terminates_member_chain() {
        assert_eq!(
            format_code("print(\"sup\")\n\n.foo", 80),
            "print(\"sup\")\n\n.foo"
        );
    }

    #[test]
    fn formats_macro_rules_and_invocations() {
        assert_eq!(
            format_code("macro choose($yes,$no) {$yes}\n@choose(1,2)", 80),
            "macro choose($yes, $no) { $yes }\n@choose(1, 2)"
        );
        let multiline = "macro unless($condition, $body) {\n\tif $condition {\n\t\t()\n\t} else {\n\t\t$body\n\t}\n}";
        assert_eq!(
            format_code(
                "macro unless($condition, $body) { if $condition {\n        ()\n    } else {\n        $body\n    } }",
                80
            ),
            multiline
        );
        assert_eq!(format_code(multiline, 80), multiline);
        assert_eq!(
            format_code("macro documented($value) {\n    // Keep this.\n    $value\n}", 80),
            "macro documented($value) {\n\t// Keep this.\n\t$value\n}"
        );
        let multiline_string = "macro text() {\n\t\"hello\n  world\"\n}";
        assert_eq!(
            format_code("macro text() {\n    \"hello\n  world\"\n}", 80),
            multiline_string
        );
        assert_eq!(
            format_code(multiline_string, 80),
            multiline_string,
            "indentation inside a multiline string is token content"
        );
        assert_eq!(
            format_code("@html { div class=@card { <not talk> } }", 80),
            "@html { div class=@card { <not talk> } }"
        );
        assert_eq!(
            format_code("quote { helper(value: $item) }", 80),
            "quote { helper(value: $item) }"
        );
    }

    #[test]
    fn test_function_calls() {
        assert_eq!(format_code("foo()", 80), "foo()");
        assert_eq!(format_code("foo(1)", 80), "foo(1)");
        assert_eq!(format_code("foo(1, 2)", 80), "foo(1, 2)");
        assert_eq!(format_code("foo\"bar\"", 80), "foo \"bar\"");
        assert_eq!(format_code("foo \"bar\"", 80), "foo \"bar\"");
        assert_eq!(format_code("foo(\"bar\")", 80), "foo(\"bar\")");
        assert_eq!(format_code("foo\"bar\"{ 1 }", 80), "foo \"bar\" { 1 }");

        // With generics
        assert_eq!(format_code("foo<Int>()", 80), "foo<Int>()");
        assert_eq!(
            format_code("foo<Int, Bool>(1, true)", 80),
            "foo<Int, Bool>(1, true)"
        );

        // Long calls should break
        let long_call = "foo(very_long_argument_name, another_very_long_argument)";
        let formatted = format_code(long_call, 40);
        assert!(formatted.contains('\n'));
    }

    #[test]
    fn test_let_declarations() {
        assert_eq!(format_code("let x", 80), "let x");
        assert_eq!(format_code("let x: Int", 80), "let x: Int");
        assert_eq!(format_code("let x = 123", 80), "let x = 123");
        assert_eq!(format_code("let x: Int = 123", 80), "let x: Int = 123");
        assert_eq!(
            format_code(
                "loop {\nlet .some(peeked) = self.peek() else {\nbreak\n}\nprint(peeked)\n}",
                80,
            ),
            "loop {\n\tlet .some(peeked) = self.peek() else {\n\t\tbreak\n\t}\n\tprint(peeked)\n}"
        );
        assert_eq!(
            format_code(
                "func value(input: Int?) -> Int {\nlet .some(value): Int? = input else { return 0 }\nvalue\n}",
                80,
            ),
            "func value(input: Int?) -> Int {\n\tlet .some(value): Int? = input else { return 0 }\n\tvalue\n}"
        );
    }

    #[test]
    fn test_if_expressions() {
        assert_eq!(format_code("if true { 123 }", 80), "if true { 123 }");
        assert_eq!(
            format_code("if true { 123 } else { 456 }", 80),
            "if true {\n\t123\n} else {\n\t456\n}"
        );
        assert_eq!(
            format_code("if true {} else {}", 80),
            "if true {\n} else {\n}"
        );
        assert_eq!(
            format_code("let value = if true { 123 } else { 456 }", 80),
            "let value = if true {\n\t123\n} else {\n\t456\n}"
        );
        assert_eq!(
            format_code("let value = if true {} else {}", 80),
            "let value = if true {\n} else {\n}"
        );
        assert_eq!(
            format_code("if let .some(cwd) = optionalthing { cwd }", 80),
            "if let .some(cwd) = optionalthing {\n\tcwd\n}"
        );
        assert_eq!(
            format_code(
                "if let .some(cwd) = optionalthing { cwd } else { \"\" }",
                80
            ),
            "if let .some(cwd) = optionalthing {\n\tcwd\n} else {\n\t\"\"\n}"
        );
        assert_eq!(
            format_code("if let .pattern(x) = foo { } else { }", 80),
            "if let .pattern(x) = foo {\n} else {\n}"
        );
        assert_eq!(
            format_code(
                "if let .some(x) = value, allowed(x) { print(x) } else { print(0) }",
                80
            ),
            "if let .some(x) = value, allowed(x) {\n\tprint(x)\n} else {\n\tprint(0)\n}"
        );
        assert_eq!(
            format_code("if first, second { print(1) } else { print(0) }", 80),
            "if first, second {\n\tprint(1)\n} else {\n\tprint(0)\n}"
        );
        assert_eq!(
            format_code(
                "if let .some(ch) = self.peek(), ch.is_ident() { return self.make(\nself.identifier()\n) }",
                80
            ),
            "if let .some(ch) = self.peek(), ch.is_ident() {\n\treturn self.make(self.identifier())\n}"
        );

        // Nested
        assert_eq!(
            format_code("if true {\nif false { 1 }\n}", 80),
            "if true {\n\tif false { 1 }\n}"
        );

        // Keep continue/break blocks multiline; parser rejects inline forms.
        assert_eq!(
            format_code("loop {\nif true {\ncontinue\n}\n}", 80),
            "loop {\n\tif true {\n\t\tcontinue\n\t}\n}"
        );
        assert_eq!(
            format_code("loop {\nif true {\nbreak\n}\n}", 80),
            "loop {\n\tif true {\n\t\tbreak\n\t}\n}"
        );

        // `'continue` resumes the enclosing handler, with or without a
        // payload.
        assert_eq!(
            format_code("#handle 'ask {\n'continue 1\n}", 80),
            "#handle 'ask {\n\t'continue 1\n}"
        );
        assert_eq!(
            format_code("#handle 'ping {\n'continue\n}", 80),
            "#handle 'ping {\n\t'continue\n}"
        );
    }

    #[test]
    fn test_loop_expressions() {
        assert_eq!(format_code("loop { 123 }", 80), "loop { 123 }");
        assert_eq!(format_code("loop true { 123 }", 80), "loop true { 123 }");
    }

    #[test]
    fn test_enum_declarations() {
        assert_eq!(format_code("enum Foo {}", 80), "enum Foo {}");
        assert_eq!(
            format_code("enum Foo { case a case b }", 80),
            "enum Foo {\n\tcase a\n\tcase b\n}"
        );
        assert_eq!(
            format_code("enum Foo { case a(Int) }", 80),
            "enum Foo {\n\tcase a(Int)\n}"
        );
        assert_eq!(
            format_code("enum Option<T> { case some(T) case none }", 80),
            "enum Option<T> {\n\tcase some(T)\n\tcase none\n}"
        );
        assert_eq!(
            format_code("enum Foo { case bar(fizz: Int,buzz: String) }", 80),
            "enum Foo {\n\tcase bar(fizz: Int, buzz: String)\n}"
        );
        assert_eq!(
            format_code(
                "pub enum Optional<Wrapped> {\ncase some(Wrapped)\ncase none\n\nfunc map<T>(transform: (Wrapped) -> T) -> T? {\nmatch self {\n.some(t) -> .some(transform(t)),\n.none -> none\n}\n}\n}",
                80
            ),
            "pub enum Optional<Wrapped> {\n\tcase some(Wrapped)\n\tcase none\n\n\tfunc map<T>(transform: (Wrapped) -> T) -> T? {\n\t\tmatch self {\n\t\t\t.some(t) -> .some(transform(t)),\n\t\t\t.none -> none\n\t\t}\n\t}\n}"
        );
    }

    #[test]
    fn formats_quoted_identifiers() {
        // Names that collide with keywords keep their #"..." spelling.
        assert_eq!(
            format_code("enum Fizz { case #\"as\", #\"func\" }", 80),
            "enum Fizz {\n\tcase #\"as\"\n\tcase #\"func\"\n}"
        );
        assert_eq!(
            format_code("let #\"struct\" = 1", 80),
            "let #\"struct\" = 1"
        );
        assert_eq!(
            format_code("let #\"hello world\" = 1", 80),
            "let #\"hello world\" = 1"
        );
        // Quoting an ordinary identifier canonicalizes to the plain spelling.
        assert_eq!(format_code("let #\"foo\" = 1", 80), "let foo = 1");
        assert_eq!(format_code("Fizz.#\"as\"", 80), "Fizz.#\"as\"");
    }

    #[test]
    fn test_match_expressions() {
        let match_expr = r#"match x {
            .some(val) -> val,
            .none() -> 0
        }"#;

        let expected = "match x {\n\t.some(val) -> val,\n\t.none -> 0\n}";
        assert_eq!(format_code(match_expr, 80), expected);

        // With enum prefix
        let match_with_enum = r#"match x {
            Option.some(val) -> val,
            Option.none -> 0
        }"#;

        let expected_enum = "match x {\n\tOption.some(val) -> val,\n\tOption.none -> 0\n}";
        assert_eq!(format_code(match_with_enum, 80), expected_enum);

        assert_eq!(
            format_code("match foo { .bar(fizz: _,buzz: value) -> value }", 80),
            "match foo {\n\t.bar(fizz: _, buzz: value) -> value\n}"
        );
    }

    #[test]
    fn test_struct_declarations() {
        assert_eq!(format_code("struct Person {}", 80), "struct Person {}");

        let struct_with_fields = r#"struct Person { let name: String let age: Int }"#;

        let expected = "struct Person {\n\tlet name: String\n\tlet age: Int\n}";
        assert_eq!(format_code(struct_with_fields, 80), expected);

        let struct_with_static_members = r#"struct Cache {
            static let version: Int = 1
            static func create() { Cache() }
        }"#;
        let expected_static_members =
            "struct Cache {\n\tstatic let version: Int = 1\n\tstatic func create() { Cache() }\n}";
        assert_eq!(
            format_code(struct_with_static_members, 80),
            expected_static_members
        );
    }

    #[test]
    fn test_return_statements() {
        assert_eq!(format_code("func() { return }", 80), "func() { return }");
        assert_eq!(
            format_code("func() { return 123 }", 80),
            "func() { return 123 }"
        );
        assert_eq!(
            format_code("func() { return foo() }", 80),
            "func() { return foo() }"
        );
    }

    #[test]
    fn test_blank_line_preservation() {
        let code_with_blanks = r#"func foo() {
            123
        }

        func bar() {
            456
        }"#;

        let formatted = format_code(code_with_blanks, 80);
        assert!(formatted.contains("\n\nfunc bar"));
    }

    #[test]
    fn test_type_annotations() {
        assert_eq!(format_code("let x: Int?", 80), "let x: Int?");
        assert_eq!(format_code("let xs: Array<Int>", 80), "let xs: [Int]");
        assert_eq!(format_code("let xs: [[String]]", 80), "let xs: [[String]]");
        assert_eq!(
            format_code("let element: [Int].Element", 80),
            "let element: [Int].Element"
        );
        assert_eq!(format_code("let x: (Int, Bool)", 80), "let x: (Int, Bool)");
        assert_eq!(
            format_code("let f: (Int) -> Bool", 80),
            "let f: (Int) -> Bool"
        );
        assert_eq!(
            format_code("let f: (Int, Bool) -> String", 80),
            "let f: (Int, Bool) -> String"
        );
    }

    #[test]
    fn test_complex_expressions() {
        // Test precedence handling
        assert_eq!(format_code("1 + 2 * 3", 80), "1 + 2 * 3");
        assert_eq!(format_code("(1 + 2) * 3", 80), "(1 + 2) * 3");

        // Test chained member access
        assert_eq!(format_code("foo.bar.baz", 80), "foo.bar.baz");

        // Test nested calls
        assert_eq!(format_code("foo(bar(baz()))", 80), "foo(bar(baz()))");
    }

    #[test]
    fn test_assignment() {
        assert_eq!(format_code("x = 123", 80), "x = 123");
        assert_eq!(format_code("x = y + z", 80), "x = y + z");
        assert_eq!(format_code("foo.bar = 123", 80), "foo.bar = 123");
    }

    #[test]
    fn test_width_constraints() {
        // Test that long lines are broken appropriately
        let long_function = "func long_name(param: Int) {}";
        let formatted = format_code(long_function, 40);
        // The exact formatting might vary, but it should be reasonable
        assert!(!formatted.is_empty());
    }

    #[test]
    fn test_pattern_matching() {
        // Test various pattern types
        assert_eq!(
            format_code("match x { 1 -> true }", 80),
            "match x {\n\t1 -> true\n}"
        );

        assert_eq!(
            format_code("match x { _ -> true }", 80),
            "match x {\n\t_ -> true\n}"
        );

        assert_eq!(
            format_code("match x { true -> 1\nfalse -> 0 }", 80),
            "match x {\n\ttrue -> 1,\n\tfalse -> 0\n}"
        );

        // Struct patterns keep shorthand fields and print `field: pattern`
        // only when the sub-pattern differs from the field name.
        assert_eq!(
            format_code("match p { Point { x , y: 1 } -> x }", 80),
            "match p {\n\tPoint { x, y: 1 } -> x\n}"
        );

        assert_eq!(
            format_code("match x { { x, y } -> x }", 80),
            "match x {\n\t{ x, y } -> x\n}"
        );

        assert_eq!(
            format_code("match x { { x: 123, .. } -> 0 }", 80),
            "match x {\n\t{ x: 123, .. } -> 0\n}"
        );
    }

    #[test]
    fn test_single_line_function_formatting() {
        // Test that simple functions can be formatted on one line
        assert_eq!(
            format_code("func add(a, b) { a + b }", 80),
            "func add(a, b) { a + b }"
        );

        // But functions with multiple statements should not
        assert_eq!(
            format_code("func foo() { let x = 1\nx + 1 }", 80),
            "func foo() {\n\tlet x = 1\n\tx + 1\n}"
        );

        // Functions containing other functions should always be multi-line
        assert_eq!(
            format_code("func outer() { func inner() {} }", 80),
            "func outer() {\n\tfunc inner() {}\n}"
        );
    }

    #[test]
    fn test_for_loop_is_always_multiline() {
        // A `for` body never collapses to one line, even when it would fit.
        assert_eq!(
            format_code("for x in xs { print(x) }", 80),
            "for x in xs {\n\tprint(x)\n}"
        );
    }

    #[test]
    fn test_for_loop_preserves_source_mode() {
        assert_eq!(
            format_code("for x in consume xs { print(x) }", 80),
            "for x in consume xs {\n\tprint(x)\n}"
        );
        assert_eq!(
            format_code("for x in mut xs { print(x) }", 80),
            "for x in mut xs {\n\tprint(x)\n}"
        );
    }

    #[test]
    fn test_block_args_formatting() {
        assert_eq!(format_code("map { $0 }", 80), "map { $0 }");
        assert_eq!(format_code("map { $0 * $1 }", 80), "map { $0 * $1 }");
        assert_eq!(format_code("map({ $0 })", 80), "map { $0 }");

        assert_eq!(
            format_code("#handle 'fizz { x in x }", 80),
            "#handle 'fizz { x in x }"
        );

        let input = "#handle 'fizz { x: Int, y: Bool in\nx\n}";
        let expected = "#handle 'fizz { x: Int, y: Bool in x }";
        assert_eq!(format_code(input, 80), expected);

        let input = "#handle 'fizz { x in\nx\nx\n}";
        let expected = "#handle 'fizz { x in\n\tx\n\tx\n}";
        assert_eq!(format_code(input, 80), expected);

        let input = "#handle 'os { request in match request { .cwd -> \"\", .args -> [] } }";
        let expected = "#handle 'os { request in\n\tmatch request {\n\t\t.cwd -> \"\",\n\t\t.args -> []\n\t}\n}";
        assert_eq!(format_code(input, 80), expected);
    }

    #[test]
    fn test_single_line_function_threshold() {
        assert_eq!(
            format_code(
                "func very_long_function_name(param_one: Int, param_two: Int) { 1 }",
                80
            ),
            "func very_long_function_name(param_one: Int, param_two: Int) {\n\t1\n}"
        );
    }

    #[test]
    fn test_preserves_line_comments_inline() {
        assert_eq!(format_string("let x=1 // note"), "let x = 1 // note");
    }

    #[test]
    fn test_preserves_line_comments_between_roots() {
        let input = "let x = 1\n// note\nlet y = 2";
        let expected = "let x = 1\n// note\nlet y = 2";
        assert_eq!(format_string(input), expected);
    }

    #[test]
    fn test_preserves_line_comments_in_block() {
        let input = "func foo() {\n// note\n}";
        let expected = "func foo() {\n\t// note\n}";
        assert_eq!(format_string(input), expected);
    }

    #[test]
    fn test_keeps_nested_comments_attached_after_labeled_arguments() {
        let input = "struct A {\n\t// first\n\tfunc foo() {}\n\n\t// second\n\tfunc bar() {\n\t\tThing(a: 1, b: 2, c: 3, d: 4, e: 5)\n\t}\n}";
        let expected = "struct A {\n\t// first\n\tfunc foo() {}\n\n\t// second\n\tfunc bar() {\n\t\tThing(a: 1, b: 2, c: 3, d: 4, e: 5)\n\t}\n}";
        assert_eq!(format_string(input), expected);
    }

    #[test]
    fn test_keeps_empty_chained_calls_on_one_line() {
        let input = "very_long_receiver_name().next().finish()";
        assert_eq!(format_string_with_width(input, 12), input);
    }

    #[test]
    fn test_wraps_long_standalone_line_comments() {
        let input = "// alpha beta gamma delta\nlet x = 1";
        let expected = "// alpha beta\n// gamma delta\nlet x = 1";
        assert_eq!(format_string_with_width(input, 18), expected);
    }

    #[test]
    fn test_wraps_long_inline_line_comments() {
        let input = "let x = 1 // alpha beta gamma";
        let expected = "let x = 1 // alpha\n// beta gamma";
        assert_eq!(format_string_with_width(input, 20), expected);
    }

    #[test]
    fn test_wraps_long_line_comments_in_block() {
        let input = "func foo() {\n// alpha beta gamma delta\n}";
        let expected = "func foo() {\n\t// alpha beta\n\t// gamma delta\n}";
        assert_eq!(format_string_with_width(input, 18), expected);
    }

    #[test]
    fn test_string_literal_formatting() {
        assert_eq!(format_code(r#""hello""#, 80), r#""hello""#);
        // \n escape preserved
        assert_eq!(format_code(r#""hello\nworld""#, 80), r#""hello\nworld""#);
        // literal newline preserved
        assert_eq!(format_code("\"hello\nworld\"", 80), "\"hello\nworld\"");
        // \t preserved
        assert_eq!(format_code(r#""tab\there""#, 80), r#""tab\there""#);
    }

    #[test]
    fn test_effect_call_formatting() {
        // Effect calls should stay on one line when they fit
        assert_eq!(format_code("'emit(123)", 80), "'emit(123)");
        assert_eq!(format_code("'emit(x, y)", 80), "'emit(x, y)");

        // Effect calls with labels
        assert_eq!(format_code("'emit(value: 123)", 80), "'emit(value: 123)");

        // Effect calls use the same trailing-block formatting as functions.
        assert_eq!(format_code("'emit(){ 1 }", 80), "'emit { 1 }");
        assert_eq!(format_code("'emit(123){ $0 }", 80), "'emit(123) { $0 }");
        assert_eq!(
            format_code("'emit<Int>() { value in value }", 80),
            "'emit<Int> { value in value }"
        );
    }

    #[test]
    fn trailing_block_has_space() {
        // Trailing block with no args - parens omitted, space before {
        assert_eq!(format_code("foo(){ 1 }", 80), "foo { 1 }");
        assert_eq!(format_code("foo() { 1 }", 80), "foo { 1 }");
        // Trailing block without parens - stays the same
        assert_eq!(format_code("foo { 1 }", 80), "foo { 1 }");
        // Trailing block with args - space before {
        assert_eq!(format_code("foo(1){ 2 }", 80), "foo(1) { 2 }");
        assert_eq!(format_code("foo(1) { 2 }", 80), "foo(1) { 2 }");
    }

    #[test]
    fn test_call_trailing_block_is_multiline() {
        assert_eq!(
            format_code("test(\"adds\") { assert(1 + 1 == 2, \"did not add\") }", 80),
            "test(\"adds\") {\n\tassert(1 + 1 == 2, \"did not add\")\n}"
        );
        assert_eq!(
            format_code("test\"adds\"{ assert(1 + 1 == 2, \"did not add\") }", 80),
            "test \"adds\" {\n\tassert(1 + 1 == 2, \"did not add\")\n}"
        );
        assert_eq!(
            format_code("other(\"adds\") { assert(true, \"ok\") }", 80),
            "other(\"adds\") { assert(true, \"ok\") }"
        );
    }

    #[test]
    fn typealias_round_trips_with_spaced_equals() {
        assert_eq!(
            format_code("typealias Target = Response", 80),
            "typealias Target = Response"
        );
    }

    #[test]
    fn long_labeled_call_round_trips() {
        // Wrapping a long labeled call must produce output the parser can
        // read back (one argument per line).
        let source = "let node = RouteNode(path: some_longer_name, handler: another_long_name, next: a_third_long_name)";
        let formatted = format_code(source, 60);
        assert!(
            formatted.contains("(\n"),
            "expected the call to wrap: {formatted}"
        );
        assert_eq!(
            format_code(&formatted, 60),
            formatted,
            "the wrapped form must re-parse and be stable"
        );
    }

    #[test]
    fn linear_struct_round_trips() {
        assert_eq!(
            format_code("struct FileHandle 'linear {\n\tlet fd: Int\n}", 80),
            "struct FileHandle 'linear {\n\tlet fd: Int\n}"
        );
        assert_eq!(
            format_code("pub struct Token 'linear {\n\tlet id: Int\n}", 80),
            "pub struct Token 'linear {\n\tlet id: Int\n}"
        );
        assert_eq!(
            format_code("struct Node<T> 'heap {\n\tlet value: T\n}", 80),
            "struct Node<T> 'heap {\n\tlet value: T\n}"
        );
    }

    #[test]
    fn enum_grades_round_trip() {
        assert_eq!(
            format_code("enum Token 'linear {\n\tcase once(Int)\n}", 80),
            "enum Token 'linear {\n\tcase once(Int)\n}"
        );
        assert_eq!(
            format_code("enum Expr<T> 'heap {\n\tcase int(Int) -> Expr<Int>\n}", 80),
            "enum Expr<T> 'heap {\n\tcase int(Int) -> Expr<Int>\n}"
        );
    }

    #[test]
    fn core_smoke_test() {
        // Make sure core is the same before and after formatting
        // (skipping core/builtins/, the builtin-type Markdown docs).
        for path in std::fs::read_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../core")).unwrap() {
            let path = path.unwrap().path();
            if path.extension().and_then(|e| e.to_str()) != Some("tlk") {
                continue;
            }
            let code = std::fs::read_to_string(&path).unwrap();
            assert_eq!(
                code,
                format_string(&code),
                "formatter changed {}",
                path.display()
            );
        }
    }

    #[test]
    fn examples_smoke_test() {
        // Make sure examples are the same before and after formatting
        // (skipping examples/expected/, the runtime stdout goldens).
        for path in std::fs::read_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../examples")).unwrap() {
            let path = path.unwrap().path();
            if path.extension().and_then(|e| e.to_str()) != Some("tlk") {
                continue;
            }
            let code = std::fs::read_to_string(&path).unwrap();
            assert_eq!(
                code,
                format_string(&code),
                "formatter changed {}",
                path.display()
            );
        }
    }
