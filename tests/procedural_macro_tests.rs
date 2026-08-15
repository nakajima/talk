use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use talk::compiling::{
    driver::{Driver, DriverConfig, Source},
    package::PackageProject,
};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

#[test]
fn discovers_and_executes_brace_token_tree_macro() {
    let root = std::env::temp_dir().join(format!(
        "talk-procedural-macro-{}-{}",
        std::process::id(),
        std::thread::current().name().unwrap_or("test")
    ));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create macro fixture");
    let main = root.join("main.tlk");
    fs::write(
        &main,
        "func helper(value: Int) -> Int { value }\nlet caller = 42\n@call_helper { caller }\n",
    )
    .expect("write use site");
    fs::write(
        root.join("identity.macro.tlk"),
        r#"
use package::Lexer::{ MacroInput, TokenTree, group_contents }
use package::Ast::{ Expr }
use package::Syntax::{ Syntax, SyntaxResult, SyntaxFailure, SyntaxContext, QuoteContext, capture_expr }

pub func call_helper(input: MacroInput, use_site: SyntaxContext, context: QuoteContext) -> SyntaxResult<Expr> {
    match input.tree {
        .group(group) -> {
            let captured = capture_expr(
                source_id: input.source_id,
                source: input.source,
                input: group_contents(group: group),
                context: use_site
            )
            if let .some(value) = captured.value {
                return quote { helper(value: $value) }
            }
            SyntaxResult<Expr>(value: .none, failure: captured.failure)
        },
        .leaf(token) -> SyntaxResult<Expr>(
            value: .none,
            failure: .some(SyntaxFailure(code: "macro.expected-group", message: "Expected a group", span: token.span))
        )
    }
}
"#,
    )
    .expect("write macro unit");

    let config = DriverConfig::new("MacroFixture")
        .source_root(root.clone())
        .workspace_root(root.clone());
    let typed = Driver::new_bare(vec![Source::from(main)], config)
        .parse()
        .expect("discover and parse")
        .resolve_names()
        .expect("expand and resolve")
        .type_check();
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let executable = typed.compile_executable(None).expect("compile expansion");
    let mut io = talk_vm::io::CaptureIO::default();
    let value = executable.run(&mut io).expect("execute expansion");
    assert_eq!(value.as_deref(), Some("42"));
    fs::remove_dir_all(root).expect("remove macro fixture");
}

/// Compile-and-run helper for wrapper fixtures: one `main.tlk`, one macro
/// unit, one expected program value.
fn run_wrapper_fixture(label: &str, main_source: &str, macro_unit: &str) -> Result<String, String> {
    let root = std::env::temp_dir().join(format!(
        "talk-wrapper-macro-{label}-{}-{}",
        std::process::id(),
        TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create wrapper fixture");
    let main = root.join("main.tlk");
    fs::write(&main, main_source).expect("write use site");
    fs::write(root.join("wrappers.macro.tlk"), macro_unit).expect("write macro unit");

    let config = DriverConfig::new("WrapperFixture")
        .source_root(root.clone())
        .workspace_root(root.clone());
    let result = (|| {
        let typed = Driver::new_bare(vec![Source::from(main)], config)
            .parse()
            .map_err(|error| format!("parse: {error:?}"))?
            .resolve_names()
            .map_err(|error| format!("resolve: {error:?}"))?
            .type_check();
        if typed.has_errors() {
            return Err(format!("type check: {:?}", typed.diagnostics()));
        }
        let executable = typed
            .compile_executable(None)
            .map_err(|error| format!("compile: {error:?}"))?;
        let mut io = talk_vm::io::CaptureIO::default();
        let value = executable
            .run(&mut io)
            .map_err(|error| format!("run: {error:?}"))?;
        Ok(value.unwrap_or_default())
    })();
    fs::remove_dir_all(root).expect("remove wrapper fixture");
    result
}

const WRAPPERS_UNIT: &str = r#"
use package::Lexer::{ MacroInput, group_contents }
use package::Ast::{ Decl }
use package::Syntax::{ Syntax, SyntaxFailure, DeclWrapperResult, DeclContext, SyntaxContext, QuoteContext, capture_decl }

pub func passthrough(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    .replace(target)
}

pub func omit(input: MacroInput?, target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    .remove
}

pub func fail_always(input: MacroInput?, target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    .failure(SyntaxFailure(code: "test.rejected", message: "wrapper rejected the target", span: 0..<0))
}

pub func replace_with(input: MacroInput?, target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    if let .some(args) = input {
        if let .group(group) = args.tree {
            for child in group.children {
                if let .group(braced) = child {
                    let captured = capture_decl(
                        source_id: args.source_id,
                        source: args.source,
                        input: group_contents(group: braced),
                        context: use_site
                    )
                    if let .some(value) = captured.value {
                        return .replace(value)
                    }
                    if let .some(failure) = captured.failure {
                        return .failure(failure)
                    }
                }
            }
        }
    }
    .failure(SyntaxFailure(code: "test.arguments", message: "expected a braced declaration argument", span: 0..<0))
}

pub func quoted(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    let result = quote decl { $target }
    if let .some(value) = result.value {
        return .replace(value)
    }
    if let .some(failure) = result.failure {
        return .failure(failure)
    }
    .failure(SyntaxFailure(code: "test.quote", message: "quotation failed", span: 0..<0))
}
"#;

#[test]
fn wrapper_replace_passes_the_target_through() {
    let value = run_wrapper_fixture(
        "passthrough",
        "#[passthrough]\nfunc greet() -> Int { 42 }\n\ngreet()\n",
        WRAPPERS_UNIT,
    )
    .expect("wrapper fixture");
    assert_eq!(value, "42");
}

#[test]
fn wrappers_apply_in_every_declaration_context() {
    let value = run_wrapper_fixture(
        "contexts",
        "#[passthrough]\n\
         pub func base() -> Int { 42 }\n\n\
         struct Holder {\n\
         \t#[quoted]\n\
         \tfunc bump(amount: Int) -> Int { amount }\n\
         }\n\n\
         enum Flag {\n\
         \t#[passthrough]\n\
         \tcase on\n\
         \tcase off\n\
         }\n\n\
         #[omit]\n\
         func broken() -> Int { \"removed before type checking\" }\n\n\
         let holder = Holder()\n\
         holder.bump(amount: base())\n",
        WRAPPERS_UNIT,
    )
    .expect("wrapper fixture");
    assert_eq!(value, "42");
}

#[test]
fn wrapper_chains_apply_innermost_first() {
    let value = run_wrapper_fixture(
        "chain",
        "#[replace_with({ func value() -> Int { 41 } })]\n\
         #[replace_with({ func value() -> Int { 42 } })]\n\
         func value() -> Int { 0 }\n\n\
         value()\n",
        WRAPPERS_UNIT,
    )
    .expect("wrapper fixture");
    assert_eq!(value, "41");
}

#[test]
fn wrapper_remove_stops_the_chain_and_unbinds_the_target() {
    let error = run_wrapper_fixture(
        "remove-chain",
        "#[replace_with({ func value() -> Int { 42 } })]\n\
         #[omit]\n\
         func value() -> Int { 0 }\n\n\
         value()\n",
        WRAPPERS_UNIT,
    )
    .expect_err("the removed declaration must not resolve");
    assert!(error.contains("UndefinedName"), "{error}");
}

#[test]
fn wrapper_failure_reports_a_structured_diagnostic() {
    let error = run_wrapper_fixture(
        "failure",
        "#[fail_always]\nfunc value() -> Int { 0 }\n\nvalue()\n",
        WRAPPERS_UNIT,
    )
    .expect_err("the wrapper failure must surface");
    assert!(error.contains("test.rejected"), "{error}");
}

#[test]
fn wrapper_replacements_cannot_introduce_macro_definitions_or_imports() {
    let error = run_wrapper_fixture(
        "smuggled-macro",
        "#[replace_with({ macro m($x) { $x } })]\n\
         func value() -> Int { 0 }\n\n\
         value()\n",
        WRAPPERS_UNIT,
    )
    .expect_err("a replacement macro definition must be rejected");
    assert!(
        error.contains("cannot produce imports or macro definitions"),
        "{error}"
    );
    let error = run_wrapper_fixture(
        "smuggled-import",
        "#[replace_with({ use foo::{ bar } })]\n\
         func value() -> Int { 0 }\n\n\
         value()\n",
        WRAPPERS_UNIT,
    )
    .expect_err("a replacement import must be rejected");
    assert!(
        error.contains("cannot produce imports or macro definitions"),
        "{error}"
    );
}

#[test]
fn undefined_wrapper_reports_a_diagnostic() {
    let error = run_wrapper_fixture(
        "undefined",
        "#[missing_wrapper]\nfunc value() -> Int { 0 }\n\nvalue()\n",
        WRAPPERS_UNIT,
    )
    .expect_err("the unknown wrapper must be reported");
    assert!(error.contains("UndefinedWrapper"), "{error}");
}

const LENS_UNIT: &str = r#"
use package::Lexer::{ MacroInput, TokenTree }
use package::Ast::{ Decl }
use package::Syntax::{
    Syntax, SyntaxFailure, DeclWrapperResult, DeclContext, SyntaxContext, QuoteContext,
    DeclShape, view_decl, view_shape, view_name, view_body, view_with_body, view_with_name,
    view_with_name_token, syntax_text
}

func shape_label(shape: DeclShape) -> String {
    match shape {
        .func_shape -> "func",
        .init_shape -> "init",
        .struct_shape -> "struct",
        .enum_shape -> "enum",
        .protocol_shape -> "protocol",
        .extend_shape -> "extend",
        .let_shape -> "let",
        .property_shape -> "property",
        .variant_shape -> "variant",
        .typealias_shape -> "typealias",
        .effect_shape -> "effect",
        .import_shape -> "import",
        .signature_shape -> "signature",
        .associated_shape -> "associated",
        .other_shape -> "other"
    }
}

func lens_error(message: String) -> DeclWrapperResult {
    .failure(SyntaxFailure(code: "lens.error", message: message, span: 0..<0))
}

pub func shape_probe(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    if let .some(view) = view_decl(target: target, declaration: declaration) {
        let name = "?"
        if let .some(declared) = view_name(view: view) { name = declared }
        return .failure(SyntaxFailure(code: "lens.probe", message: shape_label(shape: view_shape(view: view)) + "/" + name, span: 0..<0))
    }
    lens_error(message: "target did not view")
}

pub func body_probe(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    if let .some(view) = view_decl(target: target, declaration: declaration) {
        if let .some(body) = view_body(view: view) {
            return .failure(SyntaxFailure(code: "lens.body", message: syntax_text(syntax: body), span: 0..<0))
        }
        return lens_error(message: "target has no body")
    }
    lens_error(message: "target did not view")
}

pub func constant_body(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    if let .some(view) = view_decl(target: target, declaration: declaration) {
        if let .some(value) = quote { 42 }.into_value() {
            if let .some(decl) = view_with_body(view: view, body: value, context: context).into_value() {
                return .replace(decl)
            }
        }
        return lens_error(message: "rebuild failed")
    }
    lens_error(message: "target did not view")
}

pub func rewrapped(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    if let .some(view) = view_decl(target: target, declaration: declaration) {
        if let .some(body) = view_body(view: view) {
            if let .some(rewrapped_body) = quote { { $body } }.into_value() {
                if let .some(decl) = view_with_body(view: view, body: rewrapped_body, context: context).into_value() {
                    return .replace(decl)
                }
            }
        }
        return lens_error(message: "rebuild failed")
    }
    lens_error(message: "target did not view")
}

pub func hidden_rename(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    if let .some(view) = view_decl(target: target, declaration: declaration) {
        if let .some(decl) = view_with_name(view: view, name: "hidden", context: context).into_value() {
            return .replace(decl)
        }
        return lens_error(message: "rebuild failed")
    }
    lens_error(message: "target did not view")
}

pub func alias_rename(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    if let .some(args) = input {
        if let .group(group) = args.tree {
            for child in group.children {
                if let .leaf(token) = child {
                    if let .some(view) = view_decl(target: target, declaration: declaration) {
                        if let .some(decl) = view_with_name_token(view: view, source_id: args.source_id, source: args.source, token: token, use_site: use_site).into_value() {
                            return .replace(decl)
                        }
                    }
                    return lens_error(message: "rebuild failed")
                }
            }
        }
    }
    lens_error(message: "expected an identifier argument")
}
"#;

#[test]
fn lens_views_report_shape_and_name() {
    let error = run_wrapper_fixture(
        "lens-shape",
        "#[shape_probe]\nfunc value() -> Int { 0 }\n\nstruct Holder {\n\t#[shape_probe]\n\tfunc member() -> Int { 0 }\n}\n\nvalue()\n",
        LENS_UNIT,
    )
    .expect_err("the probe reports through failures");
    assert!(error.contains("func/value"), "{error}");
    assert!(error.contains("func/member"), "{error}");
}

#[test]
fn lens_view_body_extracts_the_original_tokens() {
    let error = run_wrapper_fixture(
        "lens-body",
        "#[body_probe]\nfunc value() -> Int { 41 }\n\nvalue()\n",
        LENS_UNIT,
    )
    .expect_err("the probe reports through failures");
    assert!(error.contains("{ 41 }"), "{error}");
}

#[test]
fn lens_with_body_replaces_the_body_block() {
    let value = run_wrapper_fixture(
        "lens-with-body",
        "#[constant_body]\nfunc value() -> Int { 0 }\n\nvalue()\n",
        LENS_UNIT,
    )
    .expect("wrapper fixture");
    assert_eq!(value, "42");
}

#[test]
fn lens_rewrapping_preserves_the_extracted_body() {
    let value = run_wrapper_fixture(
        "lens-rewrap",
        "#[rewrapped]\nfunc value() -> Int { 42 }\n\nvalue()\n",
        LENS_UNIT,
    )
    .expect("wrapper fixture");
    assert_eq!(value, "42");
}

#[test]
fn lens_hygienic_rename_hides_the_binder_from_callers() {
    let error = run_wrapper_fixture(
        "lens-rename-old",
        "#[hidden_rename]\nfunc value() -> Int { 0 }\n\nvalue()\n",
        LENS_UNIT,
    )
    .expect_err("the old name is gone");
    assert!(error.contains("UndefinedName"), "{error}");
    let error = run_wrapper_fixture(
        "lens-rename-new",
        "#[hidden_rename]\nfunc value() -> Int { 0 }\n\nhidden()\n",
        LENS_UNIT,
    )
    .expect_err("the introduced name is hygienic");
    assert!(error.contains("UndefinedName"), "{error}");
}

#[test]
fn lens_spliced_name_token_is_caller_visible() {
    let value = run_wrapper_fixture(
        "lens-alias",
        "#[alias_rename(answer)]\nfunc value() -> Int { 42 }\n\nanswer()\n",
        LENS_UNIT,
    )
    .expect("wrapper fixture");
    assert_eq!(value, "42");
}

#[test]
fn imports_and_executes_a_path_dependency_wrapper() {
    let temporary = std::env::temp_dir().join(format!(
        "talk-package-wrapper-test-{}-{}",
        std::process::id(),
        TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    let dependency = temporary.join("dependency");
    let root = temporary.join("root");
    fs::create_dir_all(dependency.join("src")).expect("create dependency source");
    fs::create_dir_all(root.join("src")).expect("create root source");
    fs::write(
        dependency.join("package.tlk"),
        "Package(name: \"wrapper-lib\", version: \"0.1.0\", builds: [.lib(from: \"src/lib.tlk\")], dependencies: [])",
    )
    .expect("write dependency manifest");
    fs::write(
        dependency.join("src/lib.tlk"),
        "pub func placeholder() -> Int { 0 }\n",
    )
    .expect("write dependency library");
    fs::write(
        dependency.join("src/keep.macro.tlk"),
        r#"
use package::Lexer::{ MacroInput }
use package::Ast::{ Decl }
use package::Syntax::{ Syntax, DeclWrapperResult, DeclContext, SyntaxContext, QuoteContext }

pub func keep(input: MacroInput?, consume target: Syntax<Decl>, declaration: DeclContext, use_site: SyntaxContext, context: QuoteContext) -> DeclWrapperResult {
    .replace(target)
}
"#,
    )
    .expect("write dependency wrapper");
    fs::write(
        root.join("package.tlk"),
        "Package(name: \"root\", version: \"0.1.0\", builds: [.bin(named: \"main\", from: \"src/main.tlk\")], dependencies: [.path(package: \"wrapper-lib\", path: \"../dependency\")])",
    )
    .expect("write root manifest");
    fs::write(
        root.join("src/main.tlk"),
        "use wrapper_lib::{ keep }\n\n#[keep]\nfunc answer() -> Int { 42 }\n\nanswer()\n",
    )
    .expect("write root binary");

    PackageProject::install_at(&root, true, false).expect("install path dependency");
    let project = PackageProject::open_at(&root, true).expect("open package project");
    let executable = project
        .compile_binary(None)
        .expect("compile imported wrapper");
    let mut io = talk_vm::io::CaptureIO::default();
    let value = executable
        .run(&mut io)
        .expect("execute imported wrapper expansion");
    assert_eq!(value.as_deref(), Some("42"));
    fs::remove_dir_all(temporary).expect("remove temporary directory");
}

#[test]
fn imports_and_executes_a_path_dependency_macro() {
    let temporary = std::env::temp_dir().join(format!(
        "talk-package-macro-test-{}-{}",
        std::process::id(),
        TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    let dependency = temporary.join("dependency");
    let root = temporary.join("root");
    fs::create_dir_all(dependency.join("src")).expect("create dependency source");
    fs::create_dir_all(root.join("src")).expect("create root source");
    fs::write(
        dependency.join("package.tlk"),
        "Package(name: \"macro-lib\", version: \"0.1.0\", builds: [.lib(from: \"src/lib.tlk\")], dependencies: [])",
    )
    .expect("write dependency manifest");
    fs::write(
        dependency.join("src/lib.tlk"),
        "pub func double(value: Int) -> Int { value + value }\n",
    )
    .expect("write dependency library");
    fs::write(
        dependency.join("src/twice.macro.tlk"),
        r#"
use package::Lexer::{ MacroInput, group_contents }
use package::Ast::{ Expr }
use package::Syntax::{ SyntaxResult, SyntaxContext, QuoteContext, capture_expr }

pub func twice(input: MacroInput, use_site: SyntaxContext, context: QuoteContext) -> SyntaxResult<Expr> {
    match input.tree {
        .group(group) -> {
            let captured = capture_expr(
                source_id: input.source_id,
                source: input.source,
                input: group_contents(group: group),
                context: use_site
            )
            if let .some(value) = captured.value {
                return quote { double(value: $value) }
            }
            SyntaxResult<Expr>(value: .none, failure: captured.failure)
        },
        .leaf(token) -> unreachable
    }
}
"#,
    )
    .expect("write dependency macro");
    fs::write(
        root.join("package.tlk"),
        "Package(name: \"root\", version: \"0.1.0\", builds: [.bin(named: \"main\", from: \"src/main.tlk\")], dependencies: [.path(package: \"macro-lib\", path: \"../dependency\")])",
    )
    .expect("write root manifest");
    fs::write(
        root.join("src/main.tlk"),
        "use macro_lib::{ twice as duplicate }\n@duplicate { 21 }\n",
    )
    .expect("write root binary");

    PackageProject::install_at(&root, true, false).expect("install path dependency");
    let project = PackageProject::open_at(&root, true).expect("open package project");
    let executable = project
        .compile_binary(None)
        .expect("compile imported macro");
    let mut io = talk_vm::io::CaptureIO::default();
    let value = executable
        .run(&mut io)
        .expect("execute imported macro expansion");
    assert_eq!(value.as_deref(), Some("42"));
    fs::remove_dir_all(temporary).expect("remove temporary directory");
}
