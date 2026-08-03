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
    let value = executable.run(&mut io).expect("execute imported macro expansion");
    assert_eq!(value.as_deref(), Some("42"));
    fs::remove_dir_all(temporary).expect("remove temporary directory");
}
