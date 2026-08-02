//! Differential coverage for the external LLVM backend.

use std::path::{Path, PathBuf};
use std::process::Command;

use talk::compiling::driver::{Driver, DriverConfig, Source, execute_module};
use talk_runtime::io::CaptureIO;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .to_path_buf()
}

fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::create_dir_all(&dir).expect("scratch directory");
    dir
}

fn backend(arguments: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_talk-llvm"))
        .args(arguments)
        .output()
        .expect("run talk-llvm")
}

fn compile(dir: &Path, program: &Path, entry: Option<&str>) -> PathBuf {
    let binary = dir.join("program.bin");
    let mut arguments = vec!["build"];
    if let Some(entry) = entry {
        arguments.extend(["--entry", entry]);
    }
    arguments.push(program.to_str().expect("UTF-8 program path"));
    arguments.extend(["-o", binary.to_str().expect("UTF-8 binary path")]);
    let output = backend(&arguments);
    assert!(
        output.status.success(),
        "LLVM build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    binary
}

fn interpreted(program: &Path, entry: Option<&str>) -> Vec<u8> {
    let parsed = Driver::new(
        vec![Source::from(program.to_path_buf())],
        DriverConfig::new("Main"),
    )
    .parse()
    .expect("program parses");
    let resolved = parsed.resolve_names().expect("program resolves");
    let typed = resolved.type_check();
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let executable = typed.compile_executable(entry).expect("VM compiles");
    let mut io = CaptureIO::default();
    if let Some(rendered) = execute_module(&executable, &mut io).expect("VM runs") {
        io.out.extend_from_slice(rendered.as_bytes());
        io.out.push(b'\n');
    }
    io.out
}

fn run(binary: &Path) -> std::process::Output {
    Command::new(binary).output().expect("run LLVM executable")
}

#[test]
fn package_build_uses_the_selected_binary_and_locked_dependencies() {
    let dir = scratch("package_build");
    if dir.exists() {
        std::fs::remove_dir_all(&dir).expect("remove stale package fixture");
    }
    let dependency = dir.join("dependency");
    let root = dir.join("root");
    std::fs::create_dir_all(dependency.join("src")).expect("dependency source directory");
    std::fs::create_dir_all(root.join("src")).expect("root source directory");
    std::fs::write(
        dependency.join("package.tlk"),
        "Package(name: \"llvm-test-dependency\", version: \"0.1.0\", builds: [.lib(from: \"src/lib.tlk\")], dependencies: [])",
    )
    .expect("dependency manifest");
    std::fs::write(
        dependency.join("src/lib.tlk"),
        "pub func answer() -> Int { 42 }\n",
    )
    .expect("dependency source");
    std::fs::write(
        root.join("package.tlk"),
        "Package(name: \"llvm-test-root\", version: \"0.1.0\", builds: [.bin(named: \"app\", from: \"src/main.tlk\"), .bin(named: \"other\", from: \"src/other.tlk\")], dependencies: [.path(package: \"llvm-test-dependency\", path: \"../dependency\")])",
    )
    .expect("root manifest");
    std::fs::write(
        root.join("src/main.tlk"),
        "use llvm_test_dependency::{ answer }\nprint(answer())\n",
    )
    .expect("root source");
    std::fs::write(root.join("src/other.tlk"), "print(0)\n").expect("other binary source");
    talk::compiling::package::PackageProject::install_at(&root, true, false)
        .expect("install package graph");

    let binary = dir.join("package.bin");
    let output = Command::new(env!("CARGO_BIN_EXE_talk-llvm"))
        .args(["build", "--offline", "--bin", "app", "-o"])
        .arg(&binary)
        .current_dir(root.join("src"))
        .output()
        .expect("build package");
    assert!(
        output.status.success(),
        "package build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let native = run(&binary);
    assert!(
        native.status.success(),
        "package executable failed:\n{}",
        String::from_utf8_lossy(&native.stderr)
    );
    assert_eq!(native.stdout, b"42\n");

    std::fs::remove_dir_all(dir).expect("remove package fixture");
}

#[test]
fn command_emits_language_functions_and_native_scalar_ops() {
    let dir = scratch("module_shape");
    let program = dir.join("program.tlk");
    std::fs::write(
        &program,
        "pub func bench() -> Int {\n\tlet x = 40\n\tx + 2\n}\n",
    )
    .expect("write program");

    let output = backend(&[
        "--entry",
        "bench",
        program.to_str().expect("UTF-8 program path"),
    ]);
    assert!(
        output.status.success(),
        "talk-llvm failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    assert!(ir.contains("define void @talk_fn"));
    assert!(ir.contains(" add i64 "));
    assert!(ir.contains("define void @talk_llvm_dispatch"));
}

#[test]
fn effects_closures_and_cells_agree_with_the_vm() {
    let dir = scratch("effects_closures_cells");
    let program = dir.join("program.tlk");
    std::fs::write(
        &program,
        "effect 'step(n: Int) -> Int\n\
         func run(n: Int) 'step -> Int { 'step(n: n) + 1 }\n\
         func make_counter() {\n\
         \tlet total = 0\n\
         \treturn func() { total = total + 1; total }\n\
         }\n\
         pub func bench() -> Int {\n\
         \tlet counter = make_counter()\n\
         \tcounter()\n\
         \t#handle 'step { n in 'continue n * 2 }\n\
         \tcounter() + run(n: 7)\n\
         }\n",
    )
    .expect("write program");

    let expected = interpreted(&program, Some("bench"));
    let binary = compile(&dir, &program, Some("bench"));
    let native = run(&binary);
    assert!(
        native.status.success(),
        "LLVM executable failed:\n{}",
        String::from_utf8_lossy(&native.stderr)
    );
    assert_eq!(native.stdout, expected);
}

#[test]
fn benchmark_corpus_matches_its_frozen_output() {
    let root = repo_root().join("bench");
    let mut programs: Vec<_> = std::fs::read_dir(&root)
        .expect("bench directory")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "tlk"))
        .collect();
    programs.sort();
    assert!(programs.len() >= 8, "benchmark corpus shrank");

    for program in programs {
        let name = program
            .file_stem()
            .and_then(|name| name.to_str())
            .expect("program name");
        let expected =
            std::fs::read(root.join(format!("expected/{name}.stdout"))).expect("frozen output");
        let dir = scratch(&format!("bench_{name}"));
        let output = run(&compile(&dir, &program, None));
        assert!(
            output.status.success(),
            "{name}: LLVM executable failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, expected, "{name}: LLVM output diverged");
    }
}

#[test]
fn complete_program_corpus_agrees_with_the_vm() {
    let root = repo_root().join("tests/programs");
    let mut programs: Vec<_> = std::fs::read_dir(&root)
        .expect("program corpus")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "tlk"))
        .collect();
    programs.sort();
    assert!(programs.len() >= 19, "program corpus shrank");

    for program in programs {
        let name = program
            .file_stem()
            .and_then(|name| name.to_str())
            .expect("program name");
        let expected = interpreted(&program, None);
        let dir = scratch(&format!("program_{name}"));
        let native = run(&compile(&dir, &program, None));
        assert!(
            native.status.success(),
            "{name}: LLVM executable failed:\n{}",
            String::from_utf8_lossy(&native.stderr)
        );
        assert_eq!(
            native.stdout, expected,
            "{name}: LLVM output diverged from the VM"
        );
    }
}
