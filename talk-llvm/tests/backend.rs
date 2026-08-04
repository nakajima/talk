//! Differential coverage for the external LLVM backend.

use std::path::{Path, PathBuf};
use std::process::Command;

use talk::compiling::driver::{Driver, DriverConfig, Source};
use talk_vm::io::CaptureIO;

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
    if let Some(rendered) = executable.run(&mut io).expect("VM runs") {
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

/// The export list every library-mode test emits from the shared
/// fixture in tests/native-library: scalar, String, aggregate, effect,
/// and failure cases.
const LIBRARY_EXPORTS: [&str; 9] = [
    "double", "crash", "greet", "shout", "length", "pair", "total", "handled", "leave",
];

fn library_fixtures() -> PathBuf {
    repo_root().join("tests/native-library")
}

/// The host compiler for harness translation units, resolved the way the
/// backend binary resolves its own driver.
fn clang() -> String {
    std::env::var("CLANG").unwrap_or_else(|_| "clang".to_string())
}

/// Emit a library through the CLI, keeping the .ll and runtime C next to
/// the shared object so harnesses can link statically.
fn build_library(dir: &Path, program: &Path, prefix: &str) -> (PathBuf, PathBuf) {
    let object = dir.join(format!("lib{prefix}.so"));
    let header = dir.join(format!("{prefix}.h"));
    let manifest = dir.join(format!("{prefix}.manifest"));
    let mut arguments = vec!["build"];
    for export in LIBRARY_EXPORTS {
        arguments.extend(["--export", export]);
    }
    arguments.extend(["--allow-effect", "io", "--prefix", prefix]);
    let header_path = header.to_str().expect("UTF-8 header path").to_string();
    let manifest_path = manifest.to_str().expect("UTF-8 manifest path").to_string();
    arguments.extend(["--header", &header_path, "--manifest", &manifest_path]);
    arguments.extend([
        "--keep",
        program.to_str().expect("UTF-8 program path"),
        "-o",
        object.to_str().expect("UTF-8 output path"),
    ]);
    let output = backend(&arguments);
    assert!(
        output.status.success(),
        "LLVM library build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(object.exists(), "the shared object was not produced");
    let manifest_text = std::fs::read_to_string(&manifest).expect("read manifest");
    for export in LIBRARY_EXPORTS {
        assert!(
            manifest_text.contains(&format!("{export}\t{prefix}_{export}\n")),
            "manifest is missing {export}:\n{manifest_text}"
        );
    }
    (
        object.with_extension("ll"),
        object.with_extension("runtime.c"),
    )
}

fn compile_harness(dir: &Path, name: &str, sources: &[&Path]) -> PathBuf {
    let binary = dir.join(name);
    let mut command = Command::new(clang());
    command.args(["-O2", "-std=c11", "-I"]).arg(dir);
    for source in sources {
        command.arg(source);
    }
    let output = command
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run clang");
    assert!(
        output.status.success(),
        "harness did not compile:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    binary
}

/// ADR 0048 library mode end to end on the LLVM backend, through the
/// same shared fixture and harness the C backend runs: the versioned
/// convention, the lifecycle, trap and exit containment, and agreement
/// with the VM oracle on scalar, String, aggregate, effect, and failure
/// cases.
#[test]
fn library_artifact_serves_the_shared_c_harness() {
    let dir = scratch("library");
    let program = library_fixtures().join("library.tlk");
    let oracle = interpreted(&program, Some("bench"));
    let oracle = String::from_utf8(oracle).expect("oracle output is UTF-8");
    let oracle: Vec<&str> = oracle.split_whitespace().collect();
    assert_eq!(oracle.len(), 4, "the VM oracle prints four values");
    let (ir, runtime) = build_library(&dir, &program, "mylib");
    let harness = library_fixtures().join("harness.c");
    let binary = compile_harness(&dir, "harness.bin", &[&harness, &ir, &runtime]);
    let run = Command::new(&binary)
        .args(&oracle)
        .output()
        .expect("run harness");
    assert!(
        run.status.success(),
        "harness failed (exit {:?}):\n{}",
        run.status.code(),
        String::from_utf8_lossy(&run.stderr)
    );
}

/// The acceptance criterion from ADR 0048: two generated libraries with
/// distinct prefixes link into one process without symbol collisions,
/// and both serve calls.
#[test]
fn two_libraries_with_distinct_prefixes_link_into_one_process() {
    let dir = scratch("two_libraries");
    let program = library_fixtures().join("library.tlk");
    let (one_ir, one_runtime) = build_library(&dir, &program, "one");
    let (two_ir, two_runtime) = build_library(&dir, &program, "two");
    let harness = dir.join("pair.c");
    std::fs::write(
        &harness,
        r#"
#include "one.h"
#include "two.h"

int main(void) {
    if (one_init() != ONE_OK) return 10;
    if (two_init() != TWO_OK) return 11;
    one_value a1[1]; one_value r1;
    two_value a2[1]; two_value r2;
    a1[0] = one_int(21);
    a2[0] = two_int(10);
    if (one_double(&r1, a1, 1) != ONE_OK) return 12;
    if (two_double(&r2, a2, 1) != TWO_OK) return 13;
    if (one_value_int(r1) != 42) return 14;
    if (two_value_int(r2) != 20) return 15;
    one_teardown();
    two_teardown();
    return 0;
}
"#,
    )
    .expect("write harness");
    let binary = compile_harness(
        &dir,
        "pair.bin",
        &[&harness, &one_ir, &one_runtime, &two_ir, &two_runtime],
    );
    let run = Command::new(&binary).output().expect("run harness");
    assert!(
        run.status.success(),
        "pair harness failed (exit {:?}):\n{}",
        run.status.code(),
        String::from_utf8_lossy(&run.stderr)
    );
}
