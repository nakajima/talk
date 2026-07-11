use std::process::Command;

#[test]
fn talk_source_tests_pass() {
    let output = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("test")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("run `talk test`");

    assert!(
        output.status.success(),
        "`talk test` failed with {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}
