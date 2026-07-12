use std::io::Write;
use std::process::{Command, Stdio};

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

#[test]
fn format_does_not_add_a_blank_line_at_eof() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("format")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("run `talk format`");

    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(b"let x=1\n")
        .expect("write source");

    let output = child.wait_with_output().expect("read formatter output");
    assert!(output.status.success(), "`talk format` failed");
    assert_eq!(output.stdout, b"let x = 1\n");
}
