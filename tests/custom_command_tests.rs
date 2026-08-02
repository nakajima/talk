use std::path::{Path, PathBuf};
use std::process::Command;

fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::create_dir_all(&dir).expect("scratch directory");
    dir
}

#[cfg(unix)]
#[test]
fn unknown_subcommands_delegate_to_a_path_executable() {
    use std::os::unix::fs::PermissionsExt as _;

    let dir = scratch("external_command");
    let plugin = dir.join("talk-example");
    std::fs::write(&plugin, "#!/bin/sh\nprintf '%s\\n' \"$@\"\nexit 23\n").expect("write plugin");
    let mut permissions = std::fs::metadata(&plugin)
        .expect("plugin metadata")
        .permissions();
    permissions.set_mode(0o755);
    std::fs::set_permissions(&plugin, permissions).expect("make plugin executable");

    let output = Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(["example", "one", "--flag", "two"])
        .env("PATH", &dir)
        .output()
        .expect("run talk");
    assert_eq!(output.status.code(), Some(23));
    assert_eq!(output.stdout, b"one\n--flag\ntwo\n");
}

#[test]
fn a_missing_external_command_names_the_expected_executable() {
    let output = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("definitely-not-installed")
        .env("PATH", scratch("empty_path"))
        .output()
        .expect("run talk");
    assert!(!output.status.success());
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains("talk-definitely-not-installed"), "{error}");
}
