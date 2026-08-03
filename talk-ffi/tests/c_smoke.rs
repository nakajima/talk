//! Drive the C smoke client: build the host static library, compile
//! `tests/smoke.c` against the public header, link, and run it. This
//! proves the C interface independently of Swift.

use std::path::PathBuf;
use std::process::Command;

#[test]
fn c_smoke_client_links_and_runs() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = manifest_dir
        .parent()
        .expect("talk-ffi has a workspace parent");

    let status = Command::new(env!("CARGO"))
        .args(["build", "-p", "talk-ffi", "--locked"])
        .current_dir(workspace_root)
        .status()
        .expect("cargo build -p talk-ffi runs");
    assert!(status.success(), "cargo build -p talk-ffi succeeds");

    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let output = std::env::temp_dir().join(format!("talk-ffi-smoke-{}", std::process::id()));
    let status = Command::new(&cc)
        .arg(manifest_dir.join("tests/smoke.c"))
        .arg("-I")
        .arg(manifest_dir.join("include"))
        .arg(workspace_root.join("target/debug/libtalk_ffi.a"))
        .args(["-lpthread", "-ldl", "-lm"])
        .arg("-o")
        .arg(&output)
        .status()
        .expect("the host C compiler runs");
    assert!(status.success(), "the smoke client compiles and links");

    let status = Command::new(&output)
        .status()
        .expect("the smoke client runs");
    assert!(status.success(), "the smoke client passes");
}
