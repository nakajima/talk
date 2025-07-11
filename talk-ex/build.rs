use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=src/lib.rs");
    println!("cargo:rerun-if-changed=wit/host.wit");
    Command::new("cargo")
        .args(&["component", "bindings"])
        .spawn()
        .unwrap();
}
