use std::path::Path;

fn main() {
    println!("cargo:rerun-if-changed=src/lib.rs");
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let wit = cargo_witgen::Witgen::gen_static_from_path(Path::new(&manifest_dir))
        .expect("generate wit");
    std::fs::write(Path::new(&manifest_dir).join("index.wit"), wit)
        .expect("write index.wit");
}
