use std::fs;
use std::path::Path;

#[test]
fn generated_wit_contains_expected_definitions() {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let wit_path = Path::new(manifest_dir).join("index.wit");
    let content = fs::read_to_string(&wit_path).expect("read index.wit");
    assert!(content.contains("record highlight-token"), "missing highlight token record");
    assert!(content.contains("ir: func(code: string) -> string"), "missing ir func");
    assert!(content.contains("run: func(code: string)"), "missing run func");
    assert!(content.contains("higlight: func(code: string) -> list<highlight-token>"), "missing higlight func");
}

