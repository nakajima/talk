use talk::compiling::driver::{Driver, DriverConfig, Source};

const FIXTURE: &str = r#"
func report(value: Int) -> Int {
    print(value + 1)
    value
}

report(value: 42)
"#;

fn typed() -> Driver<talk::compiling::driver::Typed> {
    Driver::new(
        vec![Source::in_memory("fixture.tlk".into(), FIXTURE)],
        DriverConfig::new("fixture").executable(),
    )
    .parse()
    .expect("fixture parses")
    .resolve_names()
    .expect("fixture resolves")
    .type_check()
}

#[test]
fn optimized_render_preserves_source_debug_metadata() {
    let rendered = typed()
        .render_mir(None, true, true)
        .expect("fixture renders optimized debug MIR");

    assert!(rendered.contains("// source fixture.tlk:"));
    assert!(rendered.contains("// locals:"));
    assert!(rendered.contains("value"));
    assert!(rendered.contains(": value + 1"));
    assert!(rendered.contains(": print(value + 1)"));
}

#[test]
fn ordinary_render_does_not_include_debug_metadata() {
    let rendered = typed()
        .render_mir(None, true, false)
        .expect("fixture renders optimized MIR");

    assert!(!rendered.contains("// source fixture.tlk:"));
    assert!(!rendered.contains("// locals:"));
}
