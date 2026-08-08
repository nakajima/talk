use talk::compiling::driver::{Driver, DriverConfig, Source};

const FIXTURE: &str = r#"
func report(value: Int) -> Int {
    print(value + 1)
    value
}

report(value: 42)
"#;

const CAPTURE_FIXTURE: &str = r#"func makeCounter() {
	let count = 0

	return func() {
		count = count + 1
		count
	}
}

let counter = makeCounter()
counter()
counter()
counter()
"#;

fn typed(source: &str) -> Driver<talk::compiling::driver::Typed> {
    Driver::new(
        vec![Source::in_memory("fixture.tlk".into(), source)],
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
    let rendered = typed(FIXTURE)
        .render_mir(None, true, true)
        .expect("fixture renders optimized debug MIR");

    assert!(rendered.contains("// source fixture.tlk:"));
    assert!(rendered.contains("// locals:"));
    assert!(rendered.contains("value"));
    assert!(rendered.contains(": value + 1"));
    assert!(rendered.contains(": print(value + 1)"));
    assert!(rendered.contains("// generated MIR: block-exit cleanup of"));
    assert!(rendered.contains(", created by "));
    assert!(rendered.contains("// generated MIR: program entry and global teardown wrapper"));
    assert!(!rendered.contains("generated MIR (no direct source span)"));
}

#[test]
fn generated_closure_prologue_names_the_capture_and_closure() {
    let rendered = typed(CAPTURE_FIXTURE)
        .render_mir(None, true, true)
        .expect("capture fixture renders optimized debug MIR");

    assert!(rendered.contains("generated MIR: bind capture L0(count) from env[0] for closure fn"));
}

#[test]
fn ordinary_render_does_not_include_debug_metadata() {
    let rendered = typed(FIXTURE)
        .render_mir(None, true, false)
        .expect("fixture renders optimized MIR");

    assert!(!rendered.contains("// source fixture.tlk:"));
    assert!(!rendered.contains("// locals:"));
}
