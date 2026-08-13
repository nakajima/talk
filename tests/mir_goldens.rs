//! Unoptimized MIR goldens, one per construct family (ADR 0057
//! slice 4): a lowering refactor that changes emitted MIR bisects here,
//! at the MIR level, instead of surfacing as "program X printed the
//! wrong number" three suites later. Regenerate deliberately with
//! `TALK_UPDATE_MIR_GOLDENS=1 cargo test --test mir_goldens`.

use talk::compiling::driver::{Driver, DriverConfig, Source, Typed};

fn typed(source: &str) -> Driver<Typed> {
    Driver::new(
        vec![Source::in_memory("golden.tlk".into(), source)],
        DriverConfig::new("golden").executable(),
    )
    .parse()
    .expect("golden parses")
    .resolve_names()
    .expect("golden resolves")
    .type_check()
}

fn check_golden(name: &str, source: &str) {
    let rendered = typed(source)
        .render_mir(None, false, false)
        .unwrap_or_else(|error| panic!("{name} renders MIR: {error}"));
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/mir/expected")
        .join(format!("{name}.mir"));
    if std::env::var_os("TALK_UPDATE_MIR_GOLDENS").is_some() {
        std::fs::create_dir_all(path.parent().expect("expected dir")).expect("mkdir");
        std::fs::write(&path, &rendered).expect("write golden");
        return;
    }
    let expected = std::fs::read_to_string(&path).unwrap_or_else(|_| {
        panic!(
            "missing golden {}; run TALK_UPDATE_MIR_GOLDENS=1 cargo test --test mir_goldens",
            path.display()
        )
    });
    assert_eq!(
        rendered,
        expected,
        "{name}: unoptimized MIR drifted from its golden; if intentional, regenerate with \
         TALK_UPDATE_MIR_GOLDENS=1 cargo test --test mir_goldens"
    );
}

macro_rules! golden {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            check_golden(stringify!($name), $source);
        }
    };
}

golden!(
    arithmetic_and_calls,
    "func add(a: Int, b: Int) -> Int { a + b }\nprint(add(a: 1, b: 2))"
);

golden!(
    string_values,
    "let name = \"world\"\nprint(\"hello \" + name)"
);

golden!(
    struct_construction_and_fields,
    "struct Point {\n\tlet x: Int\n\tlet y: Int\n}\nlet p = Point(x: 1, y: 2)\nprint(p.x + p.y)"
);

golden!(
    enum_construction_and_match,
    "enum Shape {\n\tcase circle(Int)\n\tcase square(Int)\n}\nlet s = Shape.circle(4)\nlet area = match s {\n\t.circle(r) -> r * r,\n\t.square(w) -> w * w\n}\nprint(area)"
);

golden!(
    optional_propagation,
    "func find(v: Int) -> Optional<Int> {\n\tif v > 0 { return .some(v) }\n\treturn .none\n}\nfunc doubled(v: Int) -> Optional<Int> {\n\tlet found = find(v: v)?\n\treturn .some(found * 2)\n}\nprint(doubled(v: 3))"
);

golden!(
    closures_with_cells,
    "func makeCounter() {\n\tlet count = 0\n\treturn func() {\n\t\tcount = count + 1\n\t\tcount\n\t}\n}\nlet counter = makeCounter()\ncounter()\nprint(counter())"
);

golden!(
    match_with_guards_and_binders,
    "let value = 7\nlet label = match value {\n\t0 -> \"zero\",\n\tn -> \"nonzero\"\n}\nprint(label)"
);

golden!(
    for_loops,
    "let total = 0\nfor i in 0..<5 {\n\ttotal = total + i\n}\nprint(total)"
);

golden!(
    arrays_and_subscripts,
    "let xs = [1, 2, 3]\nprint(xs[1])\nprint(xs.count)"
);

golden!(
    borrowed_parameters,
    "struct Wallet {\n\tlet balance: Int\n}\nfunc read(w: &Wallet) -> Int { w.balance }\nlet wallet = Wallet(balance: 5)\nprint(read(w: wallet))"
);

golden!(
    consuming_parameters_and_drop_glue,
    "struct Box {\n\tlet label: String\n}\nfunc eat(consume b: Box) -> Int { 1 }\nlet box = Box(label: \"x\")\nprint(eat(b: box))"
);

golden!(
    mut_writeback,
    "struct Counter {\n\tlet value: Int\n\tmut func bump() {\n\t\tself.value = self.value + 1\n\t}\n}\nlet c = Counter(value: 0)\nc.bump()\nprint(c.value)"
);

golden!(
    protocol_witness_dispatch,
    "protocol Greeter {\n\tfunc greet() -> String\n}\nstruct En {}\nextend En: Greeter {\n\tfunc greet() -> String { \"hi\" }\n}\nfunc run<T: Greeter>(g: &T) -> String { g.greet() }\nprint(run(g: En()))"
);

golden!(
    existential_pack_and_dispatch,
    "protocol Greeter {\n\tfunc greet() -> String\n}\nstruct En {}\nextend En: Greeter {\n\tfunc greet() -> String { \"hi\" }\n}\nlet boxed: any Greeter = En()\nprint(boxed.greet())"
);

golden!(
    effect_handlers,
    "effect 'ask() -> Int\n#handle 'ask { 'continue 41 }\nfunc question() 'ask -> Int {\n\t'ask() + 1\n}\nprint(question())"
);

golden!(
    generic_identity_and_instantiation,
    "func identity<T>(consume value: T) -> T { value }\nprint(identity(value: 3))\nprint(identity(value: \"s\"))"
);

golden!(
    tuples_and_projection,
    "let pair = (1, \"two\")\nprint(pair.0)\nprint(pair.1)"
);

golden!(
    derived_show_and_equality,
    "struct P {\n\tlet x: Int\n}\nlet a = P(x: 1)\nlet b = P(x: 1)\nprint(a == b)\nprint(a)"
);

golden!(
    globals_and_initialization_order,
    "let base = 10\nfunc offset() -> Int { base + 1 }\nlet derived = offset()\nprint(derived)"
);

golden!(
    string_match_arms,
    "let command = \"north\"\nlet reply = match command {\n\t\"north\" -> \"up\",\n\t_ -> \"?\"\n}\nprint(reply)"
);
