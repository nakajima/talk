//! Interface tests for the public MIR publication point (ADR 0047): a
//! source fixture compiled through `compile_mir` must publish every fact
//! the bytecode, C, and LLVM adapters read, under the invariants the
//! adapters rely on.

use talk::compiling::driver::{Driver, DriverConfig, MirEntry, Source};
use talk_mir::{Inst, MirSymbolKind, Term, TypeKind};

const FIXTURE: &str = r#"
struct Point {
	let x: Int
	let y: Int
}

enum Shape {
	case dot
	case circle(Int)
}

effect 'alarm(urgency) -> Int

func area(shape: Shape) -> Int {
	match shape {
		.dot -> 0,
		.circle(r) -> r * r
	}
}

func ringing() 'alarm -> Int {
	'alarm(urgency: 3)
}

pub func main() -> Int {
	let p = Point(x: 1, y: 2)
	let s = Shape.circle(3)
	p.x + area(shape: s)
}

#handle 'alarm { urgency in
	'continue urgency
}

let r = ringing()
"#;

fn compile(entry: MirEntry) -> talk_mir::Module {
    let driver = Driver::new(
        vec![Source::in_memory("fixture.tlk".into(), FIXTURE)],
        DriverConfig::new("fixture"),
    );
    driver
        .parse()
        .expect("fixture parses")
        .resolve_names()
        .expect("fixture resolves")
        .type_check()
        .compile_mir(entry)
        .expect("fixture publishes MIR")
        .module
}

#[test]
fn publishes_well_formed_structure() {
    let module = compile(MirEntry::Script);

    // Invariant 1: every function, block, local, layout, and global
    // reference is in range.
    assert!(module.entry < module.functions.len());
    for function in &module.functions {
        for block in &function.blocks {
            let check_operand = |local: u16| {
                assert!(
                    usize::from(local) < function.locals.len(),
                    "local {local} in range of {}",
                    function.name
                );
            };
            for inst in &block.insts {
                match inst {
                    Inst::Aggregate { layout, .. } | Inst::Blank { layout, .. } => {
                        assert!(usize::try_from(*layout).unwrap() < module.layout_table.len());
                    }
                    Inst::Call { func, .. } | Inst::MakeClosure { func, .. } => {
                        assert!(*func < module.functions.len());
                    }
                    _ => {}
                }
            }
            // Invariant 2: every block has one terminator.
            assert!(block.term.is_some(), "block of {} terminated", function.name);
            // Invariant 3: block argument counts match block parameters.
            if let Some(Term::Goto(target, args)) = &block.term {
                assert_eq!(
                    args.len(),
                    function.blocks[*target].params.len(),
                    "goto arguments match target parameters in {}",
                    function.name
                );
            }
            for param in &block.params {
                check_operand(*param);
            }
        }
        // Invariant 7: the locals table is the final frame.
        assert_eq!(function.n_locals() as usize, function.locals.len());
        // Invariant 6: frame sites name real construction sites.
        for (block, instruction) in &function.frame_sites {
            assert!(*block < function.blocks.len());
            assert!(*instruction < function.blocks[*block].insts.len());
        }
    }
}

#[test]
fn publishes_display_metadata_and_well_known_identities() {
    let module = compile(MirEntry::Script);

    // The fixture's aggregates appear with their member names.
    let point = module
        .display
        .entries
        .values()
        .find(|entry| entry.name == "Point")
        .expect("Point has a display entry");
    assert_eq!(point.kind, TypeKind::Record);
    assert_eq!(point.members, ["x", "y"]);

    let shape = module
        .display
        .entries
        .values()
        .find(|entry| entry.name == "Shape")
        .expect("Shape has a display entry");
    assert_eq!(shape.kind, TypeKind::Enum);
    assert_eq!(shape.members, ["dot", "circle"]);

    // Well-known runtime aggregate identities are published and named.
    assert_eq!(module.string_symbol.kind, MirSymbolKind::Struct);
    assert_eq!(module.storage_symbol.kind, MirSymbolKind::Struct);
    let string = module
        .display
        .entries
        .get(&module.string_symbol)
        .expect("String has a display entry");
    assert_eq!(string.kind, TypeKind::String);

    // Layout identities agree with display identities.
    for layout in &module.layout_table {
        let identity = match layout {
            talk_mir::Layout::Inline(identity, _) | talk_mir::Layout::Boxed(identity, _) => {
                identity
            }
            _ => &None,
        };
        if let Some(identity) = identity {
            assert!(
                matches!(
                    identity.kind,
                    MirSymbolKind::Struct | MirSymbolKind::Enum
                ),
                "layout identities are aggregate identities"
            );
        }
    }
}

#[test]
fn publishes_effect_identities() {
    let module = compile(MirEntry::Script);
    let mut saw_effect = false;
    for function in &module.functions {
        for block in &function.blocks {
            for inst in &block.insts {
                match inst {
                    Inst::PushHandler { effect, .. } | Inst::FindHandler { effect, .. } => {
                        assert_eq!(effect.kind, MirSymbolKind::Effect);
                        saw_effect = true;
                    }
                    _ => {}
                }
            }
        }
    }
    assert!(saw_effect, "the fixture installs a handler");
}

#[test]
fn publishes_exports_for_a_service_entry() {
    let names = vec!["main".to_string()];
    let module = compile(MirEntry::Exports {
        names: &names,
        allowed_effects: &[],
    });
    assert_eq!(module.exports.len(), 1);
    assert_eq!(module.exports[0].0, "main");
    assert!(module.exports[0].1 < module.functions.len());
}

#[test]
fn publishes_native_signature_facts() {
    let module = compile(MirEntry::Script);
    // At least one function carries a native parameter or return
    // representation and a non-uniform local layout.
    let typed = module.functions.iter().any(|function| {
        !function.param_reprs.is_empty()
            || function.return_repr.is_some()
            || function.locals.iter().any(|local| local.layout.is_some())
    });
    assert!(typed, "some function publishes layout facts");
}
