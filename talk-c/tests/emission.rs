//! Focused emitted-C structure tests: hand-built MIR fixtures fed
//! straight through the crate interface (`talk-mir` data only — the
//! crate sees no compiler internals).
//!
//! Each fixture stamps by hand the facts the compiler's frame shaping
//! publishes on the finalized module (ADR 0045): per-local layout
//! classes and frame-locality, per-site construction substrates,
//! parameter representations, and return representations. The recorded
//! facts are exactly what the real pipeline's shaping passes produce
//! for these programs; the shaping judgments themselves are tested
//! where the passes live (`mir/build/layout.rs`, `mir/build/escape.rs`
//! in the compiler crate). What these tests pin is the emitter's half
//! of the contract: given these published facts, this is the C.

use talk_c::emit;
use talk_mir::layout::{FieldRepr, Layout, LayoutId, ParamRepr, Shape, SlotKind};
use talk_mir::{
    BlockData, Constant, Function, Inst, LocalInfo, MirSymbol, Module as Program, Operand, Term,
};

fn sym(id: u32) -> MirSymbol {
    MirSymbol {
        kind: talk_mir::MirSymbolKind::Struct,
        module: 9,
        local: id,
    }
}

fn flat_pair(symbol: MirSymbol) -> Layout {
    Layout::Inline(
        Some(symbol),
        Shape::Product {
            width: 2,
            offsets: vec![0, 1],
            reprs: vec![FieldRepr::Slot(SlotKind::Int); 2],
            kinds: vec![SlotKind::Int; 2],
        },
    )
}

fn function(arity: u16, n_locals: u16, insts: Vec<Inst>, term: Term) -> Function {
    Function {
        debug_names: None,
        frame_sites: Default::default(),
        param_reprs: Vec::new(),
        return_repr: None,
        name: String::new(),
        arity,
        locals: LocalInfo::uniform(n_locals),
        blocks: vec![BlockData {
            debug: None,
            params: Vec::new(),
            insts,
            term: Some(term),
        }],
    }
}

/// Stamps the published frame facts the compiler's shaping passes
/// would derive for the fixture: each local's `(layout class,
/// frame-local)` pair and the frame-local construction sites as
/// `(block, instruction)`.
fn stamp(function: &mut Function, locals: &[(Option<LayoutId>, bool)], sites: &[(usize, usize)]) {
    for (info, (layout, frame_local)) in function.locals.iter_mut().zip(locals) {
        info.layout = *layout;
        info.frame_local = *frame_local;
    }
    function.frame_sites = sites.iter().copied().collect();
}

fn module(
    functions: Vec<Function>,
    layout_table: Vec<Layout>,
    exports: Vec<(String, usize)>,
) -> Program {
    Program {
        debug_files: Vec::new(),
        functions,
        entry: 0,
        global_slots: 0,
        exports,
        layout_table,
        display: Default::default(),
        string_symbol: MirSymbol::STRING,
        storage_symbol: MirSymbol::STORAGE,
    }
}

fn emitted(functions: Vec<Function>, layout_table: Vec<Layout>) -> String {
    emit(&module(functions, layout_table, Vec::new()))
        .expect("emission")
        .source
}

#[test]
fn native_products_store_members_and_box_at_boundaries() {
    let pair = sym(1);
    let mut entry = function(
        0,
        4,
        vec![
            Inst::Aggregate {
                tag: 0,
                dest: 1,
                layout: 0,
                args: vec![
                    Operand::Const(Constant::Int(1)),
                    Operand::Const(Constant::Int(2)),
                ],
            },
            Inst::Field {
                dest: 2,
                src: Operand::Local(1),
                container: 0,
                offset: 0,
                member: None,
            },
            Inst::Call {
                dest: 3,
                func: 1,
                args: vec![Operand::Local(1)],
                unwind: None,
            },
        ],
        Term::Return(Operand::Local(2)),
    );
    // The aggregate classes its local, and the callee only reads its
    // parameter — nothing escapes, so the value is frame-local and its
    // boxing may reuse the frame buffer.
    stamp(
        &mut entry,
        &[(None, true), (Some(0), true), (None, false), (None, false)],
        &[(0, 0)],
    );
    let mut callee = function(
        1,
        2,
        Vec::new(),
        Term::Return(Operand::Const(Constant::Unit)),
    );
    stamp(&mut callee, &[(None, false), (None, true)], &[]);
    let out = emitted(vec![entry, callee], vec![flat_pair(pair)]);
    // The construction allocates nothing: native storage, member
    // stores, and a direct member read.
    assert!(out.contains("TalkL0 x1;"), "{out}");
    assert!(out.contains("x1.m0 = talk_int(INT64_C(1)).v.i;"), "{out}");
    assert!(out.contains("x1.m1 = talk_int(INT64_C(2)).v.i;"), "{out}");
    assert!(out.contains("l[2] = talk_int(x1.m0);"), "{out}");
    // Crossing into the uniform call boundary reabstracts — into the
    // local's frame buffer, since the callee does not leak it.
    assert!(out.contains("talk_box_l0_in(fx1, x1)"), "{out}");
    assert!(out.contains("unsigned char fx1[sizeof(TalkAgg)"), "{out}");
    assert!(
        out.contains("static inline TalkValue talk_box_l0(TalkL0 v)"),
        "{out}"
    );
}

#[test]
fn spliced_fields_copy_native_sources_and_unbox_uniform_ones() {
    let inner = sym(1);
    let outer = sym(2);
    let table = vec![
        flat_pair(inner),
        Layout::Inline(
            Some(outer),
            Shape::Product {
                width: 3,
                offsets: vec![0, 2],
                reprs: vec![FieldRepr::Spliced(0), FieldRepr::Slot(SlotKind::Int)],
                kinds: vec![SlotKind::Int; 3],
            },
        ),
    ];
    // One function receives the inner pair from a call (uniform), the
    // other builds it natively in place.
    let mut from_uniform = function(
        0,
        4,
        vec![
            Inst::Call {
                dest: 1,
                func: 2,
                args: Vec::new(),
                unwind: None,
            },
            Inst::Aggregate {
                tag: 0,
                dest: 2,
                layout: 1,
                args: vec![Operand::Local(1), Operand::Const(Constant::Int(7))],
            },
            Inst::Field {
                dest: 3,
                src: Operand::Local(2),
                container: 1,
                offset: 0,
                member: Some(0),
            },
        ],
        Term::Return(Operand::Local(3)),
    );
    stamp(
        &mut from_uniform,
        &[
            (None, true),
            (None, false),
            (Some(1), true),
            (Some(0), false),
        ],
        &[(0, 1)],
    );
    let mut from_native = function(
        0,
        3,
        vec![
            Inst::Aggregate {
                tag: 0,
                dest: 1,
                layout: 0,
                args: vec![
                    Operand::Const(Constant::Int(1)),
                    Operand::Const(Constant::Int(2)),
                ],
            },
            Inst::Aggregate {
                tag: 0,
                dest: 2,
                layout: 1,
                args: vec![Operand::Local(1), Operand::Const(Constant::Int(9))],
            },
        ],
        Term::Return(Operand::Local(2)),
    );
    stamp(
        &mut from_native,
        &[(None, true), (Some(0), false), (Some(1), false)],
        &[],
    );
    let mut source = function(
        0,
        1,
        Vec::new(),
        Term::Return(Operand::Const(Constant::Unit)),
    );
    stamp(&mut source, &[(None, true)], &[]);
    let out = emitted(vec![from_uniform, from_native, source], table);
    // A uniform source for a spliced field unboxes once and copies
    // slots (ADR 0046: the flat struct has one member per slot)...
    assert!(out.contains("TalkL0 sub = talk_unbox_l0(l[1]);"), "{out}");
    assert!(out.contains("x2.m0 = sub.m0;"), "{out}");
    assert!(out.contains("x2.m1 = sub.m1;"), "{out}");
    assert!(out.contains("x2.m2 = talk_int(INT64_C(7)).v.i;"), "{out}");
    // ...a native one copies slots...
    assert!(out.contains("x2.m0 = x1.m0;"), "{out}");
    assert!(out.contains("x2.m1 = x1.m1;"), "{out}");
    // ...and reading the spliced field back copies its slots into a
    // destination classed by the field's own layout, re-boxed only
    // when it crosses the uniform return.
    assert!(out.contains("x3.m0 = x2.m0;"), "{out}");
    assert!(out.contains("x3.m1 = x2.m1;"), "{out}");
    assert!(out.contains("return talk_box_l0(x3);"), "{out}");
    // Returning the native outer struct reabstracts it whole.
    assert!(out.contains("return talk_box_l1(x2);"), "{out}");
}

#[test]
fn native_sums_write_and_read_statically() {
    let option = sym(1);
    let table = vec![Layout::Inline(
        Some(option),
        Shape::Sum {
            width: 2,
            payloads: vec![vec![1], Vec::new()],
            reprs: vec![vec![FieldRepr::Slot(SlotKind::Int)], Vec::new()],
            kinds: vec![SlotKind::Int; 2],
        },
    )];
    let mut entry = function(
        0,
        4,
        vec![
            Inst::Aggregate {
                dest: 1,
                tag: 0,
                layout: 0,
                args: vec![Operand::Const(Constant::Int(3))],
            },
            Inst::GetTag {
                dest: 2,
                src: Operand::Local(1),
            },
            Inst::Field {
                dest: 3,
                src: Operand::Local(1),
                container: 0,
                offset: 1,
                member: None,
            },
        ],
        Term::Return(Operand::Local(3)),
    );
    stamp(
        &mut entry,
        &[(None, true), (Some(0), true), (None, false), (None, false)],
        &[(0, 0)],
    );
    let out = emitted(vec![entry], table);
    assert!(out.contains("x1.m0 = 0;"), "{out}");
    assert!(out.contains("x1.m1 = talk_int(INT64_C(3)).v.i;"), "{out}");
    assert!(out.contains("l[2] = talk_int(x1.m0);"), "{out}");
    assert!(out.contains("l[3] = talk_int(x1.m1);"), "{out}");
}

#[test]
fn dynamically_indexed_sources_stay_uniform_and_tagged() {
    // A `GetElement` source has no static member in a native struct
    // (C cannot select a member by runtime index): the published
    // locals table keeps the local uniform, and `InlineArray`'s
    // boxed form stays the tagged aggregate `talk_get_element`
    // indexes.
    let mut entry = function(
        0,
        4,
        vec![
            Inst::Aggregate {
                tag: 0,
                dest: 1,
                layout: 0,
                args: vec![
                    Operand::Const(Constant::Int(1)),
                    Operand::Const(Constant::Int(2)),
                ],
            },
            Inst::Copy {
                dest: 2,
                src: Operand::Const(Constant::Int(0)),
            },
            Inst::GetElement {
                dest: 3,
                src: Operand::Local(1),
                element: LayoutId::MAX,
                index: Operand::Local(2),
            },
        ],
        Term::Return(Operand::Local(3)),
    );
    stamp(
        &mut entry,
        &[(None, true), (None, true), (None, false), (None, false)],
        &[(0, 0)],
    );
    let out = emitted(vec![entry], vec![flat_pair(MirSymbol::INLINE_ARRAY)]);
    assert!(!out.contains("TalkL0 x1"), "{out}");
    assert!(out.contains("l[1] = built;"), "{out}");
}

#[test]
fn native_signatures_pass_structs_directly() {
    // The callee publishes an inline pair parameter; the caller owns
    // one natively, so the call hands the struct over with no boxing
    // on either side, and the callee's prologue fills its struct
    // local straight from the parameter.
    let pair = sym(1);
    let mut entry = function(
        0,
        3,
        vec![
            Inst::Aggregate {
                tag: 0,
                dest: 1,
                layout: 0,
                args: vec![
                    Operand::Const(Constant::Int(1)),
                    Operand::Const(Constant::Int(2)),
                ],
            },
            Inst::Call {
                dest: 2,
                func: 1,
                args: vec![Operand::Local(1)],
                unwind: None,
            },
        ],
        Term::Return(Operand::Local(2)),
    );
    stamp(
        &mut entry,
        &[(None, true), (Some(0), true), (None, false)],
        &[(0, 0)],
    );
    let mut callee = function(
        1,
        2,
        vec![Inst::Field {
            dest: 1,
            src: Operand::Local(0),
            container: 0,
            offset: 0,
            member: None,
        }],
        Term::Return(Operand::Local(1)),
    );
    callee.param_reprs = vec![ParamRepr::Borrow(0)];
    stamp(&mut callee, &[(Some(0), false), (None, false)], &[]);
    let out = emitted(vec![entry, callee], vec![flat_pair(pair)]);
    assert!(out.contains("talk_fn1(NULL, x1)"), "{out}");
    assert!(
        out.contains("static TalkValue talk_fn1(const TalkValue *env, TalkL0 p0)"),
        "{out}"
    );
    assert!(out.contains("x0 = p0;"), "{out}");
    assert!(out.contains("l[1] = talk_int(x0.m0);"), "{out}");
    // The dispatch case converts for indirect callers.
    assert!(
        out.contains("talk_fn1(env, talk_unbox_l0(args[0]))"),
        "{out}"
    );
}

#[test]
fn values_arriving_natively_box_in_the_arena() {
    // A native parameter's value arrived from outside every site the
    // escape analysis judged, so reabstracting it must not use a
    // frame buffer: a callee returning its evolved parameter inside
    // the writeback tuple would otherwise hand the caller a pointer
    // into this dead frame.
    let pair = sym(1);
    let mut entry = function(
        0,
        2,
        vec![
            Inst::Aggregate {
                tag: 0,
                dest: 1,
                layout: 0,
                args: vec![
                    Operand::Const(Constant::Int(1)),
                    Operand::Const(Constant::Int(2)),
                ],
            },
            Inst::Call {
                dest: 1,
                func: 1,
                args: vec![Operand::Local(1)],
                unwind: None,
            },
        ],
        Term::Return(Operand::Local(1)),
    );
    stamp(&mut entry, &[(None, true), (None, false)], &[]);
    let mut callee = function(
        1,
        3,
        vec![Inst::Call {
            dest: 1,
            func: 2,
            args: vec![Operand::Local(0)],
            unwind: None,
        }],
        Term::Return(Operand::Local(1)),
    );
    callee.param_reprs = vec![ParamRepr::Value(0)];
    stamp(
        &mut callee,
        &[(Some(0), false), (None, false), (None, true)],
        &[],
    );
    let mut sink = function(1, 2, Vec::new(), Term::Return(Operand::Local(0)));
    stamp(&mut sink, &[(None, false), (None, true)], &[]);
    let out = emitted(vec![entry, callee, sink], vec![flat_pair(pair)]);
    assert!(out.contains("talk_box_l0(x0)"), "{out}");
    assert!(!out.contains("talk_box_l0_in(fx0, x0)"), "{out}");
}

#[test]
fn native_returns_hand_back_structs() {
    // The callee publishes an inline return: it hands its struct
    // back directly (no arena box), the caller's destination is
    // classed from the published fact, and unwind paths return a
    // zeroed sentinel of the native type.
    let pair = sym(1);
    let mut entry = function(
        0,
        3,
        vec![
            Inst::Call {
                dest: 1,
                func: 1,
                args: Vec::new(),
                unwind: None,
            },
            Inst::Field {
                dest: 2,
                src: Operand::Local(1),
                container: 0,
                offset: 0,
                member: None,
            },
        ],
        Term::Return(Operand::Local(2)),
    );
    stamp(
        &mut entry,
        &[(None, true), (Some(0), false), (None, false)],
        &[],
    );
    let mut callee = function(
        0,
        2,
        vec![
            Inst::Call {
                dest: 0,
                func: 2,
                args: Vec::new(),
                unwind: None,
            },
            Inst::Aggregate {
                tag: 0,
                dest: 1,
                layout: 0,
                args: vec![Operand::Local(0), Operand::Const(Constant::Int(2))],
            },
        ],
        Term::Return(Operand::Local(1)),
    );
    callee.return_repr = Some(0);
    stamp(&mut callee, &[(None, false), (Some(0), false)], &[]);
    let mut helper = function(
        0,
        1,
        Vec::new(),
        Term::Return(Operand::Const(Constant::Unit)),
    );
    stamp(&mut helper, &[(None, true)], &[]);
    let out = emitted(vec![entry, callee, helper], vec![flat_pair(pair)]);
    assert!(
        out.contains("static TalkL0 talk_fn1(const TalkValue *env)"),
        "{out}"
    );
    assert!(out.contains("    return x1;"), "{out}");
    // The callee contains a call, so its unwind path must return the
    // native sentinel rather than Unit.
    assert!(out.contains("return (TalkL0){0};"), "{out}");
    // The caller's destination takes the struct without reboxing.
    assert!(out.contains("x1 = talk_fn1(NULL);"), "{out}");
    assert!(out.contains("l[2] = talk_int(x1.m0);"), "{out}");
    assert!(
        out.contains("case 1: return talk_box_l0(talk_fn1(env));"),
        "{out}"
    );
}

#[test]
fn blank_cells_box_native_and_zero() {
    // The initializer's blank receiver: declared blankness. Nothing
    // observes an unassigned field (definite assignment on the happy
    // path, per-field shadows on the abort path), so a box-native
    // receiver is zeroed native storage — no tagged placeholders.
    let pair = sym(1);
    let mut entry = function(
        0,
        3,
        vec![
            Inst::Blank { dest: 1, layout: 0 },
            Inst::Aggregate {
                tag: 0,
                dest: 2,
                layout: 0,
                args: vec![
                    Operand::Const(Constant::Int(1)),
                    Operand::Const(Constant::Int(2)),
                ],
            },
        ],
        Term::Return(Operand::Local(1)),
    );
    stamp(
        &mut entry,
        &[(None, true), (None, false), (Some(0), true)],
        &[(0, 1)],
    );
    let out = emitted(vec![entry], vec![flat_pair(pair)]);
    // The blank builds as a zeroed native box (its local never
    // classes — the value leaves through the init call)...
    assert!(!out.contains("TalkL0 x1;"), "{out}");
    assert!(
        out.contains("memset(TALK_NATIVE_PAYLOAD(built), 0, sizeof(TalkL0));"),
        "{out}"
    );
    // ...while the honest construction of the same layout goes
    // native in its frame local.
    assert!(out.contains("x2.m0 = talk_int(INT64_C(1)).v.i;"), "{out}");
}

/// A library fixture: an inert entry plus one exported identity-ish
/// function per name, all under the uniform convention, the shape
/// `Entry::Exports` produces.
fn library(exports: &[(&str, usize)]) -> Program {
    let entry = function(
        0,
        1,
        Vec::new(),
        Term::Return(Operand::Const(Constant::Unit)),
    );
    let wrapped = function(1, 2, Vec::new(), Term::Return(Operand::Local(0)));
    module(
        vec![entry, wrapped],
        Vec::new(),
        exports
            .iter()
            .map(|(name, id)| (name.to_string(), *id))
            .collect(),
    )
}

#[test]
fn library_emission_omits_main_and_wraps_each_export() {
    let artifact =
        talk_c::emit_library(&library(&[("double", 1)]), "mylib").expect("library emission");
    // No process entry, and the boundary section is compiled in.
    assert!(
        !artifact.source.contains("int main("),
        "{}",
        artifact.source
    );
    assert!(
        artifact.source.starts_with("#define TALK_LIBRARY 1"),
        "{}",
        artifact.source
    );
    // One externally visible arity-checked wrapper per export, plus
    // the lifecycle entry points; everything else stays static.
    assert!(
        artifact
            .source
            .contains("int mylib_double(TalkValue *out, const TalkValue *args, size_t argc)"),
        "{}",
        artifact.source
    );
    assert!(artifact.source.contains("argc != 1"), "{}", artifact.source);
    assert!(
        artifact.source.contains("int mylib_init(void)"),
        "{}",
        artifact.source
    );
    assert!(
        artifact.source.contains("void mylib_teardown(void)"),
        "{}",
        artifact.source
    );
    assert!(
        artifact
            .source
            .contains("const char *mylib_error_message(void)"),
        "{}",
        artifact.source
    );
    // The header speaks the same convention under public names.
    assert!(
        artifact.header.contains("#define MYLIB_ABI_VERSION 1"),
        "{}",
        artifact.header
    );
    assert!(
        artifact
            .header
            .contains("int mylib_double(mylib_value *out, const mylib_value *args, size_t argc);"),
        "{}",
        artifact.header
    );
    assert!(
        artifact.header.contains("MYLIB_ERR_TRAP"),
        "{}",
        artifact.header
    );
    // The manifest maps each export name to its external symbol.
    assert_eq!(artifact.manifest, "double\tmylib_double\n");
}

#[test]
fn library_mangling_is_deterministic_and_collision_free() {
    let artifact = talk_c::emit_library(&library(&[("a_b", 1), ("café", 1), ("a?b", 1)]), "lib")
        .expect("library emission");
    // Underscores double and non-alphanumeric bytes escape to hex,
    // so distinct names cannot meet at one symbol.
    assert_eq!(
        artifact.manifest,
        "a_b\tlib_a__b\ncafé\tlib_caf_c3_a9\na?b\tlib_a_3fb\n"
    );
}

#[test]
fn library_emission_reports_adapter_errors() {
    let invalid_prefix = talk_c::emit_library(&library(&[("f", 1)]), "1bad");
    assert!(
        invalid_prefix.is_err_and(|error| error.message().contains("prefix")),
        "an invalid prefix must be rejected"
    );
    let empty_prefix = talk_c::emit_library(&library(&[("f", 1)]), "");
    assert!(empty_prefix.is_err(), "an empty prefix must be rejected");
    let lifecycle_collision = talk_c::emit_library(&library(&[("init", 1)]), "lib");
    assert!(
        lifecycle_collision.is_err_and(|error| error.message().contains("lib_init")),
        "an export colliding with a lifecycle symbol must be rejected"
    );
    let duplicate = talk_c::emit_library(&library(&[("f", 1), ("f", 1)]), "lib");
    assert!(
        duplicate.is_err_and(|error| error.message().contains("duplicate")),
        "duplicate external symbols must be rejected"
    );
    let empty_name = talk_c::emit_library(&library(&[("", 1)]), "lib");
    assert!(empty_name.is_err(), "an empty export name must be rejected");
    let missing_function = talk_c::emit_library(&library(&[("f", 9)]), "lib");
    assert!(
        missing_function.is_err(),
        "an export naming a missing function must be rejected"
    );
    let no_exports = talk_c::emit_library(&library(&[]), "lib");
    assert!(
        no_exports.is_err(),
        "a library with no exports must be rejected"
    );
}

#[test]
fn eligibility_excludes_boxed_empty_and_spliced_sums() {
    let table = vec![
        flat_pair(sym(1)),
        Layout::Boxed(
            Some(sym(2)),
            Shape::Product {
                width: 5,
                offsets: vec![0, 1, 2, 3, 4],
                reprs: vec![FieldRepr::Slot(SlotKind::Int); 5],
                kinds: vec![SlotKind::Int; 5],
            },
        ),
        Layout::Inline(
            Some(sym(3)),
            Shape::Product {
                width: 0,
                offsets: Vec::new(),
                reprs: Vec::new(),
                kinds: Vec::new(),
            },
        ),
        Layout::Inline(
            Some(sym(4)),
            Shape::Sum {
                width: 3,
                payloads: vec![vec![1], Vec::new()],
                reprs: vec![vec![FieldRepr::Spliced(0)], Vec::new()],
                kinds: vec![SlotKind::Int; 3],
            },
        ),
        Layout::Slot,
        Layout::Opaque,
    ];
    assert_eq!(
        talk_c::eligible_layouts(&table, &talk_c::struct_layouts(&table)),
        vec![true, false, false, false, false, false]
    );
}
