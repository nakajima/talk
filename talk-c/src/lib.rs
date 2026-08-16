//! MIR to C source lowering: the ahead-of-time target.
//!
//! Same input as `lower::lower`: the optimized, register-allocated MIR
//! program. Basic blocks become labels and `goto`s, MIR locals become one
//! `TalkValue l[]` array per activation, and the C compiler does the
//! register allocation and instruction selection the VM never gets to do.
//!
//! Covered: the whole scalar set, aggregates, closures and indirect
//! calls, effect handlers, managed memory, static literal data, program
//! globals, host IO, `'heap` objects with merge-only regions, cells, and
//! existentials. Every program in `bench/`, `tests/programs/`, and the
//! `tests/reference/` corpora that the checker accepts compiles and
//! agrees with the interpreter.
//!
//! Every MIR instruction is translated. The instruction match is
//! exhaustive on purpose: a variant added to MIR later is a compile
//! error here rather than a program that quietly does something else.
//!
//! `talk build --native` drives this end to end — emit C, run the host
//! compiler — producing an executable that links nothing but libc.
//!
//! Buffers use machine pointers with a reference-counted header rather
//! than the VM's simulated byte memory, so the exit allocation balance is
//! reproduced exactly while per-access provenance checking is not.

use std::fmt::Write as _;

/// A C-adapter rejection: malformed public MIR supplied manually, a
/// target representability failure, or a target-internal invariant
/// failure. Adapter errors carry no parser spans; the compiler locates
/// source errors before publishing MIR (ADR 0047).
#[derive(Debug)]
pub struct Error {
    message: String,
}

impl Error {
    fn new(message: String) -> Self {
        Self { message }
    }

    /// A deliberate fail-closed rejection of MIR this target does not
    /// represent. Compiler-produced modules never trigger one (ADR
    /// 0037's completeness requirement).
    fn unsupported(message: String) -> Self {
        debug_assert!(message.contains("not supported yet"));
        Self::new(message)
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

use rustc_hash::FxHashMap;

use talk_mir::layout::{FieldRepr, Layout, LayoutId, Shape, SlotKind};
use talk_mir::{
    CmpKind, Constant, Function, Inst, MirSymbol, Module as Program, Operand, ScalarOp, Term,
};
use talk_native_runtime::emit::{
    Interners, c_escape, needs_identity, resumable_functions, static_strings, symbol_rows,
    type_table,
};

/// The generated file's runtime half, emitted verbatim ahead of the
/// translated functions. Owned by `talk-native-runtime` and shared with
/// the LLVM backend (ADR 0047).
const PRELUDE: &str = talk_native_runtime::source();

/// The emitted translation unit.
#[derive(Debug)]
pub struct Artifact {
    pub source: String,
}

/// A library-mode emission (ADR 0048): the translation unit exposing one
/// wrapper per `Module.exports` entry, the matching C header, and the
/// export-name-to-symbol manifest.
#[derive(Debug)]
pub struct LibraryArtifact {
    pub source: String,
    pub header: String,
    pub manifest: String,
}

/// Everything shared by the executable and library artifacts: the
/// runtime prelude, data tables, and every translated function body.
/// Library mode also carries the interned String identity for the
/// boundary's string constructor.
struct Translation<'p> {
    source: String,
    facts: Facts<'p>,
    string_ids: Option<(u32, u32)>,
}

fn translate(program: &Program, library: bool) -> Result<Translation<'_>, Error> {
    let display = &program.display;
    // Function bodies intern static data as they are emitted, so they are
    // built first and the blob is placed ahead of them.
    let mut emitter = Emitter {
        widest_arity: program
            .functions
            .iter()
            .map(|function| usize::from(function.arity))
            .max()
            .unwrap_or(0),
        ..Emitter::default()
    };
    let facts = Facts::new(program);
    // ADR 0065: the resumable set — every function a suspension's
    // return-status can propagate through — and whether any
    // address-taken function is in it (the conservative indirect rule).
    let resumable = resumable_functions(&program.functions);
    let closures_suspend = program.functions.iter().any(|function| {
        function.blocks.iter().any(|block| {
            block.insts.iter().any(|inst| match inst {
                Inst::MakeClosure { func, .. } => {
                    resumable.get(*func).copied().unwrap_or(false)
                }
                _ => false,
            })
        })
    });
    let mut bodies = String::new();
    for (id, function) in program.functions.iter().enumerate() {
        emitter.function(&mut bodies, id, function, &facts, &resumable, closures_suspend)?;
    }
    emit_dispatch(&mut bodies, program, &facts);
    // Built after the bodies (they record which layouts went native) but
    // placed ahead of them, like the statics blob.
    let mut layout_decls = String::new();
    emitter.layout_decls(&mut layout_decls, &facts)?;

    // The layout data table interns display ids for spliced children,
    // so it is built before the type table that indexes them.
    let mut layout_data = String::new();
    emit_layout_table(&mut layout_data, &mut emitter, &facts)?;

    // The boundary's string constructor needs core String's interned
    // identity; interning happens before the type table is rendered.
    let string_ids = if library {
        program
            .layout_table
            .iter()
            .position(|layout| {
                matches!(
                    layout,
                    Layout::Inline(Some(symbol), _) | Layout::Boxed(Some(symbol), _)
                        if *symbol == program.string_symbol
                )
            })
            .map(|layout| {
                let display = emitter.interners.display_id(program.string_symbol);
                (u32::try_from(layout).unwrap_or(u32::MAX), display)
            })
    } else {
        None
    };

    let mut out = String::new();
    if library {
        // Compiles the runtime's boundary machinery in (setjmp trap
        // containment, live-resource tracking, full reset).
        out.push_str("#define TALK_LIBRARY 1\n");
    }
    out.push_str(PRELUDE);
    out.push('\n');
    emit_statics(&mut out, &emitter.interners.statics);
    static_strings(&mut out, &emitter.interners);
    type_table(&mut out, &emitter.interners, display);
    if library {
        symbol_rows(&mut out, &emitter.interners);
    }
    out.push_str(&layout_data);
    out.push_str(&layout_decls);
    if program.global_slots != 0 {
        let _ = writeln!(
            out,
            "\n/* Program globals: one 8-byte boxed slot each, zero meaning\n\
             \x20  uninitialized so a read before the initializer traps. */\n\
             static unsigned char talk_globals[{}];",
            program.global_slots as u64 * 8
        );
    }
    out.push('\n');
    for (id, function) in program.functions.iter().enumerate() {
        let _ = writeln!(
            out,
            "static {} {}({}); /* {} */",
            return_type(facts.sigs[id].ret),
            symbol(id),
            parameter_list(function.arity, &facts.sigs[id]),
            comment(&function.name)
        );
    }
    out.push_str(&bodies);
    Ok(Translation {
        source: out,
        facts,
        string_ids,
    })
}

/// Emit one self-contained C translation unit for a finalized MIR
/// module.
pub fn emit(program: &Program) -> Result<Artifact, Error> {
    let entry = program
        .functions
        .get(program.entry)
        .ok_or_else(|| internal("entry function is missing"))?;
    if entry.arity != 0 {
        return Err(unsupported("an entry function with parameters"));
    }
    let Translation {
        source: mut out,
        facts,
        string_ids: _,
    } = translate(program, false)?;
    // The process arguments are the host's, so `argc`/`arg_len`/
    // `arg_copy` read them straight from `main`.
    let _ = write!(
        out,
        "\nint main(int argc, char **argv) {{\n    \
         talk_argc = argc;\n    \
         talk_argv = argv;\n    \
         {{ char anchor; talk_stack_init((uintptr_t)&anchor); }}\n    \
         talk_statics_base = talk_statics;\n    \
         talk_statics_len = sizeof talk_statics;\n    \
         talk_types = talk_type_table;\n    \
         talk_type_count = sizeof talk_type_table / sizeof *talk_type_table;\n    \
         talk_layouts = talk_layout_table;\n    \
         talk_layout_count = sizeof talk_layout_table / sizeof *talk_layout_table;\n    \
         int status = talk_print({});\n    \
         talk_arena_release();\n    \
         talk_effects_release();\n    \
         return status;\n}}\n",
        match facts.sigs[program.entry].ret {
            Some(layout) => format!("talk_box_l{layout}({}(NULL))", symbol(program.entry)),
            None => format!("{}(NULL)", symbol(program.entry)),
        }
    );
    Ok(Artifact { source: out })
}

/// Emit a library translation unit (ADR 0048): no `main`, every
/// implementation function private, one externally visible wrapper per
/// `Module.exports` entry under `prefix`, plus namespaced lifecycle
/// entry points. Traps and exit requests are contained at the wrapper
/// boundary and returned as statuses; they never terminate the host.
/// The convention, lifecycle, header, and mangling are the shared
/// boundary in `talk_native_runtime::library`.
pub fn emit_library(program: &Program, prefix: &str) -> Result<LibraryArtifact, Error> {
    use talk_native_runtime::library;
    if program.exports.is_empty() {
        return Err(Error::new(
            "a library artifact needs at least one export".to_string(),
        ));
    }
    let names: Vec<&str> = program
        .exports
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    let symbols = library::resolve_symbols(prefix, &names).map_err(Error::new)?;
    let mut exports: Vec<(library::Export, usize)> = Vec::with_capacity(symbols.len());
    for ((name, func), symbol) in program.exports.iter().zip(symbols) {
        let function = program.functions.get(*func).ok_or_else(|| {
            Error::new(format!(
                "export \"{name}\" names a function this module does not contain"
            ))
        })?;
        exports.push((
            library::Export {
                name: name.clone(),
                symbol,
                arity: function.arity,
            },
            *func,
        ));
    }

    let Translation {
        source: mut out,
        facts,
        string_ids,
    } = translate(program, true)?;
    out.push_str(&library::boundary_prelude());
    out.push_str(&library::cleanup_helper(program.global_slots != 0));
    out.push_str(&library::lifecycle(
        prefix,
        "sizeof talk_layout_table / sizeof *talk_layout_table",
    ));
    out.push_str(&library::accessors(prefix, string_ids));
    for (export, func) in &exports {
        // The wrapper enters generated code the way `talk_dispatch`
        // does: uniform values in, converted at the callee's published
        // signature, reabstracted on the way out.
        let sig = &facts.sigs[*func];
        let arguments: String = (0..export.arity)
            .map(|index| match sig.param(index) {
                Some(layout) => format!(", talk_unbox_l{layout}(args[{index}])"),
                None => format!(", args[{index}]"),
            })
            .collect();
        let call = format!("{}(NULL{arguments})", symbol(*func));
        let call = match sig.ret {
            Some(layout) => format!("talk_box_l{layout}({call})"),
            None => call,
        };
        out.push_str(&library::wrapper(
            export,
            &format!("TalkValue result = {call};"),
        ));
    }
    let exports: Vec<library::Export> = exports.into_iter().map(|(export, _)| export).collect();
    Ok(LibraryArtifact {
        header: library::header(prefix, &exports),
        manifest: library::manifest(&exports),
        source: out,
    })
}

/// Immortal literal bytes. One trailing zero keeps the array non-empty
/// when a program has no literals, so `sizeof` and the static-range test
/// stay well defined.
fn emit_statics(out: &mut String, bytes: &[u8]) {
    let _ = writeln!(
        out,
        "\n/* Immortal literal data; retaining or freeing a pointer into\n\
         \x20  this blob is a no-op, as provenance zero is in the VM. */"
    );
    let _ = write!(out, "static unsigned char talk_statics[] = {{");
    for (index, byte) in bytes.iter().enumerate() {
        if index % 16 == 0 {
            let _ = write!(out, "\n   ");
        }
        let _ = write!(out, " {byte},");
    }
    if bytes.is_empty() {
        let _ = write!(out, " 0");
    }
    let _ = writeln!(out, "\n}};");
}

/// `CallIndirect` reaches a function value's target through one switch, so
/// closures need no function-pointer types in the generated C. The switch
/// speaks the uniform convention; a native-signature callee converts at
/// its case.
fn emit_dispatch(out: &mut String, program: &Program, facts: &Facts) {
    let _ = writeln!(
        out,
        "\nstatic TalkValue talk_dispatch(uint32_t function, const TalkValue *env, const TalkValue *args) {{"
    );
    let _ = writeln!(out, "    (void)args;");
    let _ = writeln!(out, "    switch (function) {{");
    for (id, function) in program.functions.iter().enumerate() {
        let sig = &facts.sigs[id];
        let arguments: String = (0..function.arity)
            .map(|index| match sig.param(index) {
                Some(layout) => format!(", talk_unbox_l{layout}(args[{index}])"),
                None => format!(", args[{index}]"),
            })
            .collect();
        let call = format!("{}(env{arguments})", symbol(id));
        let call = match sig.ret {
            Some(layout) => format!("talk_box_l{layout}({call})"),
            None => call,
        };
        let _ = writeln!(out, "    case {id}: return {call};");
    }
    let _ = writeln!(
        out,
        "    default: talk_trap(\"call to an unknown function\");"
    );
    let _ = writeln!(out, "    }}");
    let _ = writeln!(out, "}}");
}

/// The published layout table as C data (ADR 0046): structure for the
/// logical member operations and the renderer, mirroring the wire
/// descriptors exactly.
fn emit_layout_table(out: &mut String, emitter: &mut Emitter, facts: &Facts) -> Result<(), Error> {
    let row = |emitter: &mut Emitter, offset: u32, repr: FieldRepr| -> Result<String, Error> {
        Ok(match repr {
            FieldRepr::Slot(_) => format!("{{ {offset}, 1, UINT32_MAX, 0 }}"),
            FieldRepr::Spliced(child) => {
                let width = facts.shape_of(child)?.width();
                let symbol = emitter.display_of(facts.table, child);
                format!("{{ {offset}, {width}, {child}u, {symbol} }}")
            }
        })
    };
    let mut entries: Vec<String> = Vec::with_capacity(facts.table.len());
    for (id, layout) in facts.table.iter().enumerate() {
        match layout {
            Layout::Slot => entries.push("    { 1, 0, NULL, 0, NULL, 0 },".into()),
            Layout::Opaque => entries.push("    { 0, 0, NULL, 0, NULL, 0 },".into()),
            Layout::Inline(_, shape) | Layout::Boxed(_, shape) => match shape {
                Shape::Product {
                    width,
                    offsets,
                    reprs,
                    ..
                } => {
                    let mut rows = Vec::with_capacity(reprs.len());
                    for (offset, repr) in offsets.iter().zip(reprs) {
                        rows.push(row(emitter, *offset, *repr)?);
                    }
                    let fields = if rows.is_empty() {
                        "NULL".to_string()
                    } else {
                        let _ = writeln!(
                            out,
                            "static const TalkField talk_lfields_{id}[] = {{ {} }};",
                            rows.join(", ")
                        );
                        format!("talk_lfields_{id}")
                    };
                    entries.push(format!(
                        "    {{ {width}, 0, {fields}, {}, NULL, 0 }},",
                        rows.len()
                    ));
                }
                Shape::Sum {
                    width,
                    payloads,
                    reprs,
                    ..
                } => {
                    let mut rows = Vec::new();
                    let mut starts = vec![0usize];
                    for (offsets, variant_reprs) in payloads.iter().zip(reprs) {
                        for (offset, repr) in offsets.iter().zip(variant_reprs) {
                            rows.push(row(emitter, *offset, *repr)?);
                        }
                        starts.push(rows.len());
                    }
                    let fields = if rows.is_empty() {
                        "NULL".to_string()
                    } else {
                        let _ = writeln!(
                            out,
                            "static const TalkField talk_lfields_{id}[] = {{ {} }};",
                            rows.join(", ")
                        );
                        format!("talk_lfields_{id}")
                    };
                    let rendered: Vec<String> =
                        starts.iter().map(|start| start.to_string()).collect();
                    let _ = writeln!(
                        out,
                        "static const uint32_t talk_lvars_{id}[] = {{ {} }};",
                        rendered.join(", ")
                    );
                    entries.push(format!(
                        "    {{ {width}, 1, {fields}, {}, talk_lvars_{id}, {} }},",
                        rows.len(),
                        payloads.len()
                    ));
                }
            },
        }
    }
    let _ = writeln!(out, "static const TalkLayoutInfo talk_layout_table[] = {{");
    for entry in entries {
        let _ = writeln!(out, "{entry}");
    }
    let _ = writeln!(out, "}};");
    Ok(())
}

#[derive(Default)]
struct Emitter {
    /// The interned identities the shared data tables render (effects,
    /// statics, display ids), one definition with the LLVM backend.
    interners: Interners,
    /// The widest arity `talk_dispatch` can reach, which sets the size of
    /// every indirect call's argument array.
    widest_arity: usize,
}

impl Emitter {
    /// A construction's rendered identity, read off its layout: the
    /// declared symbol as a display id, or zero for anonymous products.
    fn display_of(&mut self, table: &[Layout], layout: LayoutId) -> u32 {
        match table.get(usize::try_from(layout).unwrap_or(usize::MAX)) {
            Some(Layout::Inline(Some(symbol), _) | Layout::Boxed(Some(symbol), _)) => {
                self.interners.display_id(*symbol)
            }
            _ => 0,
        }
    }

    fn function(
        &mut self,
        out: &mut String,
        id: usize,
        function: &Function,
        facts: &Facts,
        resumable: &[bool],
        closures_suspend: bool,
    ) -> Result<(), Error> {
        // Only a frame that names itself can ever be a continuation's
        // target or a handler's installer, so leaf functions stay free of
        // shadow-stack traffic. A resumable function (ADR 0065) always
        // carries identity: suspensions land by frame id.
        let is_resumable = resumable.get(id).copied().unwrap_or(false);
        let identified = needs_identity(function) || is_resumable;
        let sig = &facts.sigs[id];
        if is_resumable {
            return self.resumable_function(
                out,
                id,
                function,
                facts,
                resumable,
                closures_suspend,
            );
        }
        let _ = writeln!(
            out,
            "\n/* {} */\nstatic {} {}({}) {{",
            comment(&function.name),
            return_type(sig.ret),
            symbol(id),
            parameter_list(function.arity, sig)
        );
        // Zero is `TALK_UNIT`, so an unwritten local reads as Unit rather
        // than as whatever the stack held.
        let _ = writeln!(out, "    TalkValue l[{}];", function.n_locals().max(1));
        let _ = writeln!(out, "    memset(l, 0, sizeof l);");
        let _ = writeln!(out, "    (void)env;");
        // Locals classed to an inline layout get native struct storage
        // (ADR 0045); everything else stays a tagged slot in `l[]`. A
        // frame-local native value also gets a boxing buffer, so its
        // reabstractions reuse one slot instead of growing the arena.
        // Both facts come published on the function's locals table; this
        // backend only filters for the layouts it can store.
        let native: Vec<Option<LayoutId>> = function
            .locals
            .iter()
            .map(|info| info.layout.filter(|layout| facts.storable(*layout)))
            .collect();
        let buffered: Vec<bool> = function
            .locals
            .iter()
            .zip(&native)
            .map(|(info, class)| info.frame_local && class.is_some())
            .collect();
        let frame = Frame {
            native,
            buffered,
            ret: sig.ret,
            facts,
        };
        for (local, class) in frame.native.iter().enumerate() {
            if let Some(layout) = class {
                let _ = writeln!(out, "    TalkL{layout} x{local};");
                let _ = writeln!(out, "    memset(&x{local}, 0, sizeof x{local});");
                if frame.buffered[local] {
                    let width = frame.shape(*layout)?.width();
                    let _ = writeln!(
                        out,
                        "    _Alignas(TalkValue) unsigned char fx{local}[sizeof(TalkAgg) + {} * sizeof(TalkValue)];",
                        width.max(1)
                    );
                    let _ = writeln!(out, "    (void)fx{local};");
                }
            }
        }
        // Every function, not only the ones carrying frame identity: any
        // of them can be the one that runs the stack out.
        let _ = writeln!(out, "    talk_frame_enter();");
        if identified {
            let _ = writeln!(out, "    const size_t frame_depth = talk_depth;");
            let _ = writeln!(out, "    const uint32_t frame_id = talk_enter();");
        }
        // One storage slot per frame-local construction site, reused on
        // every execution of that site. The escape analysis is what makes
        // the reuse safe.
        let mut storage = FxHashMap::default();
        for (block_index, block) in function.blocks.iter().enumerate() {
            for (instruction_index, inst) in block.insts.iter().enumerate() {
                if !function
                    .frame_sites
                    .contains(&(block_index, instruction_index))
                {
                    continue;
                }
                let layout = match inst {
                    Inst::Aggregate { dest, layout, .. } => {
                        // A native destination allocates nothing, so its
                        // site needs no frame buffer.
                        if frame.class_of(*dest).is_some() {
                            continue;
                        }
                        *layout
                    }
                    _ => continue,
                };
                let width = usize::try_from(frame.facts.width_of(layout)?).unwrap_or(1);
                let slot = storage.len();
                // Raw aligned storage rather than a struct with a
                // `TalkAgg` member: `TalkAgg` ends in a flexible array,
                // and a struct holding one anywhere but last is a GNU
                // extension that clang rejects. A box-native site's
                // buffer holds the native header and struct instead of
                // the tagged form.
                if frame.facts.boxes_native(layout) {
                    let _ = writeln!(
                        out,
                        "    _Alignas(TalkValue) unsigned char f{slot}[sizeof(TalkNative) + sizeof(TalkL{layout})];"
                    );
                } else {
                    let _ = writeln!(
                        out,
                        "    _Alignas(TalkValue) unsigned char f{slot}[sizeof(TalkAgg) + {} * sizeof(TalkValue)];",
                        width.max(1)
                    );
                }
                storage.insert((block_index, instruction_index), slot);
            }
        }
        // Parameters land in their storage: a native parameter fills its
        // struct local directly (or reboxes when the body degraded that
        // layout to uniform); everything else takes its `l[]` slot.
        for index in 0..function.arity {
            match sig.param(index) {
                Some(layout) => {
                    if frame.class_of(index) == Some(layout) {
                        let _ = writeln!(out, "    x{index} = p{index};");
                    } else {
                        let _ = writeln!(out, "    l[{index}] = talk_box_l{layout}(p{index});");
                    }
                }
                None => {
                    let _ = writeln!(out, "    l[{index}] = p{index};");
                }
            }
        }
        // Entering block zero by `goto` rather than by falling through
        // keeps every emitted label a used one.
        let _ = writeln!(out, "    goto b0;");
        for (index, block) in function.blocks.iter().enumerate() {
            let _ = writeln!(out, "b{index}:");
            for (instruction_index, inst) in block.insts.iter().enumerate() {
                let frame_slot = storage.get(&(index, instruction_index)).copied();
                self.inst(out, inst, identified, frame_slot, &frame, &mut SusCtx::inert())?;
            }
            let term = block
                .term
                .as_ref()
                .ok_or_else(|| internal("basic block has no terminator"))?;
            emit_term(out, term, function, identified, &frame)?;
        }
        let _ = writeln!(out, "}}");
        Ok(())
    }

    /// ADR 0065: emit one function in resumable form — a wrapper with
    /// the published signature over a heap-framed impl with re-entry
    /// dispatch. Locals are forced uniform so the frame's `l[]` is the
    /// whole state; `TalkValue *l = fr->l;` keeps every instruction
    /// emission textually identical.
    fn resumable_function(
        &mut self,
        out: &mut String,
        id: usize,
        function: &Function,
        facts: &Facts,
        resumable: &[bool],
        closures_suspend: bool,
    ) -> Result<(), Error> {
        let sig = &facts.sigs[id];
        let n_locals = usize::from(function.n_locals()).max(1);
        let frame = Frame {
            native: vec![None; function.locals.len().max(n_locals)],
            buffered: vec![false; function.locals.len().max(n_locals)],
            ret: None,
            facts,
        };
        let mut sus = SusCtx {
            active: true,
            next_rpc: 1,
            marked: resumable,
            closures_suspend,
        };
        // The body first, into a buffer: the impl's dispatch needs the
        // final re-entry count.
        let mut body = String::new();
        for (index, block) in function.blocks.iter().enumerate() {
            let _ = writeln!(body, "b{index}:");
            for inst in &block.insts {
                self.inst(&mut body, inst, true, None, &frame, &mut sus)?;
            }
            let term = block
                .term
                .as_ref()
                .ok_or_else(|| internal("basic block has no terminator"))?;
            emit_term(&mut body, term, function, true, &frame)?;
        }
        let _ = writeln!(
            out,
            "
/* {} (resumable) */
static TalkValue {}_impl(TalkResumeFrame *fr);",
            comment(&function.name),
            symbol(id)
        );
        let _ = writeln!(
            out,
            "static {} {}({}) {{",
            return_type(sig.ret),
            symbol(id),
            parameter_list(function.arity, sig)
        );
        let _ = writeln!(
            out,
            "    TalkResumeFrame *fr = talk_resume_frame_new({n_locals}, {}_impl, env);",
            symbol(id)
        );
        for index in 0..function.arity {
            match sig.param(index) {
                Some(layout) => {
                    let _ = writeln!(out, "    fr->l[{index}] = talk_box_l{layout}(p{index});");
                }
                None => {
                    let _ = writeln!(out, "    fr->l[{index}] = p{index};");
                }
            }
        }
        let _ = writeln!(out, "    TalkValue v = {}_impl(fr);", symbol(id));
        let _ = writeln!(out, "    if (talk_frame_detached) {{");
        let _ = writeln!(out, "        talk_frame_detached = 0;");
        let _ = writeln!(out, "    }} else {{");
        let _ = writeln!(out, "        free(fr);");
        let _ = writeln!(out, "    }}");
        match sig.ret {
            Some(ret) => {
                let _ = writeln!(
                    out,
                    "    if (talk_unwinding || talk_suspend_pending) {{ return (TalkL{ret}){{0}}; }}"
                );
                let _ = writeln!(out, "    return talk_unbox_l{ret}(v);");
            }
            None => {
                let _ = writeln!(out, "    return v;");
            }
        }
        let _ = writeln!(out, "}}");
        let _ = writeln!(
            out,
            "static TalkValue {}_impl(TalkResumeFrame *fr) {{",
            symbol(id)
        );
        let _ = writeln!(out, "    TalkValue *l = fr->l;");
        let _ = writeln!(out, "    const TalkValue *env = fr->env;");
        let _ = writeln!(out, "    (void)env;");
        let _ = writeln!(out, "    (void)l;");
        let _ = writeln!(out, "    talk_frame_enter();");
        // Depth is captured before the identity push, so this frame's
        // shadow slot is frame_depth — the same relationship the plain
        // identified prologue has.
        let _ = writeln!(out, "    const size_t frame_depth = talk_depth;");
        let _ = writeln!(out, "    uint32_t frame_id;");
        let _ = writeln!(out, "    if (fr->rpc == 0) {{");
        let _ = writeln!(out, "        frame_id = talk_enter();");
        let _ = writeln!(out, "        fr->id = frame_id;");
        let _ = writeln!(out, "    }} else {{");
        let _ = writeln!(out, "        frame_id = fr->id;");
        let _ = writeln!(out, "        talk_reenter_identity(frame_id);");
        let _ = writeln!(out, "    }}");
        let _ = writeln!(out, "    switch (fr->rpc) {{");
        let _ = writeln!(out, "    case 0: goto b0;");
        for k in 1..sus.next_rpc {
            let _ = writeln!(out, "    case {k}: goto r{k};");
        }
        let _ = writeln!(out, "    default: talk_trap(\"resume into an unknown state\");");
        let _ = writeln!(out, "    }}");
        out.push_str(&body);
        let _ = writeln!(out, "}}");
        Ok(())
    }

    fn inst(
        &mut self,
        out: &mut String,
        inst: &Inst,
        identified: bool,
        frame_slot: Option<usize>,
        frame: &Frame,
        sus: &mut SusCtx,
    ) -> Result<(), Error> {
        match inst {
            Inst::Copy { dest, src } => {
                // Register reuse can unify a copy's endpoints; a self-copy is
                // a no-op, and clang rejects it under -Wself-assign.
                if let Some(layout) = frame.class_of(*dest) {
                    // The derivation only classes a local when every
                    // definition agrees, so a native destination's source
                    // is a native local of the same layout.
                    let Operand::Local(src) = src else {
                        return Err(internal("a native local copied from a constant"));
                    };
                    if frame.class_of(*src) != Some(layout) {
                        return Err(internal("a native local copied across layout classes"));
                    }
                    if dest != src {
                        let _ = writeln!(out, "    x{dest} = x{src};");
                    }
                } else if !matches!(src, Operand::Local(src) if src == dest) {
                    let _ = writeln!(out, "    l[{dest}] = {};", frame.value(*src)?);
                }
            }
            Inst::Scalar { dest, op, a, b } => {
                let _ = writeln!(out, "    l[{dest}] = {};", scalar(*op, *a, *b, frame)?);
            }
            Inst::Call {
                dest,
                func,
                args,
                unwind,
            } => {
                // The callee's published signature decides each slot: a
                // native parameter takes the caller's struct directly (no
                // boxing — the point of the convention) or unboxes a
                // uniform source; a native result lands in the caller's
                // struct local or reboxes.
                let sig = frame
                    .facts
                    .sigs
                    .get(*func)
                    .ok_or_else(|| internal("call to a function outside the program"))?;
                let mut rendered = vec!["NULL".to_string()];
                for (index, arg) in args.iter().enumerate() {
                    let index = u16::try_from(index).unwrap_or(u16::MAX);
                    rendered.push(match sig.param(index) {
                        Some(layout) => match (frame.class(*arg), arg) {
                            (Some(class), Operand::Local(id)) if class == layout => {
                                format!("x{id}")
                            }
                            _ => format!("talk_unbox_l{layout}({})", frame.value(*arg)?),
                        },
                        None => frame.value(*arg)?,
                    });
                }
                let call = format!("{}({})", symbol(*func), rendered.join(", "));
                match sig.ret {
                    Some(ret) if frame.class_of(*dest) == Some(ret) => {
                        let _ = writeln!(out, "    x{dest} = {call};");
                    }
                    Some(ret) => {
                        let _ = writeln!(out, "    l[{dest}] = talk_box_l{ret}({call});");
                    }
                    None => {
                        let _ = writeln!(out, "    l[{dest}] = {call};");
                    }
                }
                let stub = sus.active && sus.marked.get(*func).copied().unwrap_or(false);
                if stub {
                    // A resumable callee's impl computes the uniform
                    // value directly, so re-entry lands in the same
                    // representation the normal path boxed into l[].
                    let k = sus.reserve();
                    let _ = writeln!(out, "    goto j{k};");
                    let _ = writeln!(out, "r{k}:");
                    let _ = writeln!(out, "    l[{dest}] = talk_reenter(fr->child);");
                    let _ = writeln!(out, "j{k}: ;");
                    emit_unwind_check(out, *unwind, identified, frame);
                    emit_suspend_stub(out, k);
                } else {
                    emit_unwind_check(out, *unwind, identified, frame);
                }
            }
            Inst::CallIndirect {
                dest,
                callee,
                args,
                unwind,
            } => {
                let callee = frame.value(*callee)?;
                let _ = writeln!(out, "    {{");
                // Sized to the widest function in the program, not to this
                // site's argument count. `talk_dispatch` reads `args[i]`
                // for every arity it can dispatch to, and the C compiler
                // inlines it without knowing which case the tag selects --
                // a shorter array is an out-of-bounds read on paths that
                // never execute.
                let width = self.widest_arity.max(1);
                let _ = writeln!(out, "        TalkValue a[{width}];");
                for (index, arg) in args.iter().enumerate() {
                    let _ = writeln!(out, "        a[{index}] = {};", frame.value(*arg)?);
                }
                // The slots past this call's own arguments are never read
                // on a reachable path, but they are copied by value into
                // the wider cases of the dispatch switch.
                if args.len() < width {
                    let _ = writeln!(
                        out,
                        "        memset(a + {}, 0, sizeof(TalkValue) * {});",
                        args.len(),
                        width - args.len()
                    );
                }
                let _ = writeln!(
                    out,
                    "        l[{dest}] = talk_dispatch({callee}.v.agg->meta, {callee}.v.agg->fields, a);"
                );
                let _ = writeln!(out, "    }}");
                let stub = sus.active && sus.closures_suspend;
                if stub {
                    let k = sus.reserve();
                    let _ = writeln!(out, "    goto j{k};");
                    let _ = writeln!(out, "r{k}:");
                    let _ = writeln!(out, "    l[{dest}] = talk_reenter(fr->child);");
                    let _ = writeln!(out, "j{k}: ;");
                    emit_unwind_check(out, *unwind, identified, frame);
                    emit_suspend_stub(out, k);
                } else {
                    emit_unwind_check(out, *unwind, identified, frame);
                }
            }
            Inst::MakeClosure { dest, func, env } => {
                let _ = writeln!(out, "    {{");
                let _ = writeln!(
                    out,
                    "        TalkValue built = talk_closure({func}, {});",
                    env.len()
                );
                for (index, captured) in env.iter().enumerate() {
                    let _ = writeln!(
                        out,
                        "        built.v.agg->fields[{index}] = {};",
                        frame.value(*captured)?
                    );
                }
                let _ = writeln!(out, "        l[{dest}] = built;");
                let _ = writeln!(out, "    }}");
            }
            Inst::EnvGet { dest, index } => {
                let _ = writeln!(out, "    l[{dest}] = env[{index}];");
            }
            Inst::MakeCont { dest } => {
                let _ = writeln!(out, "    l[{dest}] = talk_cont(frame_depth, frame_id);");
            }
            Inst::PushHandler {
                effect,
                clause,
                cont,
                binds,
            } => {
                let _ = writeln!(
                    out,
                    "    talk_push_handler({}, {}, {}, {}, frame_depth, frame_id);",
                    self.interners.effect(*effect),
                    frame.value(*clause)?,
                    frame.value(*cont)?,
                    i32::from(*binds)
                );
            }
            Inst::FindHandler {
                clause,
                cont,
                index,
                binds,
                effect,
            } => {
                let _ = writeln!(
                    out,
                    "    talk_find_handler({}, &l[{clause}], &l[{cont}], &l[{index}], &l[{binds}]);",
                    self.interners.effect(*effect)
                );
            }
            Inst::GetFloor { dest } => {
                let _ = writeln!(out, "    l[{dest}] = talk_get_floor();");
            }
            Inst::SetFloor { src } => {
                let _ = writeln!(out, "    talk_set_floor({});", frame.value(*src)?);
            }
            Inst::AbortTo { cont, value } => {
                let returned = frame.return_value(*value)?;
                let cont = frame.value(*cont)?;
                let value = frame.value(*value)?;
                // Aborting to the aborting frame's own continuation is an
                // ordinary return: there are no suspended frames between
                // here and the delimiter.
                if identified {
                    let _ = writeln!(
                        out,
                        "    if (talk_cont_depth({cont}) == frame_depth && talk_cont_frame({cont}) == frame_id) {{"
                    );
                    let _ = writeln!(out, "        talk_leave();");
                    let _ = writeln!(out, "        return {returned};");
                    let _ = writeln!(out, "    }}");
                }
                let _ = writeln!(out, "    talk_abort_to({cont}, {value});");
                emit_return(out, &frame.unwind_value(), identified);
            }
            // Literal values are cached immutable aggregates over the
            // module's static bytes. Loading one is a pointer copy even
            // when the site executes repeatedly in a loop.
            Inst::StringLit {
                dest,
                bytes,
                layout,
                storage_layout: _,
            } => {
                let literal =
                    self.interners
                        .intern_static_string(bytes, *layout, MirSymbol::STRING);
                let _ = writeln!(out, "    l[{dest}] = talk_static_string({literal});");
            }
            Inst::BytesLit { dest, bytes } => {
                let offset = self.interners.intern_static(bytes);
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_pointer(talk_statics + {offset});"
                );
            }
            Inst::CellNew { dest, init } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_cell_new({});",
                    frame.value(*init)?
                );
            }
            Inst::CellGet { dest, cell } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_cell_get({});",
                    frame.value(*cell)?
                );
            }
            Inst::CellSet { cell, src } => {
                let _ = writeln!(
                    out,
                    "    talk_cell_set({}, {});",
                    frame.value(*cell)?,
                    frame.value(*src)?
                );
            }
            Inst::ExistentialPack {
                dest,
                protocol,
                payload,
                witnesses,
            } => {
                // Carries the protocol's display identity so a result
                // renders as its payload, not as the witness table.
                let symbol = self.interners.display_id(*protocol);
                self.interners.existential_ids.insert(symbol);
                // Payload first, witnesses after, in one aggregate: slot 0
                // drop, slot 1 retain, requirements from 2.
                let _ = writeln!(out, "    {{");
                let _ = writeln!(
                    out,
                    "        TalkValue built = talk_agg(TALK_DYN, {symbol}, 0, {});",
                    witnesses.len() + 1
                );
                let _ = writeln!(
                    out,
                    "        built.v.agg->fields[0] = {};",
                    frame.value(*payload)?
                );
                for (index, witness) in witnesses.iter().enumerate() {
                    let _ = writeln!(
                        out,
                        "        built.v.agg->fields[{}] = {};",
                        index + 1,
                        frame.value(*witness)?
                    );
                }
                let _ = writeln!(out, "        l[{dest}] = built;");
                let _ = writeln!(out, "    }}");
            }
            Inst::ExistentialPayload { dest, src } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_existential_payload({});",
                    frame.value(*src)?
                );
            }
            Inst::ExistentialWitness { dest, src, index } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_existential_witness({}, {index});",
                    frame.value(*src)?
                );
            }
            Inst::GetElement {
                dest,
                src,
                element,
                index,
            } => {
                // Inline elements stride by their width and read as
                // spliced children; every other element is one slot.
                let inline = matches!(
                    frame
                        .facts
                        .table
                        .get(usize::try_from(*element).unwrap_or(usize::MAX)),
                    Some(Layout::Inline(_, _))
                );
                if inline {
                    let stride = frame.facts.width_of(*element)?;
                    let symbol = self.display_of(frame.facts.table, *element);
                    let _ = writeln!(
                        out,
                        "    l[{dest}] = talk_get_element_slice({}, {}, {stride}, {element}u, {symbol});",
                        frame.value(*src)?,
                        frame.value(*index)?
                    );
                } else {
                    let _ = writeln!(
                        out,
                        "    l[{dest}] = talk_get_element({}, {});",
                        frame.value(*src)?,
                        frame.value(*index)?
                    );
                }
            }
            Inst::ObjectNew { dest, args } => {
                let _ = writeln!(out, "    {{");
                let _ = writeln!(
                    out,
                    "        TalkValue built = talk_object_new({});",
                    args.len()
                );
                for (index, arg) in args.iter().enumerate() {
                    let _ = writeln!(
                        out,
                        "        built.v.obj->fields[{index}] = {};",
                        frame.value(*arg)?
                    );
                }
                let _ = writeln!(out, "        l[{dest}] = built;");
                let _ = writeln!(out, "    }}");
            }
            Inst::ObjectGet { dest, src, index } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = {}.v.obj->fields[{index}];",
                    frame.value(*src)?
                );
            }
            Inst::ObjectSet { obj, src, index } => {
                let _ = writeln!(
                    out,
                    "    talk_object_set({}, {index}, {});",
                    frame.value(*obj)?,
                    frame.value(*src)?
                );
            }
            Inst::RegionAcquire { src } => {
                let _ = writeln!(out, "    talk_region_acquire({});", frame.value(*src)?);
            }
            Inst::RegionRelease { src } => {
                let _ = writeln!(out, "    talk_region_release({});", frame.value(*src)?);
            }
            Inst::SetFinalizer { obj, closure } => {
                let _ = writeln!(
                    out,
                    "    {}.v.obj->finalizer = {};",
                    frame.value(*obj)?,
                    frame.value(*closure)?
                );
            }
            Inst::Io { dest, op, a, b, c } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_int(talk_io({op}, {}, {}, {}));",
                    frame.value(*a)?,
                    frame.value(*b)?,
                    frame.value(*c)?
                );
            }
            Inst::TaskSpawn { dest, arg, worker } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_int(talk_task_spawn({}, {}));",
                    frame.value(*arg)?,
                    frame.value(*worker)?
                );
            }
            Inst::TaskJoin { dest, handle } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_task_join({});",
                    frame.value(*handle)?
                );
            }
            Inst::TaskWidth { dest } => {
                let _ = writeln!(out, "    l[{dest}] = talk_int(talk_task_width());");
            }
            Inst::ChanSend { handle, value } => {
                let _ = writeln!(
                    out,
                    "    talk_chan_send({}, {});",
                    frame.value(*handle)?,
                    frame.value(*value)?
                );
            }
            Inst::ChanTake { dest, handle } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_chan_take({});",
                    frame.value(*handle)?
                );
            }
            Inst::Suspend {
                dest,
                effect,
                args,
                entry,
                unwind,
            } => {
                // ADR 0065: record the in-flight suspension, link this
                // frame, and either land it (this frame installed the
                // handler: run the clause and return its result on the
                // native return path) or propagate the status outward.
                if !sus.active {
                    // ADR 0068: this function is outside the resumable
                    // set, which the fixpoint derived from binding
                    // PushHandlers — no binding clause exists for this
                    // effect anywhere in the program, so the branch arm
                    // holding this site is unreachable.
                    let _ = writeln!(
                        out,
                        "    talk_trap(\"a perform matched a resumption-binding handler the compiler proved absent\");"
                    );
                    return Ok(());
                }
                let k = sus.reserve();
                let effect = self.interners.effect(*effect);
                let _ = writeln!(out, "    {{");
                let _ = writeln!(out, "        TalkValue sa[{}];", args.len().max(1));
                if args.is_empty() {
                    let _ = writeln!(out, "        memset(sa, 0, sizeof sa);");
                }
                for (index, arg) in args.iter().enumerate() {
                    let _ = writeln!(out, "        sa[{index}] = {};", frame.value(*arg)?);
                }
                let _ = writeln!(
                    out,
                    "        talk_suspend_begin({effect}, sa, {}, {});",
                    args.len(),
                    frame.value(*entry)?
                );
                let _ = writeln!(out, "    }}");
                let _ = writeln!(out, "    fr->rpc = {k};");
                let _ = writeln!(out, "    talk_suspend_link(fr);");
                let _ = writeln!(out, "    if (talk_suspend_is_mine(frame_id)) {{");
                let _ = writeln!(out, "        TalkValue sr = talk_suspend_finish(frame_depth);");
                let _ = writeln!(out, "        talk_leave();");
                let _ = writeln!(out, "        talk_frame_detached = 1;");
                let _ = writeln!(out, "        return sr;");
                let _ = writeln!(out, "    }}");
                let _ = writeln!(out, "    talk_leave();");
                let _ = writeln!(out, "    talk_frame_detached = 1;");
                let _ = writeln!(out, "    return talk_unit();");
                let _ = writeln!(out, "r{k}:");
                // Re-entry delivers the resume value — or, under a
                // cancellation (the unwind status pre-set), routes into
                // this site's cleanup edge like any aborted call.
                let _ = writeln!(out, "    if (talk_unwinding) {{");
                match unwind {
                    Some(block) => {
                        let _ = writeln!(out, "        goto b{block};");
                    }
                    None => {
                        let _ = writeln!(out, "        talk_leave();");
                        let _ = writeln!(out, "        return talk_unit();");
                    }
                }
                let _ = writeln!(out, "    }}");
                let _ = writeln!(out, "    l[{dest}] = talk_resume_take();");
            }
            Inst::Resume { dest, cont, value } => {
                let call = format!(
                    "talk_resume_extent({}, {})",
                    frame.value(*cont)?,
                    frame.value(*value)?
                );
                match frame.class_of(*dest) {
                    Some(layout) => {
                        let _ = writeln!(out, "    x{dest} = talk_unbox_l{layout}({call});");
                    }
                    None => {
                        let _ = writeln!(out, "    l[{dest}] = {call};");
                    }
                }
            }
            Inst::Cancel { cont } => {
                let _ = writeln!(out, "    talk_cancel_extent({});", frame.value(*cont)?);
            }
            Inst::ChanCtl { dest, handle, op } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_int(talk_chan_ctl({}, {}));",
                    frame.value(*handle)?,
                    frame.value(*op)?
                );
            }
            Inst::Alloc { dest, bytes } => {
                let _ = writeln!(out, "    l[{dest}] = talk_alloc({});", frame.value(*bytes)?);
            }
            Inst::Free { src } => {
                let _ = writeln!(out, "    talk_free({});", frame.value(*src)?);
            }
            Inst::RetainPtr { src } => {
                let _ = writeln!(out, "    talk_retain({});", frame.value(*src)?);
            }
            Inst::IsUnique { dest, src } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_is_unique({});",
                    frame.value(*src)?
                );
            }
            Inst::PtrAdd {
                dest,
                ptr,
                offset,
                size,
            } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_ptr_add({}, {}, {size});",
                    frame.value(*ptr)?,
                    frame.value(*offset)?
                );
            }
            Inst::MemCopy { from, to, len } => {
                let _ = writeln!(
                    out,
                    "    talk_mem_copy({}, {}, {});",
                    frame.value(*from)?,
                    frame.value(*to)?,
                    frame.value(*len)?
                );
            }
            Inst::Load { dest, ptr, kind } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = {}({});",
                    load_helper(*kind),
                    frame.value(*ptr)?
                );
            }
            Inst::Store { ptr, src, kind } => {
                let _ = writeln!(
                    out,
                    "    {};",
                    store(*kind, &frame.value(*ptr)?, &frame.value(*src)?)
                );
            }
            Inst::GlobalLoad { dest, global } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_load_boxed(talk_pointer(talk_globals + {}));",
                    u64::from(*global) * 8
                );
            }
            Inst::GlobalStore { global, src } => {
                let _ = writeln!(
                    out,
                    "    talk_store_boxed(talk_pointer(talk_globals + {}), {});",
                    u64::from(*global) * 8,
                    frame.value(*src)?
                );
            }
            // A blank record awaiting its initializer. Nothing observes
            // an unassigned field (definite assignment on the happy
            // path, per-field shadows on the abort path), so a
            // box-native receiver is simply zeroed storage; other
            // receivers keep the tagged aggregate of Units.
            Inst::Blank { dest, layout } => {
                let symbol = self.display_of(frame.facts.table, *layout);
                if frame.facts.boxes_native(*layout) {
                    let _ = writeln!(out, "    {{");
                    let _ = writeln!(
                        out,
                        "        TalkValue built = talk_native_box({layout}u, {symbol}, sizeof(TalkL{layout}));"
                    );
                    let _ = writeln!(
                        out,
                        "        memset(TALK_NATIVE_PAYLOAD(built), 0, sizeof(TalkL{layout}));"
                    );
                    let _ = writeln!(out, "        l[{dest}] = built;");
                    let _ = writeln!(out, "    }}");
                } else {
                    let Shape::Product { reprs, .. } = frame.facts.shape_of(*layout)? else {
                        return Err(internal("a blank receiver under a non-product layout"));
                    };
                    let args = vec![Operand::Const(Constant::Unit); reprs.len()];
                    emit_construction(
                        out,
                        *dest,
                        0,
                        *layout,
                        &args,
                        frame_slot,
                        frame,
                        Sink::Tagged { symbol },
                    )?
                }
            }
            Inst::Aggregate {
                dest,
                tag,
                layout,
                args,
            } => {
                let sink = if frame.class_of(*dest).is_some() {
                    Sink::NativeLocal
                } else if frame.facts.boxes_native(*layout) {
                    Sink::NativeTemp
                } else {
                    Sink::Tagged {
                        symbol: self.display_of(frame.facts.table, *layout),
                    }
                };
                emit_construction(out, *dest, *tag, *layout, args, frame_slot, frame, sink)?
            }
            Inst::Field {
                dest,
                src,
                container,
                offset,
                member,
            } => {
                match (frame.class(*src), src) {
                    (Some(layout), Operand::Local(src)) => {
                        let kinds = frame.shape(layout)?.kinds();
                        match member {
                            None => {
                                let kind = *kinds
                                    .get(usize::from(*offset))
                                    .ok_or_else(|| internal("a member slot past its layout"))?;
                                let _ = writeln!(
                                    out,
                                    "    l[{dest}] = {};",
                                    retag_kind(kind, &format!("x{src}.m{offset}"))
                                );
                            }
                            // A zero-width member reconstitutes as Unit.
                            Some(child) if frame.facts.width_of(*child)? == 0 => {
                                let _ = writeln!(out, "    l[{dest}] = talk_unit();");
                            }
                            // A spliced member lands whole in a native
                            // destination of its own layout: slot copies,
                            // no boxing.
                            Some(child) if frame.class_of(*dest) == Some(*child) => {
                                let span = frame.facts.width_of(*child)?;
                                for slot in 0..span {
                                    let _ = writeln!(
                                        out,
                                        "    x{dest}.m{slot} = x{src}.m{};",
                                        u32::from(*offset) + slot
                                    );
                                }
                            }
                            Some(child) => {
                                let span = frame.facts.width_of(*child)?;
                                let _ = writeln!(out, "    {{");
                                let _ = writeln!(out, "        TalkL{child} tmp;");
                                for slot in 0..span {
                                    let _ = writeln!(
                                        out,
                                        "        tmp.m{slot} = x{src}.m{};",
                                        u32::from(*offset) + slot
                                    );
                                }
                                let _ =
                                    writeln!(out, "        l[{dest}] = talk_box_l{child}(tmp);");
                                let _ = writeln!(out, "    }}");
                            }
                        }
                    }
                    _ => {
                        let value = frame.value(*src)?;
                        // A box-native container reads its flat payload's
                        // members; a tagged container reads flat slots.
                        if frame.facts.boxes_native(*container) {
                            let payload =
                                format!("((const TalkL{container} *)TALK_NATIVE_PAYLOAD({value}))");
                            match member {
                                None => {
                                    let kind = *frame
                                        .facts
                                        .shape_of(*container)?
                                        .kinds()
                                        .get(usize::from(*offset))
                                        .ok_or_else(|| internal("a member slot past its layout"))?;
                                    let read = retag_kind(kind, &format!("{payload}->m{offset}"));
                                    match frame.class_of(*dest) {
                                        Some(child) => {
                                            let _ = writeln!(
                                                out,
                                                "    x{dest} = talk_unbox_l{child}({read});"
                                            );
                                        }
                                        None => {
                                            let _ = writeln!(out, "    l[{dest}] = {read};");
                                        }
                                    }
                                }
                                Some(child) if frame.facts.width_of(*child)? == 0 => {
                                    let _ = writeln!(out, "    l[{dest}] = talk_unit();");
                                }
                                Some(child) if frame.class_of(*dest) == Some(*child) => {
                                    let span = frame.facts.width_of(*child)?;
                                    for slot in 0..span {
                                        let _ = writeln!(
                                            out,
                                            "    x{dest}.m{slot} = {payload}->m{};",
                                            u32::from(*offset) + slot
                                        );
                                    }
                                }
                                Some(child) => {
                                    let span = frame.facts.width_of(*child)?;
                                    let _ = writeln!(out, "    {{");
                                    let _ = writeln!(out, "        TalkL{child} tmp;");
                                    for slot in 0..span {
                                        let _ = writeln!(
                                            out,
                                            "        tmp.m{slot} = {payload}->m{};",
                                            u32::from(*offset) + slot
                                        );
                                    }
                                    let _ = writeln!(
                                        out,
                                        "        l[{dest}] = talk_box_l{child}(tmp);"
                                    );
                                    let _ = writeln!(out, "    }}");
                                }
                            }
                        } else {
                            let read = match member {
                                None => format!("{value}.v.agg->fields[{offset}]"),
                                Some(child) if frame.facts.width_of(*child)? == 0 => {
                                    "talk_unit()".to_string()
                                }
                                // A box-native child leaves in its native
                                // form, keeping the runtime invariant the
                                // static payload reads depend on.
                                Some(child) if frame.facts.boxes_native(*child) => {
                                    let _ = writeln!(out, "    {{");
                                    let _ = writeln!(out, "        TalkL{child} tmp;");
                                    let kinds = frame.facts.shape_of(*child)?.kinds().to_vec();
                                    for (slot, kind) in kinds.iter().enumerate() {
                                        let _ = writeln!(
                                            out,
                                            "        tmp.m{slot} = {};",
                                            untag_kind(
                                                *kind,
                                                &format!(
                                                    "{value}.v.agg->fields[{}]",
                                                    u32::from(*offset) + slot as u32
                                                )
                                            )
                                        );
                                    }
                                    match frame.class_of(*dest) {
                                        Some(class) if class == *child => {
                                            let _ = writeln!(out, "        x{dest} = tmp;");
                                        }
                                        _ => {
                                            let _ = writeln!(
                                                out,
                                                "        l[{dest}] = talk_box_l{child}(tmp);"
                                            );
                                        }
                                    }
                                    let _ = writeln!(out, "    }}");
                                    return Ok(());
                                }
                                Some(child) => {
                                    let span = frame.facts.width_of(*child)?;
                                    let symbol = self.display_of(frame.facts.table, *child);
                                    format!(
                                        "talk_slice({value}, {offset}, {span}, {child}u, {symbol})"
                                    )
                                }
                            };
                            // The destination can be classed even when the
                            // source degraded to uniform.
                            match frame.class_of(*dest) {
                                Some(child) => {
                                    let _ =
                                        writeln!(out, "    x{dest} = talk_unbox_l{child}({read});");
                                }
                                None => {
                                    let _ = writeln!(out, "    l[{dest}] = {read};");
                                }
                            }
                        }
                    }
                }
            }
            Inst::GetTag { dest, src } => match (frame.class(*src), src) {
                (Some(layout), Operand::Local(src)) => {
                    if !matches!(frame.shape(layout)?, Shape::Sum { .. }) {
                        return Err(internal("a tag read on a native product"));
                    }
                    let _ = writeln!(out, "    l[{dest}] = talk_int(x{src}.m0);");
                }
                _ => {
                    // Flat sums carry the tag in slot 0, already an Int.
                    let _ = writeln!(
                        out,
                        "    l[{dest}] = {}.v.agg->fields[0];",
                        frame.value(*src)?
                    );
                }
            },
            Inst::SetField {
                rec,
                src,
                container,
                offset,
                member,
            } => match frame.class_of(*rec) {
                Some(layout) => {
                    // Native storage is exclusively owned, so the write
                    // is a member store with no copy-on-write check.
                    match member {
                        None => {
                            let kind = *frame
                                .shape(layout)?
                                .kinds()
                                .get(usize::from(*offset))
                                .ok_or_else(|| internal("a member slot past its layout"))?;
                            let _ = writeln!(
                                out,
                                "    x{rec}.m{offset} = {};",
                                untag_kind(kind, &frame.value(*src)?)
                            );
                        }
                        Some(child) if frame.facts.width_of(*child)? == 0 => {}
                        Some(child) if frame.class(*src) == Some(*child) => {
                            let Operand::Local(src) = src else {
                                unreachable!()
                            };
                            let span = frame.facts.width_of(*child)?;
                            for slot in 0..span {
                                let _ = writeln!(
                                    out,
                                    "    x{rec}.m{} = x{src}.m{slot};",
                                    u32::from(*offset) + slot
                                );
                            }
                        }
                        Some(child) => {
                            let span = frame.facts.width_of(*child)?;
                            let value = frame.value(*src)?;
                            let _ = writeln!(out, "    {{");
                            let _ = writeln!(
                                out,
                                "        TalkL{child} sub = talk_unbox_l{child}({value});"
                            );
                            for slot in 0..span {
                                let _ = writeln!(
                                    out,
                                    "        x{rec}.m{} = sub.m{slot};",
                                    u32::from(*offset) + slot
                                );
                            }
                            let _ = writeln!(out, "    }}");
                        }
                    }
                }
                None => {
                    let span = match member {
                        None => 1,
                        Some(child) => frame.facts.width_of(*child)?,
                    };
                    if span == 0 {
                        return Ok(());
                    }
                    // A box-native container stays native across the
                    // write: copy the box, store the member's slots.
                    if frame.facts.boxes_native(*container) {
                        let _ = writeln!(out, "    {{");
                        let _ = writeln!(
                            out,
                            "        TalkValue copy = talk_box_l{container}(talk_unbox_l{container}(l[{rec}]));"
                        );
                        let _ = writeln!(
                            out,
                            "        TalkL{container} *v = (TalkL{container} *)TALK_NATIVE_PAYLOAD(copy);"
                        );
                        match member {
                            None => {
                                let kind = *frame
                                    .facts
                                    .shape_of(*container)?
                                    .kinds()
                                    .get(usize::from(*offset))
                                    .ok_or_else(|| internal("a member slot past its layout"))?;
                                let _ = writeln!(
                                    out,
                                    "        v->m{offset} = {};",
                                    untag_kind(kind, &frame.value(*src)?)
                                );
                            }
                            Some(child) if frame.class(*src) == Some(*child) => {
                                let Operand::Local(src) = src else {
                                    unreachable!()
                                };
                                for slot in 0..span {
                                    let _ = writeln!(
                                        out,
                                        "        v->m{} = x{src}.m{slot};",
                                        u32::from(*offset) + slot
                                    );
                                }
                            }
                            Some(child) => {
                                let value = frame.value(*src)?;
                                let _ = writeln!(
                                    out,
                                    "        TalkL{child} sub = talk_unbox_l{child}({value});"
                                );
                                for slot in 0..span {
                                    let _ = writeln!(
                                        out,
                                        "        v->m{} = sub.m{slot};",
                                        u32::from(*offset) + slot
                                    );
                                }
                            }
                        }
                        let _ = writeln!(out, "        l[{rec}] = copy;");
                        let _ = writeln!(out, "    }}");
                    } else {
                        // The logical setter is copy-on-write over the
                        // flat slots; a spliced write flattens its span.
                        let _ = writeln!(
                            out,
                            "    l[{rec}] = talk_set_slots(l[{rec}], {offset}, {span}, {});",
                            frame.value(*src)?
                        );
                    }
                }
            },
            Inst::FieldIndex { dest, src, index } => {
                // The existential boundary resolves through the value's
                // own published layout at runtime.
                let read = format!("talk_native_field({}, {index})", frame.value(*src)?);
                match frame.class_of(*dest) {
                    Some(child) => {
                        let _ = writeln!(out, "    x{dest} = talk_unbox_l{child}({read});");
                    }
                    None => {
                        let _ = writeln!(out, "    l[{dest}] = {read};");
                    }
                }
            }
            Inst::SetFieldIndex { rec, src, index } => {
                let _ = writeln!(
                    out,
                    "    l[{rec}] = talk_native_set_field(l[{rec}], {index}, {});",
                    frame.value(*src)?
                );
            }
        }
        Ok(())
    }
}

/// Program-wide layout facts the emitter consults everywhere: the
/// published table, which layouts this backend can store natively in
/// frame locals, which are structurally representable as C structs at
/// all, which box natively (payload = the struct, behind TALK_NATIVE),
/// and every function's native signature.
struct Facts<'p> {
    table: &'p [Layout],
    eligible: Vec<bool>,
    structs: Vec<bool>,
    box_native: Vec<bool>,
    sigs: Vec<FnSig>,
}

/// One function's calling convention: which parameters arrive as native
/// structs and whether the result leaves as one. `None` everywhere means
/// the uniform tagged convention.
struct FnSig {
    params: Vec<Option<LayoutId>>,
    ret: Option<LayoutId>,
}

impl FnSig {
    fn param(&self, index: u16) -> Option<LayoutId> {
        self.params.get(usize::from(index)).copied().flatten()
    }
}

impl<'p> Facts<'p> {
    fn new(program: &'p Program) -> Facts<'p> {
        let table = program.layout_table.as_slice();
        let structs = struct_layouts(table);
        let eligible = eligible_layouts(table, &structs);
        let box_native = box_native_layouts(table, &structs);
        let native = |layout: Option<LayoutId>| {
            layout.filter(|layout| {
                eligible
                    .get(usize::try_from(*layout).unwrap_or(usize::MAX))
                    .copied()
                    .unwrap_or(false)
            })
        };
        // Signatures come from published facts alone, never from any
        // one body: every caller and the callee must agree on them.
        let sigs = program
            .functions
            .iter()
            .map(|function| FnSig {
                params: function
                    .param_reprs
                    .iter()
                    .map(|repr| native(repr.layout()))
                    .collect(),
                ret: native(function.return_repr),
            })
            .collect();
        Facts {
            table,
            eligible,
            structs,
            box_native,
            sigs,
        }
    }

    /// Whether a classed local may hold this layout natively.
    fn storable(&self, layout: LayoutId) -> bool {
        self.eligible
            .get(usize::try_from(layout).unwrap_or(usize::MAX))
            .copied()
            .unwrap_or(false)
    }

    /// The shape behind any structurally representable layout.
    fn shape_of(&self, layout: LayoutId) -> Result<&Shape, Error> {
        match self
            .table
            .get(usize::try_from(layout).unwrap_or(usize::MAX))
        {
            Some(Layout::Inline(_, shape) | Layout::Boxed(_, shape)) => Ok(shape),
            _ => Err(internal("a representable layout without a shape")),
        }
    }

    /// A shaped layout's slot count.
    fn width_of(&self, layout: LayoutId) -> Result<u32, Error> {
        Ok(self.shape_of(layout)?.width())
    }

    /// Whether a layout's boxed form is the native struct.
    fn boxes_native(&self, layout: LayoutId) -> bool {
        self.box_native
            .get(usize::try_from(layout).unwrap_or(usize::MAX))
            .copied()
            .unwrap_or(false)
    }
}

/// The C type carrying one function result.
fn return_type(ret: Option<LayoutId>) -> String {
    match ret {
        Some(layout) => format!("TalkL{layout}"),
        None => "TalkValue".to_string(),
    }
}

/// Every function takes the executing closure's environment first, so
/// `talk_dispatch` can call any of them uniformly and `EnvGet` is a
/// plain index. Direct calls pass `NULL`. Native parameters arrive as
/// their structs.
fn parameter_list(arity: u16, sig: &FnSig) -> String {
    let mut rendered = String::from("const TalkValue *env");
    for index in 0..arity {
        match sig.param(index) {
            Some(layout) => {
                let _ = write!(rendered, ", TalkL{layout} p{index}");
            }
            None => {
                let _ = write!(rendered, ", TalkValue p{index}");
            }
        }
    }
    rendered
}

/// Which inline layouts this backend can store natively (ADR 0045): a
/// non-empty inline product whose spliced fields are themselves eligible,
/// or an inline sum whose payload elements are all single slots. Sums
/// with wider elements are excluded because `GetPayload` does not carry
/// the tag, so a read site can only be static when every variant places
/// element `j` at slot `j + 1`. Interning assigns children before
/// parents, so one ascending pass settles the recursion.
/// Layouts a frame local can hold natively: the representable set,
/// restricted to inline roots (spliced children are always inline, so
/// the recursions agree; only the root class differs).
pub fn eligible_layouts(table: &[Layout], structs: &[bool]) -> Vec<bool> {
    table
        .iter()
        .zip(structs)
        .map(|(layout, ok)| *ok && matches!(layout, Layout::Inline(_, _)))
        .collect()
}

/// Layouts representable as C structs at all — `eligible_layouts`
/// without the root inline gate: products (inline OR boxed) whose
/// spliced children are representable or zero-width, and sums whose
/// payload elements are all single slots. Every id in this set gets a
/// `TalkL` declaration.
pub fn struct_layouts(table: &[Layout]) -> Vec<bool> {
    let mut ok = vec![false; table.len()];
    for id in 0..table.len() {
        let shape = match &table[id] {
            Layout::Inline(_, shape) | Layout::Boxed(_, shape) => shape,
            _ => continue,
        };
        if shape.width() == 0 {
            continue;
        }
        ok[id] = match shape {
            Shape::Product { reprs, .. } => reprs.iter().all(|repr| match repr {
                FieldRepr::Slot(_) => true,
                FieldRepr::Spliced(child) => {
                    let index = usize::try_from(*child).unwrap_or(usize::MAX);
                    index < id && (ok[index] || zero_width(table, *child))
                }
            }),
            Shape::Sum { reprs, .. } => reprs
                .iter()
                .flatten()
                .all(|repr| matches!(repr, FieldRepr::Slot(_))),
        };
    }
    ok
}

/// Layouts whose BOXED form stores the native struct behind
/// `TALK_NATIVE` (box and unbox are copies): representable products —
/// except `InlineArray`, whose dynamic element reads need uniform
/// tagged fields. Sums keep tagged boxes.
fn box_native_layouts(table: &[Layout], structs: &[bool]) -> Vec<bool> {
    table
        .iter()
        .enumerate()
        .map(|(id, layout)| {
            let (symbol, shape) = match layout {
                Layout::Inline(symbol, shape) | Layout::Boxed(symbol, shape) => (symbol, shape),
                _ => return false,
            };
            structs.get(id).copied().unwrap_or(false)
                && matches!(shape, Shape::Product { .. })
                && *symbol != Some(MirSymbol::INLINE_ARRAY)
        })
        .collect()
}

/// Whether a layout occupies no slots at all — the unit tuple and empty
/// structs. Such a value has exactly one inhabitant, so native storage
/// omits it and every boundary reconstitutes it as Unit.
fn zero_width(table: &[Layout], layout: LayoutId) -> bool {
    matches!(
        table.get(usize::try_from(layout).unwrap_or(usize::MAX)),
        Some(Layout::Inline(_, shape)) if shape.width() == 0
    )
}

/// Per-function value representations: which locals hold a native struct
/// (`TalkL<n> x<local>`) rather than a slot in the uniform `l[]` array,
/// which of those reabstract into a per-local frame buffer instead of
/// the arena because the escape analysis proved their value never
/// leaves the frame, and what this function's returns carry.
struct Frame<'t> {
    native: Vec<Option<LayoutId>>,
    buffered: Vec<bool>,
    ret: Option<LayoutId>,
    facts: &'t Facts<'t>,
}

impl Frame<'_> {
    fn class_of(&self, local: u16) -> Option<LayoutId> {
        self.native.get(usize::from(local)).copied().flatten()
    }

    fn class(&self, operand: Operand) -> Option<LayoutId> {
        match operand {
            Operand::Local(id) => self.class_of(id),
            Operand::Const(_) => None,
        }
    }

    fn shape(&self, layout: LayoutId) -> Result<&Shape, Error> {
        match self
            .facts
            .table
            .get(usize::try_from(layout).unwrap_or(usize::MAX))
        {
            Some(Layout::Inline(_, shape)) => Ok(shape),
            _ => Err(internal("a native local's layout is not inline")),
        }
    }

    /// The rendered return value for this frame: a native return hands
    /// the struct over directly (or unboxes a uniform source); a uniform
    /// return goes through `value`.
    fn return_value(&self, op: Operand) -> Result<String, Error> {
        match self.ret {
            Some(ret) => match (self.class(op), op) {
                (Some(class), Operand::Local(id)) if class == ret => Ok(format!("x{id}")),
                _ => Ok(format!("talk_unbox_l{ret}({})", self.value(op)?)),
            },
            None => self.value(op),
        }
    }

    /// What an unwind or abort path returns: callers never read it (they
    /// check `talk_unwinding`), so a native return hands back a zeroed
    /// struct where the uniform convention hands back Unit.
    fn unwind_value(&self) -> String {
        match self.ret {
            Some(ret) => format!("(TalkL{ret}){{0}}"),
            None => "talk_unit()".to_string(),
        }
    }

    /// The operand as a tagged `TalkValue`, the representation every
    /// context that is not layout-aware expects. A native local crossing
    /// such a boundary — a call argument, a return, a captured value —
    /// is reabstracted into its uniform boxed form here: into the
    /// local's frame buffer when the value provably stays in the frame,
    /// into the arena otherwise.
    fn value(&self, op: Operand) -> Result<String, Error> {
        match self.class(op) {
            Some(layout) => {
                let Operand::Local(id) = op else {
                    unreachable!()
                };
                if self.buffered.get(usize::from(id)).copied().unwrap_or(false) {
                    Ok(format!("talk_box_l{layout}_in(fx{id}, x{id})"))
                } else {
                    Ok(format!("talk_box_l{layout}(x{id})"))
                }
            }
            None => operand(op),
        }
    }
}

fn kind_type(kind: SlotKind) -> &'static str {
    match kind {
        SlotKind::Int | SlotKind::Bool | SlotKind::Byte => "int64_t",
        SlotKind::F64 => "double",
        SlotKind::Ptr => "unsigned char *",
        SlotKind::Value => "TalkValue",
    }
}

/// A native member rendered back into a tagged `TalkValue`.
fn retag_kind(kind: SlotKind, member: &str) -> String {
    match kind {
        SlotKind::Int => format!("talk_int({member})"),
        SlotKind::Bool => format!("talk_bool({member})"),
        SlotKind::Byte => format!("talk_byte({member})"),
        SlotKind::F64 => format!("talk_float({member})"),
        SlotKind::Ptr => format!("talk_pointer({member})"),
        SlotKind::Value => member.to_string(),
    }
}

/// A tagged `TalkValue` expression rendered as a native member.
fn untag_kind(kind: SlotKind, value: &str) -> String {
    match kind {
        SlotKind::Int | SlotKind::Bool | SlotKind::Byte => format!("{value}.v.i"),
        SlotKind::F64 => format!("{value}.v.f"),
        SlotKind::Ptr => format!("{value}.v.ptr"),
        SlotKind::Value => value.to_string(),
    }
}

/// Suspension-emission context (ADR 0065): active inside a resumable
/// function, where it numbers the re-entry points and knows which
/// callees can carry a suspension out.
struct SusCtx<'a> {
    active: bool,
    next_rpc: u32,
    marked: &'a [bool],
    closures_suspend: bool,
}

impl<'a> SusCtx<'a> {
    fn inert() -> SusCtx<'static> {
        SusCtx {
            active: false,
            next_rpc: 1,
            marked: &[],
            closures_suspend: false,
        }
    }

    fn reserve(&mut self) -> u32 {
        let k = self.next_rpc;
        self.next_rpc += 1;
        k
    }
}

/// The propagation stub after a possibly-suspending call in a resumable
/// function: link this frame into the segment and either land the
/// suspension (this frame installed the target handler) or pass the
/// status to the caller.
fn emit_suspend_stub(out: &mut String, k: u32) {
    let _ = writeln!(out, "    if (talk_suspend_pending) {{");
    let _ = writeln!(out, "        fr->rpc = {k};");
    let _ = writeln!(out, "        talk_suspend_link(fr);");
    // The detach flag is set immediately before each return: the
    // landing path nests arbitrary execution inside talk_suspend_finish,
    // and a flag set earlier would be consumed by an inner invoker.
    let _ = writeln!(out, "        if (talk_suspend_is_mine(frame_id)) {{");
    let _ = writeln!(out, "            TalkValue sr = talk_suspend_finish(frame_depth);");
    let _ = writeln!(out, "            talk_leave();");
    let _ = writeln!(out, "            talk_frame_detached = 1;");
    let _ = writeln!(out, "            return sr;");
    let _ = writeln!(out, "        }}");
    let _ = writeln!(out, "        talk_leave();");
    let _ = writeln!(out, "        talk_frame_detached = 1;");
    let _ = writeln!(out, "        return talk_unit();");
    let _ = writeln!(out, "    }}");
}

/// After any call, an in-flight unwind either ends at this frame or keeps
/// going through this frame's cleanup block.
fn emit_unwind_check(out: &mut String, unwind: Option<usize>, identified: bool, frame: &Frame) {
    let _ = writeln!(out, "    if (talk_unwinding) {{");
    if identified {
        let _ = writeln!(
            out,
            "        if (talk_unwind_targets(frame_depth, frame_id)) {{"
        );
        let _ = writeln!(out, "            talk_leave();");
        // The delivered abort value is this frame's real result, so a
        // native return unboxes it into the convention.
        match frame.ret {
            Some(ret) => {
                let _ = writeln!(
                    out,
                    "            return talk_unbox_l{ret}(talk_unwind_take());"
                );
            }
            None => {
                let _ = writeln!(out, "            return talk_unwind_take();");
            }
        }
        let _ = writeln!(out, "        }}");
    }
    match unwind {
        Some(block) => {
            let _ = writeln!(out, "        goto b{block};");
        }
        None => {
            if identified {
                let _ = writeln!(out, "        talk_leave();");
            }
            let _ = writeln!(out, "        return {};", frame.unwind_value());
        }
    }
    let _ = writeln!(out, "    }}");
}

fn emit_return(out: &mut String, value: &str, identified: bool) {
    if identified {
        let _ = writeln!(out, "    talk_leave();");
    }
    let _ = writeln!(out, "    return {value};");
}

/// Where a construction's members land: an untagged struct in a frame
/// local (`x{dest}.m{n}`), an untagged temporary boxed behind
/// `TALK_NATIVE` on completion, or the tagged fallback aggregate. The
/// sink decides the member expression, the conversion direction, and
/// the prologue/epilogue; the shape decides each argument's member and
/// slot kind.
#[derive(Clone, Copy)]
enum Sink {
    NativeLocal,
    NativeTemp,
    Tagged { symbol: u32 },
}

/// The one construction emitter (ADR 0046): every representation is
/// slot-addressed — resolve each argument's placement from the shape,
/// convert it for the sink, store its slots.
fn emit_construction(
    out: &mut String,
    dest: u16,
    tag: u16,
    layout: LayoutId,
    args: &[Operand],
    frame_slot: Option<usize>,
    frame: &Frame,
    sink: Sink,
) -> Result<(), Error> {
    let shape = frame.facts.shape_of(layout)?;
    let placements: Vec<(u32, FieldRepr)> = match shape {
        Shape::Product { offsets, reprs, .. } => {
            if tag != 0 || reprs.len() != args.len() {
                return Err(internal("a construction's arity disagrees with its layout"));
            }
            offsets.iter().copied().zip(reprs.iter().copied()).collect()
        }
        Shape::Sum {
            payloads, reprs, ..
        } => {
            let offsets = payloads
                .get(usize::from(tag))
                .ok_or_else(|| internal("a variant tag past its layout"))?;
            if offsets.len() != args.len() {
                return Err(internal("a variant's arity disagrees with its layout"));
            }
            offsets
                .iter()
                .copied()
                .zip(reprs[usize::from(tag)].iter().copied())
                .collect()
        }
    };
    let kinds = shape.kinds().to_vec();
    let width = shape.width();
    let is_sum = matches!(shape, Shape::Sum { .. });

    if let Sink::Tagged { symbol } = sink {
        let _ = writeln!(out, "    {{");
        match frame_slot {
            Some(slot) => {
                let _ = writeln!(
                    out,
                    "        TalkValue built = talk_agg_in(f{slot}, {layout}u, {symbol}, 0, {width});"
                );
            }
            None => {
                let _ = writeln!(
                    out,
                    "        TalkValue built = talk_agg({layout}u, {symbol}, 0, {width});"
                );
            }
        }
        if is_sum {
            let _ = writeln!(out, "        built.v.agg->fields[0] = talk_int({tag});");
        }
        for ((offset, repr), arg) in placements.iter().zip(args) {
            match repr {
                FieldRepr::Slot(_) => {
                    let _ = writeln!(
                        out,
                        "        built.v.agg->fields[{offset}] = {};",
                        frame.value(*arg)?
                    );
                }
                FieldRepr::Spliced(child) => {
                    let span = frame.facts.width_of(*child)?;
                    if span == 0 {
                        continue;
                    }
                    if frame.class(*arg) == Some(*child) {
                        let Operand::Local(arg) = arg else {
                            unreachable!()
                        };
                        let child_kinds = frame.facts.shape_of(*child)?.kinds().to_vec();
                        for (slot, kind) in child_kinds.iter().enumerate() {
                            let _ = writeln!(
                                out,
                                "        built.v.agg->fields[{}] = {};",
                                offset + slot as u32,
                                retag_kind(*kind, &format!("x{arg}.m{slot}"))
                            );
                        }
                    } else if matches!(arg, Operand::Const(Constant::Unit)) {
                        // A blank receiver's unassigned span.
                        for slot in 0..span {
                            let _ = writeln!(
                                out,
                                "        built.v.agg->fields[{}] = talk_unit();",
                                offset + slot
                            );
                        }
                    } else if frame.facts.boxes_native(*child) {
                        let child_kinds = frame.facts.shape_of(*child)?.kinds().to_vec();
                        let value = frame.value(*arg)?;
                        let _ = writeln!(out, "        {{");
                        let _ = writeln!(
                            out,
                            "            TalkL{child} sub = talk_unbox_l{child}({value});"
                        );
                        for (slot, kind) in child_kinds.iter().enumerate() {
                            let _ = writeln!(
                                out,
                                "            built.v.agg->fields[{}] = {};",
                                offset + slot as u32,
                                retag_kind(*kind, &format!("sub.m{slot}"))
                            );
                        }
                        let _ = writeln!(out, "        }}");
                    } else {
                        let _ = writeln!(
                            out,
                            "        memcpy(built.v.agg->fields + {offset}, {}.v.agg->fields, {span} * sizeof(TalkValue));",
                            frame.value(*arg)?
                        );
                    }
                }
            }
        }
        let _ = writeln!(out, "        l[{dest}] = built;");
        let _ = writeln!(out, "    }}");
        return Ok(());
    }

    let (target, indent) = match sink {
        Sink::NativeLocal => (format!("x{dest}"), "    "),
        _ => {
            if is_sum {
                return Err(internal("a box-native construction is not a product"));
            }
            let _ = writeln!(out, "    {{");
            let _ = writeln!(out, "        TalkL{layout} tmp;");
            ("tmp".to_string(), "        ")
        }
    };
    if is_sum {
        let _ = writeln!(out, "{indent}{target}.m0 = {tag};");
    }
    for ((offset, repr), arg) in placements.iter().zip(args) {
        match repr {
            FieldRepr::Slot(_) => {
                let kind = *kinds
                    .get(usize::try_from(*offset).unwrap_or(usize::MAX))
                    .ok_or_else(|| internal("a member slot past its layout"))?;
                let _ = writeln!(
                    out,
                    "{indent}{target}.m{offset} = {};",
                    untag_kind(kind, &frame.value(*arg)?)
                );
            }
            FieldRepr::Spliced(child) => {
                let span = frame.facts.width_of(*child)?;
                if span == 0 {
                    continue;
                }
                if frame.class(*arg) == Some(*child) {
                    let Operand::Local(arg) = arg else {
                        unreachable!()
                    };
                    for slot in 0..span {
                        let _ =
                            writeln!(out, "{indent}{target}.m{} = x{arg}.m{slot};", offset + slot);
                    }
                } else {
                    // The dual-form unbox reads native boxes and flat
                    // aggregates alike.
                    let value = frame.value(*arg)?;
                    let _ = writeln!(out, "{indent}{{");
                    let _ = writeln!(
                        out,
                        "{indent}    TalkL{child} sub = talk_unbox_l{child}({value});"
                    );
                    for slot in 0..span {
                        let _ = writeln!(
                            out,
                            "{indent}    {target}.m{} = sub.m{slot};",
                            offset + slot
                        );
                    }
                    let _ = writeln!(out, "{indent}}}");
                }
            }
        }
    }
    if matches!(sink, Sink::NativeTemp) {
        match frame_slot {
            Some(slot) => {
                let _ = writeln!(
                    out,
                    "        l[{dest}] = talk_box_l{layout}_in(f{slot}, tmp);"
                );
            }
            None => {
                let _ = writeln!(out, "        l[{dest}] = talk_box_l{layout}(tmp);");
            }
        }
        let _ = writeln!(out, "    }}");
    }
    Ok(())
}

fn emit_term(
    out: &mut String,
    term: &Term,
    function: &Function,
    identified: bool,
    frame: &Frame,
) -> Result<(), Error> {
    match term {
        Term::Goto(target, args) => emit_goto(out, *target, args, function, frame)?,
        Term::Branch {
            cond,
            then_block,
            else_block,
        } => {
            let _ = writeln!(
                out,
                "    if ({}.v.i) goto b{then_block}; else goto b{else_block};",
                frame.value(*cond)?
            );
        }
        Term::Switch {
            tag,
            targets,
            default,
        } => {
            let _ = writeln!(out, "    switch ({}.v.i) {{", frame.value(*tag)?);
            for (value, target) in targets.iter().enumerate() {
                let _ = writeln!(out, "    case {value}: goto b{target};");
            }
            let _ = writeln!(out, "    default: goto b{default};");
            let _ = writeln!(out, "    }}");
        }
        Term::Return(value) => {
            let rendered = frame.return_value(*value)?;
            emit_return(out, &rendered, identified);
        }
        Term::Trap(message) => {
            let _ = writeln!(out, "    talk_trap(\"{}\");", c_escape(message));
        }
        // The end of a cleanup block: this frame is done, and the unwind
        // continues into the caller.
        Term::UnwindRet => emit_return(out, &frame.unwind_value(), identified),
    }
    Ok(())
}

/// A `Goto` carrying arguments is a parallel copy into the target's block
/// parameters, so every argument is read before any parameter is written.
/// A native block parameter takes its source struct whole; the derivation
/// guarantees the source is a native local of the same layout.
fn emit_goto(
    out: &mut String,
    target: usize,
    args: &[Operand],
    function: &Function,
    frame: &Frame,
) -> Result<(), Error> {
    if args.is_empty() {
        let _ = writeln!(out, "    goto b{target};");
        return Ok(());
    }
    let params = &function
        .blocks
        .get(target)
        .ok_or_else(|| internal("branch to a block that does not exist"))?
        .params;
    if params.len() != args.len() {
        return Err(internal(
            "block argument count does not match its parameters",
        ));
    }
    let _ = writeln!(out, "    {{");
    for (index, (arg, param)) in args.iter().zip(params).enumerate() {
        match frame.class_of(*param) {
            Some(layout) => {
                let Operand::Local(src) = arg else {
                    return Err(internal("a native block parameter fed a constant"));
                };
                if frame.class_of(*src) != Some(layout) {
                    return Err(internal("a native block parameter crossed layout classes"));
                }
                let _ = writeln!(out, "        TalkL{layout} e{index} = x{src};");
            }
            None => {
                let _ = writeln!(out, "        TalkValue e{index} = {};", frame.value(*arg)?);
            }
        }
    }
    for (index, param) in params.iter().enumerate() {
        match frame.class_of(*param) {
            Some(_) => {
                let _ = writeln!(out, "        x{param} = e{index};");
            }
            None => {
                let _ = writeln!(out, "        l[{param}] = e{index};");
            }
        }
    }
    let _ = writeln!(out, "        goto b{target};");
    let _ = writeln!(out, "    }}");
    Ok(())
}

fn scalar(op: ScalarOp, a: Operand, b: Option<Operand>, frame: &Frame) -> Result<String, Error> {
    let helper = match op {
        ScalarOp::IntAdd => "talk_add",
        ScalarOp::IntSub => "talk_sub",
        ScalarOp::IntMul => "talk_mul",
        ScalarOp::IntDiv => "talk_div",
        ScalarOp::IntAnd => "talk_and",
        ScalarOp::IntOr => "talk_or",
        ScalarOp::IntXor => "talk_xor",
        ScalarOp::IntShl => "talk_shl",
        ScalarOp::IntShr => "talk_shr",
        ScalarOp::IntNot => "talk_not",
        // Int, Bool, and Byte comparisons all read the same payload word;
        // byte arithmetic is what the spike leaves out, not byte equality.
        ScalarOp::IntCmp(kind)
        | ScalarOp::BoolCmp(kind)
        | ScalarOp::ByteCmp(kind)
        | ScalarOp::PtrCmp(kind) => comparison(kind),
        ScalarOp::FloatAdd => "talk_float_add",
        ScalarOp::FloatSub => "talk_float_sub",
        ScalarOp::FloatMul => "talk_float_mul",
        ScalarOp::FloatDiv => "talk_float_div",
        ScalarOp::FloatCmp(kind) => float_comparison(kind),
        ScalarOp::FloatToIntTrunc => "talk_float_to_int",
        ScalarOp::IntToFloat => "talk_int_to_float",
        ScalarOp::ByteAnd => "talk_byte_and",
        ScalarOp::ByteOr => "talk_byte_or",
        ScalarOp::ByteXor => "talk_byte_xor",
        ScalarOp::ByteShl => "talk_byte_shl",
        ScalarOp::ByteShr => "talk_byte_shr",
        ScalarOp::ByteNot => "talk_byte_not",
        ScalarOp::ByteToInt => "talk_byte_to_int",
        ScalarOp::IntToByte => "talk_int_to_byte",
    };
    let a = frame.value(a)?;
    Ok(match b {
        Some(b) => format!("{helper}({a}, {})", frame.value(b)?),
        None => format!("{helper}({a})"),
    })
}

impl Emitter {
    /// Struct declarations and boxing/unboxing helpers for every layout
    /// some function stored natively, plus the spliced children those
    /// layouts embed. Ascending id order is dependency order: interning
    /// assigns children before parents.
    fn layout_decls(&mut self, out: &mut String, facts: &Facts) -> Result<(), Error> {
        // Children intern before parents, so ascending ids declare every
        // spliced member type before its first use.
        for id in 0..facts.table.len() {
            if facts.structs[id] {
                self.layout_decl(out, u32::try_from(id).unwrap_or(u32::MAX), facts)?;
            }
        }
        self.native_dispatchers(out, facts)?;
        Ok(())
    }

    /// The four program-wide native-box entry points the prelude
    /// forward-declares: the logical field read and write (the
    /// existential boundary's dynamic container), the tagged conversion
    /// rendering uses, and the region scan's walk. Emitted even when no
    /// layout boxes natively, so the prototypes always resolve.
    fn native_dispatchers(&mut self, out: &mut String, facts: &Facts) -> Result<(), Error> {
        let boxed: Vec<LayoutId> = (0..facts.table.len())
            .filter(|id| facts.box_native[*id])
            .map(|id| u32::try_from(id).unwrap_or(u32::MAX))
            .collect();

        let _ = writeln!(
            out,
            "
static TalkValue talk_native_retag(TalkValue value) {{"
        );
        let _ = writeln!(out, "    switch (value.v.native->layout) {{");
        for id in &boxed {
            let _ = writeln!(
                out,
                "    case {id}: return talk_retag_l{id}(*(const TalkL{id} *)TALK_NATIVE_PAYLOAD(value));"
            );
        }
        let _ = writeln!(out, "    }}");
        let _ = writeln!(
            out,
            "    return talk_unit();
}}"
        );

        // Children of box-native layouts must be TALK_NATIVE wherever
        // the emitter reasons statically; the table-driven paths rebox
        // the flat slices they build.
        let _ = writeln!(
            out,
            "
static TalkValue talk_rebox(uint32_t layout, TalkValue flat) {{"
        );
        let _ = writeln!(out, "    switch (layout) {{");
        for id in &boxed {
            let _ = writeln!(
                out,
                "    case {id}: return talk_box_l{id}(talk_unbox_l{id}(flat));"
            );
        }
        let _ = writeln!(out, "    }}");
        let _ = writeln!(
            out,
            "    return flat;
}}"
        );

        let _ = writeln!(
            out,
            "
static void talk_native_scan(TalkValue value, struct TalkObject ***out, size_t *count,
                             size_t *capacity) {{"
        );
        let _ = writeln!(out, "    switch (value.v.native->layout) {{");
        for id in &boxed {
            let has_handles = facts
                .shape_of(*id)?
                .kinds()
                .iter()
                .any(|kind| matches!(kind, SlotKind::Value));
            if has_handles {
                let _ = writeln!(
                    out,
                    "    case {id}: talk_scan_l{id}((const TalkL{id} *)TALK_NATIVE_PAYLOAD(value), out, count, capacity); break;"
                );
            }
        }
        let _ = writeln!(out, "    default: break;");
        let _ = writeln!(
            out,
            "    }}
}}"
        );
        Ok(())
    }

    fn layout_decl(&mut self, out: &mut String, id: LayoutId, facts: &Facts) -> Result<(), Error> {
        let table = facts.table;
        let Some(Layout::Inline(symbol, shape) | Layout::Boxed(symbol, shape)) =
            table.get(usize::try_from(id).unwrap_or(usize::MAX))
        else {
            return Err(internal("a representable layout without a shape"));
        };
        let display = symbol.map(|symbol| self.interners.display_id(symbol)).unwrap_or(0);
        if facts.box_native[usize::try_from(id).unwrap_or(usize::MAX)] {
            return self.native_box_decl(out, id, display, shape);
        }
        // Slot-addressed everywhere (ADR 0046): the struct is the flat
        // layout — one member per slot, a sum's tag in slot zero — so
        // boxing and unboxing are the same per-slot conversion loop for
        // every shape.
        slot_typedef(out, id, shape);
        let width = shape.width();
        for buffered in [false, true] {
            let (name, arguments, create) = if buffered {
                (
                    format!("talk_box_l{id}_in"),
                    format!("void *storage, TalkL{id} v"),
                    format!("talk_agg_in(storage, {id}u, {display}, 0, {width})"),
                )
            } else {
                (
                    format!("talk_box_l{id}"),
                    format!("TalkL{id} v"),
                    format!("talk_agg({id}u, {display}, 0, {width})"),
                )
            };
            let _ = writeln!(out, "static inline TalkValue {name}({arguments}) {{");
            let _ = writeln!(out, "    TalkValue built = {create};");
            for (slot, kind) in shape.kinds().iter().enumerate() {
                let _ = writeln!(
                    out,
                    "    built.v.agg->fields[{slot}] = {};",
                    retag_kind(*kind, &format!("v.m{slot}"))
                );
            }
            let _ = writeln!(out, "    return built;\n}}");
        }
        let _ = writeln!(
            out,
            "static inline TalkL{id} talk_unbox_l{id}(TalkValue b) {{"
        );
        let _ = writeln!(out, "    TalkL{id} v;");
        for (slot, kind) in shape.kinds().iter().enumerate() {
            let _ = writeln!(
                out,
                "    v.m{slot} = {};",
                untag_kind(*kind, &format!("b.v.agg->fields[{slot}]"))
            );
        }
        let _ = writeln!(out, "    return v;\n}}");
        Ok(())
    }

    /// A box-native product: the struct declaration, copy-based box and
    /// unbox, the tagged conversion rendering uses, and — when any slot
    /// can hold a `'heap` handle — the region scan's member walk.
    fn native_box_decl(
        &mut self,
        out: &mut String,
        id: LayoutId,
        display: u32,
        shape: &Shape,
    ) -> Result<(), Error> {
        slot_typedef(out, id, shape);
        let width = shape.width();
        let _ = writeln!(
            out,
            "static inline TalkValue talk_box_l{id}(TalkL{id} v) {{"
        );
        let _ = writeln!(
            out,
            "    TalkValue built = talk_native_box({id}u, {display}, sizeof(TalkL{id}));"
        );
        let _ = writeln!(out, "    *(TalkL{id} *)TALK_NATIVE_PAYLOAD(built) = v;");
        let _ = writeln!(out, "    return built;\n}}");
        let _ = writeln!(
            out,
            "static inline TalkValue talk_box_l{id}_in(void *storage, TalkL{id} v) {{"
        );
        let _ = writeln!(
            out,
            "    TalkValue built = talk_native_box_in(storage, {id}u, {display});"
        );
        let _ = writeln!(out, "    *(TalkL{id} *)TALK_NATIVE_PAYLOAD(built) = v;");
        let _ = writeln!(out, "    return built;\n}}");
        let _ = writeln!(
            out,
            "static inline TalkL{id} talk_unbox_l{id}(TalkValue b) {{"
        );
        // Box-native values are TALK_NATIVE wherever the emitter reasons
        // statically, but children sliced out of flat parents arrive
        // tagged — accept both forms.
        let _ = writeln!(out, "    if (b.tag == TALK_NATIVE) {{");
        let _ = writeln!(
            out,
            "        return *(const TalkL{id} *)TALK_NATIVE_PAYLOAD(b);"
        );
        let _ = writeln!(out, "    }}");
        let _ = writeln!(out, "    TalkL{id} v;");
        for (slot, kind) in shape.kinds().iter().enumerate() {
            let _ = writeln!(
                out,
                "    v.m{slot} = {};",
                untag_kind(*kind, &format!("b.v.agg->fields[{slot}]"))
            );
        }
        let _ = writeln!(out, "    return v;\n}}");
        // The flat form rendering and the logical boundary use (cold
        // path): the same per-slot retag as an eligible layout's box.
        let _ = writeln!(out, "static TalkValue talk_retag_l{id}(TalkL{id} v) {{");
        let _ = writeln!(out, "    (void)v;");
        let _ = writeln!(
            out,
            "    TalkValue built = talk_agg({id}u, {display}, 0, {width});"
        );
        for (slot, kind) in shape.kinds().iter().enumerate() {
            let _ = writeln!(
                out,
                "    built.v.agg->fields[{slot}] = {};",
                retag_kind(*kind, &format!("v.m{slot}"))
            );
        }
        let _ = writeln!(out, "    return built;\n}}");
        let has_handles = shape
            .kinds()
            .iter()
            .any(|kind| matches!(kind, SlotKind::Value));
        if has_handles {
            let _ = writeln!(
                out,
                "static void talk_scan_l{id}(const TalkL{id} *v, struct TalkObject ***scan_out,\n                            size_t *scan_count, size_t *scan_capacity) {{"
            );
            for (slot, kind) in shape.kinds().iter().enumerate() {
                if matches!(kind, SlotKind::Value) {
                    let _ = writeln!(
                        out,
                        "    talk_scan_handles(v->m{slot}, scan_out, scan_count, scan_capacity);"
                    );
                }
            }
            let _ = writeln!(out, "}}");
        }
        Ok(())
    }
}

/// A representable product's struct typedef: one member per occupied
/// field, in declaration order.
/// A representable layout's struct typedef: the flat form, one member
/// per slot in offset order (ADR 0046) — sums and products identical.
fn slot_typedef(out: &mut String, id: LayoutId, shape: &Shape) {
    let _ = writeln!(out, "\ntypedef struct {{");
    for (slot, kind) in shape.kinds().iter().enumerate() {
        let _ = writeln!(out, "    {} m{slot};", kind_type(*kind));
    }
    let _ = writeln!(out, "}} TalkL{id};");
}

/// The element class is fixed at emit time, so a load is a direct access
/// rather than a dispatch on the kind.
fn load_helper(kind: SlotKind) -> &'static str {
    match kind {
        SlotKind::Byte => "talk_load_byte",
        SlotKind::Int => "talk_load_i64",
        SlotKind::F64 => "talk_load_f64",
        SlotKind::Bool => "talk_load_bool",
        SlotKind::Ptr => "talk_load_ptr",
        SlotKind::Value => "talk_load_boxed",
    }
}

fn store(kind: SlotKind, ptr: &str, src: &str) -> String {
    match kind {
        SlotKind::Byte => format!("talk_store_byte({ptr}, {src})"),
        SlotKind::Int | SlotKind::Bool => format!("talk_store_word({ptr}, {src}.v.i)"),
        SlotKind::F64 => format!("talk_store_f64({ptr}, {src})"),
        SlotKind::Ptr => format!("talk_store_ptr({ptr}, {src})"),
        SlotKind::Value => format!("talk_store_boxed({ptr}, {src})"),
    }
}

fn float_comparison(kind: CmpKind) -> &'static str {
    match kind {
        CmpKind::Eq => "talk_float_cmp_eq",
        CmpKind::Ne => "talk_float_cmp_ne",
        CmpKind::Lt => "talk_float_cmp_lt",
        CmpKind::Le => "talk_float_cmp_le",
        CmpKind::Gt => "talk_float_cmp_gt",
        CmpKind::Ge => "talk_float_cmp_ge",
    }
}

fn comparison(kind: CmpKind) -> &'static str {
    match kind {
        CmpKind::Eq => "talk_cmp_eq",
        CmpKind::Ne => "talk_cmp_ne",
        CmpKind::Lt => "talk_cmp_lt",
        CmpKind::Le => "talk_cmp_le",
        CmpKind::Gt => "talk_cmp_gt",
        CmpKind::Ge => "talk_cmp_ge",
    }
}

fn operand(operand: Operand) -> Result<String, Error> {
    Ok(match operand {
        Operand::Local(id) => format!("l[{id}]"),
        Operand::Const(Constant::Unit) => "talk_unit()".to_string(),
        Operand::Const(Constant::Bool(value)) => format!("talk_bool({})", i32::from(value)),
        Operand::Const(Constant::Int(value)) => format!("talk_int({})", integer(value)),
        // Bit patterns, so no value is lost to a decimal literal.
        Operand::Const(Constant::Float(value)) => {
            format!("talk_float_bits(UINT64_C({}))", value.to_bits())
        }
    })
}

/// `INT64_MIN` has no C literal: the token is a negation of a value one
/// past `INT64_MAX`, which does not fit a signed 64-bit type.
fn integer(value: i64) -> String {
    match value {
        i64::MIN => "(-INT64_C(9223372036854775807) - 1)".to_string(),
        _ => format!("INT64_C({value})"),
    }
}

fn symbol(id: usize) -> String {
    format!("talk_fn{id}")
}

fn unsupported(what: &str) -> Error {
    Error::unsupported(format!("{what} is not supported yet by the C backend"))
}

fn internal(message: &str) -> Error {
    Error::new(format!("C backend: {message}"))
}

/// Function names reach the output inside `/* */`, which does not nest.
fn comment(name: &str) -> String {
    name.replace("/*", "/ *").replace("*/", "* /")
}
