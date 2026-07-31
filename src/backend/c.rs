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

use rustc_hash::FxHashMap;

use super::BackendError;
use super::c_escape::{self, FrameSites};
use super::mir::{CmpKind, Constant, Function, Inst, MemTy, Operand, Program, ScalarOp, Term};
use crate::name_resolution::symbol::Symbol as CompilerSymbol;
use crate::parsing::span::Span;

/// The generated file's runtime half, emitted verbatim ahead of the
/// translated functions.
const PRELUDE: &str = include_str!("c_prelude.c");

/// Whether a display entry names a struct, an enum, or the core String,
/// which the runtime renders as quoted text rather than as a record.
pub(crate) enum TypeKind {
    Record,
    Enum,
    String,
}

/// Type and member names for rendering a result the way the runtime
/// renders one. MIR carries symbols; the names live in the programs'
/// catalogs, so they are read here and emitted as static tables.
#[derive(Default)]
pub(crate) struct DisplayNames {
    entries: FxHashMap<CompilerSymbol, (String, TypeKind, Vec<String>)>,
}

pub(crate) fn display_names(programs: &[super::ProgramInput<'_>]) -> DisplayNames {
    let mut names = DisplayNames::default();
    for input in programs {
        let types = input.program.types();
        let resolved = input.program.resolved_names();
        let name_of = |symbol: &CompilerSymbol| {
            resolved
                .symbol_names
                .get(symbol)
                .cloned()
                .unwrap_or_else(|| format!("{symbol:?}"))
        };
        for (symbol, def) in &types.catalog.enums {
            names.entries.insert(
                *symbol,
                (
                    name_of(symbol),
                    TypeKind::Enum,
                    def.variants.keys().cloned().collect(),
                ),
            );
        }
        for (symbol, def) in &types.catalog.structs {
            let kind = if *symbol == CompilerSymbol::String {
                TypeKind::String
            } else {
                TypeKind::Record
            };
            names.entries.insert(
                *symbol,
                (name_of(symbol), kind, def.fields.keys().cloned().collect()),
            );
        }
    }
    names
}

pub(crate) fn emit(
    program: &Program,
    escaping_parameters: &[Vec<bool>],
    display: &DisplayNames,
) -> Result<String, BackendError> {
    let entry = program
        .functions
        .get(program.entry)
        .ok_or_else(|| internal("entry function is missing"))?;
    if entry.arity != 0 {
        return Err(unsupported("an entry function with parameters"));
    }

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
    let frame_sites = c_escape::frame_sites(program, escaping_parameters);
    let mut bodies = String::new();
    for (id, function) in program.functions.iter().enumerate() {
        emitter.function(&mut bodies, id, function, &frame_sites)?;
    }
    emit_dispatch(&mut bodies, program);

    let mut out = String::from(PRELUDE);
    out.push('\n');
    emit_statics(&mut out, &emitter.statics);
    emit_type_table(&mut out, &emitter, display);
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
            "static TalkValue {}({}); /* {} */",
            symbol(id),
            parameters(function.arity),
            comment(&function.name)
        );
    }
    out.push_str(&bodies);
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
         int status = talk_print({}(NULL));\n    \
         talk_arena_release();\n    \
         talk_effects_release();\n    \
         return status;\n}}\n",
        symbol(program.entry)
    );
    Ok(out)
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
/// closures need no function-pointer types in the generated C.
fn emit_dispatch(out: &mut String, program: &Program) {
    let _ = writeln!(
        out,
        "\nstatic TalkValue talk_dispatch(uint32_t function, const TalkValue *env, const TalkValue *args) {{"
    );
    let _ = writeln!(out, "    (void)args;");
    let _ = writeln!(out, "    switch (function) {{");
    for (id, function) in program.functions.iter().enumerate() {
        let arguments: String = (0..function.arity)
            .map(|index| format!(", args[{index}]"))
            .collect();
        let _ = writeln!(
            out,
            "    case {id}: return {}(env{arguments});",
            symbol(id)
        );
    }
    let _ = writeln!(out, "    default: talk_trap(\"call to an unknown function\");");
    let _ = writeln!(out, "    }}");
    let _ = writeln!(out, "}}");
}

/// The display table, indexed by the ids handed out while emitting. Slot
/// zero is the anonymous product, so `symbol` zero renders as a tuple.
fn emit_type_table(out: &mut String, emitter: &Emitter, display: &DisplayNames) {
    let mut ordered: Vec<(&CompilerSymbol, &u32)> = emitter.display_ids.iter().collect();
    ordered.sort_by_key(|(_, id)| **id);
    for (symbol, id) in &ordered {
        let members = display
            .entries
            .get(symbol)
            .map(|(_, _, members)| members.as_slice())
            .unwrap_or_default();
        if members.is_empty() {
            continue;
        }
        let rendered: Vec<String> = members
            .iter()
            .map(|member| format!("\"{}\"", escape(member)))
            .collect();
        let _ = writeln!(
            out,
            "static const char *const talk_members_{id}[] = {{ {} }};",
            rendered.join(", ")
        );
    }
    let _ = writeln!(out, "static const TalkTypeInfo talk_type_table[] = {{");
    let _ = writeln!(out, "    {{ \"\", TALK_TYPE_TUPLE, 0, NULL }},");
    for (symbol, id) in &ordered {
        if emitter.existential_ids.contains(id) {
            let _ = writeln!(out, "    {{ \"\", TALK_TYPE_EXISTENTIAL, 0, NULL }},");
            continue;
        }
        let (name, kind, members) = match display.entries.get(symbol) {
            Some(entry) => entry,
            // A symbol with no catalog entry renders structurally.
            None => {
                let _ = writeln!(out, "    {{ \"\", TALK_TYPE_TUPLE, 0, NULL }},");
                continue;
            }
        };
        let kind = match kind {
            TypeKind::Record => "TALK_TYPE_RECORD",
            TypeKind::Enum => "TALK_TYPE_ENUM",
            TypeKind::String => "TALK_TYPE_STRING",
        };
        let members_ref = if members.is_empty() {
            "NULL".to_string()
        } else {
            format!("talk_members_{id}")
        };
        let _ = writeln!(
            out,
            "    {{ \"{}\", {kind}, {}, {members_ref} }},",
            escape(name),
            members.len()
        );
    }
    let _ = writeln!(out, "}};");
}

#[derive(Default)]
struct Emitter {
    /// Effect symbols numbered densely, the way `lower`'s `EffectPool`
    /// numbers them for the VM.
    effects: FxHashMap<CompilerSymbol, u32>,
    /// Immortal literal bytes, deduplicated as `lower`'s `StaticsPool`
    /// deduplicates them.
    statics: Vec<u8>,
    static_offsets: FxHashMap<Vec<u8>, u32>,
    /// The widest arity `talk_dispatch` can reach, which sets the size of
    /// every indirect call's argument array.
    widest_arity: usize,
    /// Struct and enum symbols numbered densely from one; zero is the
    /// anonymous product.
    display_ids: FxHashMap<CompilerSymbol, u32>,
    /// Of those, the ids belonging to protocol existentials, which have
    /// no catalog entry and render as their payload.
    existential_ids: rustc_hash::FxHashSet<u32>,
}

impl Emitter {
    fn effect(&mut self, symbol: CompilerSymbol) -> u32 {
        let next = u32::try_from(self.effects.len()).unwrap_or_default();
        *self.effects.entry(symbol).or_insert(next)
    }

    fn display_id(&mut self, symbol: CompilerSymbol) -> u32 {
        let next = u32::try_from(self.display_ids.len() + 1).unwrap_or(1);
        *self.display_ids.entry(symbol).or_insert(next)
    }

    fn intern_static(&mut self, bytes: &[u8]) -> u32 {
        if let Some(offset) = self.static_offsets.get(bytes) {
            return *offset;
        }
        let offset = u32::try_from(self.statics.len()).unwrap_or_default();
        self.statics.extend_from_slice(bytes);
        self.static_offsets.insert(bytes.to_vec(), offset);
        offset
    }

    fn function(
        &mut self,
        out: &mut String,
        id: usize,
        function: &Function,
        frame_sites: &FrameSites,
    ) -> Result<(), BackendError> {
        // Only a frame that names itself can ever be a continuation's
        // target or a handler's installer, so leaf functions stay free of
        // shadow-stack traffic.
        let identified = needs_identity(function);
        let _ = writeln!(
            out,
            "\n/* {} */\nstatic TalkValue {}({}) {{",
            comment(&function.name),
            symbol(id),
            parameters(function.arity)
        );
        // Zero is `TALK_UNIT`, so an unwritten local reads as Unit rather
        // than as whatever the stack held.
        let _ = writeln!(out, "    TalkValue l[{}];", function.n_locals.max(1));
        let _ = writeln!(out, "    memset(l, 0, sizeof l);");
        let _ = writeln!(out, "    (void)env;");
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
                if !frame_sites.contains(&(id, block_index, instruction_index)) {
                    continue;
                }
                let width = match inst {
                    Inst::Record { args, .. }
                    | Inst::Tuple { args, .. }
                    | Inst::Variant { args, .. } => args.len(),
                    _ => continue,
                };
                let slot = storage.len();
                // Raw aligned storage rather than a struct with a
                // `TalkAgg` member: `TalkAgg` ends in a flexible array,
                // and a struct holding one anywhere but last is a GNU
                // extension that clang rejects.
                let _ = writeln!(
                    out,
                    "    _Alignas(TalkValue) unsigned char f{slot}[sizeof(TalkAgg) + {} * sizeof(TalkValue)];",
                    width.max(1)
                );
                storage.insert((block_index, instruction_index), slot);
            }
        }
        for index in 0..function.arity {
            let _ = writeln!(out, "    l[{index}] = p{index};");
        }
        // Entering block zero by `goto` rather than by falling through
        // keeps every emitted label a used one.
        let _ = writeln!(out, "    goto b0;");
        for (index, block) in function.blocks.iter().enumerate() {
            let _ = writeln!(out, "b{index}:");
            for (instruction_index, inst) in block.insts.iter().enumerate() {
                let frame_slot = storage.get(&(index, instruction_index)).copied();
                self.inst(out, inst, identified, frame_slot)?;
            }
            let term = block
                .term
                .as_ref()
                .ok_or_else(|| internal("basic block has no terminator"))?;
            emit_term(out, term, function, identified)?;
        }
        let _ = writeln!(out, "}}");
        Ok(())
    }

    fn inst(
        &mut self,
        out: &mut String,
        inst: &Inst,
        identified: bool,
        frame_slot: Option<usize>,
    ) -> Result<(), BackendError> {
        match inst {
            Inst::Copy { dest, src } => {
                let _ = writeln!(out, "    l[{dest}] = {};", operand(*src)?);
            }
            Inst::Scalar { dest, op, a, b } => {
                let _ = writeln!(out, "    l[{dest}] = {};", scalar(*op, *a, *b)?);
            }
            Inst::Call {
                dest,
                func,
                args,
                unwind,
            } => {
                let mut rendered = vec!["NULL".to_string()];
                for arg in args {
                    rendered.push(operand(*arg)?);
                }
                let _ = writeln!(
                    out,
                    "    l[{dest}] = {}({});",
                    symbol(*func),
                    rendered.join(", ")
                );
                emit_unwind_check(out, *unwind, identified);
            }
            Inst::CallIndirect {
                dest,
                callee,
                args,
                unwind,
            } => {
                let callee = operand(*callee)?;
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
                    let _ = writeln!(out, "        a[{index}] = {};", operand(*arg)?);
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
                    "        l[{dest}] = talk_dispatch({callee}.v.agg->tag, {callee}.v.agg->fields, a);"
                );
                let _ = writeln!(out, "    }}");
                emit_unwind_check(out, *unwind, identified);
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
                        operand(*captured)?
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
            } => {
                let _ = writeln!(
                    out,
                    "    talk_push_handler({}, {}, {}, frame_depth, frame_id);",
                    self.effect(*effect),
                    operand(*clause)?,
                    operand(*cont)?
                );
            }
            Inst::FindHandler {
                clause,
                cont,
                index,
                effect,
            } => {
                let _ = writeln!(
                    out,
                    "    talk_find_handler({}, &l[{clause}], &l[{cont}], &l[{index}]);",
                    self.effect(*effect)
                );
            }
            Inst::GetFloor { dest } => {
                let _ = writeln!(out, "    l[{dest}] = talk_get_floor();");
            }
            Inst::SetFloor { src } => {
                let _ = writeln!(out, "    talk_set_floor({});", operand(*src)?);
            }
            Inst::AbortTo { cont, value } => {
                let cont = operand(*cont)?;
                let value = operand(*value)?;
                // Aborting to the aborting frame's own continuation is an
                // ordinary return: there are no suspended frames between
                // here and the delimiter.
                if identified {
                    let _ = writeln!(
                        out,
                        "    if (talk_cont_depth({cont}) == frame_depth && talk_cont_frame({cont}) == frame_id) {{"
                    );
                    let _ = writeln!(out, "        talk_leave();");
                    let _ = writeln!(out, "        return {value};");
                    let _ = writeln!(out, "    }}");
                }
                let _ = writeln!(out, "    talk_abort_to({cont}, {value});");
                emit_return(out, "talk_unit()", identified);
            }
            // A literal is static bytes behind the core `String` shape:
            // `String { Storage { base }, byte_count, capacity }` (layout
            // owned by core/String.tlk, as `lower` builds it too).
            Inst::StringLit { dest, bytes } => {
                let offset = self.intern_static(bytes);
                // The literal is the core `String` shape over static
                // bytes, so it carries String's display identity and
                // renders as quoted text rather than as a record.
                let string_symbol = self.display_id(CompilerSymbol::String);
                let storage_symbol = self.display_id(CompilerSymbol::Storage);
                let _ = writeln!(out, "    {{");
                let _ = writeln!(out, "        TalkValue storage = talk_agg({storage_symbol}, 0, 1);");
                let _ = writeln!(
                    out,
                    "        storage.v.agg->fields[0] = talk_pointer(talk_statics + {offset});"
                );
                let _ = writeln!(out, "        TalkValue built = talk_agg({string_symbol}, 0, 3);");
                let _ = writeln!(out, "        built.v.agg->fields[0] = storage;");
                let _ = writeln!(
                    out,
                    "        built.v.agg->fields[1] = talk_int({});",
                    bytes.len()
                );
                let _ = writeln!(
                    out,
                    "        built.v.agg->fields[2] = talk_int({});",
                    bytes.len()
                );
                let _ = writeln!(out, "        l[{dest}] = built;");
                let _ = writeln!(out, "    }}");
            }
            Inst::BytesLit { dest, bytes } => {
                let offset = self.intern_static(bytes);
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_pointer(talk_statics + {offset});"
                );
            }
            Inst::CellNew { dest, init } => {
                let _ = writeln!(out, "    l[{dest}] = talk_cell_new({});", operand(*init)?);
            }
            Inst::CellGet { dest, cell } => {
                let _ = writeln!(out, "    l[{dest}] = talk_cell_get({});", operand(*cell)?);
            }
            Inst::CellSet { cell, src } => {
                let _ = writeln!(
                    out,
                    "    talk_cell_set({}, {});",
                    operand(*cell)?,
                    operand(*src)?
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
                let symbol = self.display_id(*protocol);
                self.existential_ids.insert(symbol);
                // Payload first, witnesses after, in one aggregate: slot 0
                // drop, slot 1 retain, requirements from 2.
                let _ = writeln!(out, "    {{");
                let _ = writeln!(
                    out,
                    "        TalkValue built = talk_agg({symbol}, 0, {});",
                    witnesses.len() + 1
                );
                let _ = writeln!(
                    out,
                    "        built.v.agg->fields[0] = {};",
                    operand(*payload)?
                );
                for (index, witness) in witnesses.iter().enumerate() {
                    let _ = writeln!(
                        out,
                        "        built.v.agg->fields[{}] = {};",
                        index + 1,
                        operand(*witness)?
                    );
                }
                let _ = writeln!(out, "        l[{dest}] = built;");
                let _ = writeln!(out, "    }}");
            }
            Inst::ExistentialPayload { dest, src } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_existential_payload({});",
                    operand(*src)?
                );
            }
            Inst::ExistentialWitness { dest, src, index } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_existential_witness({}, {index});",
                    operand(*src)?
                );
            }
            Inst::GetElement { dest, src, index } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_get_element({}, {});",
                    operand(*src)?,
                    operand(*index)?
                );
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
                        operand(*arg)?
                    );
                }
                let _ = writeln!(out, "        l[{dest}] = built;");
                let _ = writeln!(out, "    }}");
            }
            Inst::ObjectGet { dest, src, index } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = {}.v.obj->fields[{index}];",
                    operand(*src)?
                );
            }
            Inst::ObjectSet { obj, src, index } => {
                let _ = writeln!(
                    out,
                    "    talk_object_set({}, {index}, {});",
                    operand(*obj)?,
                    operand(*src)?
                );
            }
            Inst::RegionAcquire { src } => {
                let _ = writeln!(out, "    talk_region_acquire({});", operand(*src)?);
            }
            Inst::RegionRelease { src } => {
                let _ = writeln!(out, "    talk_region_release({});", operand(*src)?);
            }
            Inst::SetFinalizer { obj, closure } => {
                let _ = writeln!(
                    out,
                    "    {}.v.obj->finalizer = {};",
                    operand(*obj)?,
                    operand(*closure)?
                );
            }
            Inst::Io { dest, op, a, b, c } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_int(talk_io({op}, {}, {}, {}));",
                    operand(*a)?,
                    operand(*b)?,
                    operand(*c)?
                );
            }
            Inst::Alloc { dest, bytes } => {
                let _ = writeln!(out, "    l[{dest}] = talk_alloc({});", operand(*bytes)?);
            }
            Inst::Free { src } => {
                let _ = writeln!(out, "    talk_free({});", operand(*src)?);
            }
            Inst::RetainPtr { src } => {
                let _ = writeln!(out, "    talk_retain({});", operand(*src)?);
            }
            Inst::IsUnique { dest, src } => {
                let _ = writeln!(out, "    l[{dest}] = talk_is_unique({});", operand(*src)?);
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
                    operand(*ptr)?,
                    operand(*offset)?
                );
            }
            Inst::MemCopy { from, to, len } => {
                let _ = writeln!(
                    out,
                    "    talk_mem_copy({}, {}, {});",
                    operand(*from)?,
                    operand(*to)?,
                    operand(*len)?
                );
            }
            Inst::Load { dest, ptr, kind } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = {}({});",
                    load_helper(*kind),
                    operand(*ptr)?
                );
            }
            Inst::Store { ptr, src, kind } => {
                let _ = writeln!(out, "    {};", store(*kind, &operand(*ptr)?, &operand(*src)?));
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
                    operand(*src)?
                );
            }
            Inst::Tuple { dest, args } => emit_aggregate(out, *dest, 0, 0, args, frame_slot)?,
            Inst::Record {
                dest,
                struct_symbol,
                args,
            } => {
                let symbol = self.display_id(*struct_symbol);
                emit_aggregate(out, *dest, symbol, 0, args, frame_slot)?
            }
            Inst::Variant {
                dest,
                enum_symbol,
                tag,
                args,
            } => {
                let symbol = self.display_id(*enum_symbol);
                emit_aggregate(out, *dest, symbol, *tag, args, frame_slot)?
            }
            Inst::TupleGet { dest, src, index }
            | Inst::GetField { dest, src, index }
            | Inst::GetPayload { dest, src, index } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = {}.v.agg->fields[{index}];",
                    operand(*src)?
                );
            }
            Inst::GetTag { dest, src } => {
                let _ = writeln!(
                    out,
                    "    l[{dest}] = talk_int((int64_t){}.v.agg->tag);",
                    operand(*src)?
                );
            }
            Inst::SetField { rec, src, index } => {
                let _ = writeln!(
                    out,
                    "    l[{rec}] = talk_set_field(l[{rec}], {index}, {});",
                    operand(*src)?
                );
            }
        }
        Ok(())
    }
}

/// Whether the function reifies its own frame. Continuations only ever
/// name the frame that created them, so a function with no `MakeCont` and
/// no `PushHandler` can neither be an unwind target nor own a handler.
fn needs_identity(function: &Function) -> bool {
    function.blocks.iter().any(|block| {
        block.insts.iter().any(|inst| {
            matches!(
                inst,
                Inst::MakeCont { .. } | Inst::PushHandler { .. } | Inst::AbortTo { .. }
            )
        })
    })
}

/// After any call, an in-flight unwind either ends at this frame or keeps
/// going through this frame's cleanup block.
fn emit_unwind_check(out: &mut String, unwind: Option<usize>, identified: bool) {
    let _ = writeln!(out, "    if (talk_unwinding) {{");
    if identified {
        let _ = writeln!(
            out,
            "        if (talk_unwind_targets(frame_depth, frame_id)) {{"
        );
        let _ = writeln!(out, "            talk_leave();");
        let _ = writeln!(out, "            return talk_unwind_take();");
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
            let _ = writeln!(out, "        return talk_unit();");
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

/// Records, tuples, and enum payloads share one heap shape, so they share
/// one construction sequence.
fn emit_aggregate(
    out: &mut String,
    dest: u16,
    symbol: u32,
    tag: u16,
    args: &[Operand],
    frame_slot: Option<usize>,
) -> Result<(), BackendError> {
    let _ = writeln!(out, "    {{");
    match frame_slot {
        Some(slot) => {
            let _ = writeln!(
                out,
                "        TalkValue built = talk_agg_in(f{slot}, {symbol}, {tag}, {});",
                args.len()
            );
        }
        None => {
            let _ = writeln!(
                out,
                "        TalkValue built = talk_agg({symbol}, {tag}, {});",
                args.len()
            );
        }
    }
    for (index, arg) in args.iter().enumerate() {
        let _ = writeln!(
            out,
            "        built.v.agg->fields[{index}] = {};",
            operand(*arg)?
        );
    }
    let _ = writeln!(out, "        l[{dest}] = built;");
    let _ = writeln!(out, "    }}");
    Ok(())
}

fn emit_term(
    out: &mut String,
    term: &Term,
    function: &Function,
    identified: bool,
) -> Result<(), BackendError> {
    match term {
        Term::Goto(target, args) => emit_goto(out, *target, args, function)?,
        Term::Branch {
            cond,
            then_block,
            else_block,
        } => {
            let _ = writeln!(
                out,
                "    if ({}.v.i) goto b{then_block}; else goto b{else_block};",
                operand(*cond)?
            );
        }
        Term::Switch {
            tag,
            targets,
            default,
        } => {
            let _ = writeln!(out, "    switch ({}.v.i) {{", operand(*tag)?);
            for (value, target) in targets.iter().enumerate() {
                let _ = writeln!(out, "    case {value}: goto b{target};");
            }
            let _ = writeln!(out, "    default: goto b{default};");
            let _ = writeln!(out, "    }}");
        }
        Term::Return(value) => {
            let rendered = operand(*value)?;
            emit_return(out, &rendered, identified);
        }
        Term::Trap(message) => {
            let _ = writeln!(out, "    talk_trap(\"{}\");", escape(message));
        }
        // The end of a cleanup block: this frame is done, and the unwind
        // continues into the caller.
        Term::UnwindRet => emit_return(out, "talk_unit()", identified),
    }
    Ok(())
}

/// A `Goto` carrying arguments is a parallel copy into the target's block
/// parameters, so every argument is read before any parameter is written.
fn emit_goto(
    out: &mut String,
    target: usize,
    args: &[Operand],
    function: &Function,
) -> Result<(), BackendError> {
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
        return Err(internal("block argument count does not match its parameters"));
    }
    let _ = writeln!(out, "    {{");
    for (index, arg) in args.iter().enumerate() {
        let _ = writeln!(out, "        TalkValue e{index} = {};", operand(*arg)?);
    }
    for (index, param) in params.iter().enumerate() {
        let _ = writeln!(out, "        l[{param}] = e{index};");
    }
    let _ = writeln!(out, "        goto b{target};");
    let _ = writeln!(out, "    }}");
    Ok(())
}

fn scalar(op: ScalarOp, a: Operand, b: Option<Operand>) -> Result<String, BackendError> {
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
        ScalarOp::IntCmp(kind) | ScalarOp::BoolCmp(kind) | ScalarOp::ByteCmp(kind) => {
            comparison(kind)
        }
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
    let a = operand(a)?;
    Ok(match b {
        Some(b) => format!("{helper}({a}, {})", operand(b)?),
        None => format!("{helper}({a})"),
    })
}

/// The element class is fixed at emit time, so a load is a direct access
/// rather than a dispatch on the kind.
fn load_helper(kind: MemTy) -> &'static str {
    match kind {
        MemTy::Byte => "talk_load_byte",
        MemTy::I64 => "talk_load_i64",
        MemTy::F64 => "talk_load_f64",
        MemTy::Bool => "talk_load_bool",
        MemTy::Ptr => "talk_load_ptr",
        MemTy::Boxed => "talk_load_boxed",
    }
}

fn store(kind: MemTy, ptr: &str, src: &str) -> String {
    match kind {
        MemTy::Byte => format!("talk_store_byte({ptr}, {src})"),
        MemTy::I64 | MemTy::Bool => format!("talk_store_word({ptr}, {src}.v.i)"),
        MemTy::F64 => format!("talk_store_f64({ptr}, {src})"),
        MemTy::Ptr => format!("talk_store_ptr({ptr}, {src})"),
        MemTy::Boxed => format!("talk_store_boxed({ptr}, {src})"),
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

fn operand(operand: Operand) -> Result<String, BackendError> {
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

/// Every function takes the executing closure's environment first, so
/// `talk_dispatch` can call any of them uniformly and `EnvGet` is a plain
/// index. Direct calls pass `NULL`.
fn parameters(arity: u16) -> String {
    let mut rendered = String::from("const TalkValue *env");
    for index in 0..arity {
        let _ = write!(rendered, ", TalkValue p{index}");
    }
    rendered
}

fn symbol(id: usize) -> String {
    format!("talk_fn{id}")
}

fn unsupported(what: &str) -> BackendError {
    BackendError::unsupported(
        format!("{what} is not supported yet by the C backend"),
        Span::SYNTHESIZED,
    )
}

fn internal(message: &str) -> BackendError {
    BackendError::new(format!("C backend: {message}"), Span::SYNTHESIZED)
}

/// Function names reach the output inside `/* */`, which does not nest.
fn comment(name: &str) -> String {
    name.replace("/*", "/ *").replace("*/", "* /")
}

fn escape(text: &str) -> String {
    text.replace('\\', "\\\\").replace('"', "\\\"")
}
