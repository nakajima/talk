//! The shared native data-table emission.
//!
//! Both native backends intern the same identities while translating
//! function bodies and render the same runtime-consumed C data tables
//! (`talk_type_table`, `talk_lib_symbols`) from them, so the interners
//! and the byte-identical tables are one definition rather than two
//! that could drift.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use talk_mir::{DisplayNames, Function, Inst, MirSymbol, MirSymbolKind, TypeKind};

/// The identities a backend interns while emitting function bodies,
/// rendered afterward as the runtime's data tables.
#[derive(Default)]
pub struct Interners {
    /// Effect symbols numbered densely, the way `lower`'s `EffectPool`
    /// numbers them for the VM.
    effects: HashMap<MirSymbol, u32>,
    /// Immortal literal bytes, deduplicated as `lower`'s `StaticsPool`
    /// deduplicates them.
    pub statics: Vec<u8>,
    static_offsets: HashMap<Vec<u8>, u32>,
    /// Fully formed immutable string descriptors. The bytes live in
    /// `statics`; generated code loads one cached aggregate instead of
    /// rebuilding the String shape at every literal evaluation.
    pub static_strings: Vec<StaticString>,
    static_string_ids: HashMap<(u32, u32, u32, u32), u32>,
    /// Struct and enum symbols numbered densely from one; zero is the
    /// anonymous product.
    pub display_ids: HashMap<MirSymbol, u32>,
    /// Of those, the ids belonging to protocol existentials, which have
    /// no catalog entry and render as their payload.
    pub existential_ids: HashSet<u32>,
}

#[derive(Clone, Copy, Debug)]
pub struct StaticString {
    pub offset: u32,
    pub len: u32,
    pub layout: u32,
    pub display: u32,
}

impl Interners {
    pub fn effect(&mut self, symbol: MirSymbol) -> u32 {
        let next = u32::try_from(self.effects.len()).unwrap_or_default();
        *self.effects.entry(symbol).or_insert(next)
    }

    pub fn display_id(&mut self, symbol: MirSymbol) -> u32 {
        let next = u32::try_from(self.display_ids.len() + 1).unwrap_or(1);
        *self.display_ids.entry(symbol).or_insert(next)
    }

    pub fn intern_static(&mut self, bytes: &[u8]) -> u32 {
        if let Some(offset) = self.static_offsets.get(bytes) {
            return *offset;
        }
        let offset = u32::try_from(self.statics.len()).unwrap_or_default();
        self.statics.extend_from_slice(bytes);
        self.static_offsets.insert(bytes.to_vec(), offset);
        offset
    }

    pub fn intern_static_string(&mut self, bytes: &[u8], layout: u32, symbol: MirSymbol) -> u32 {
        let offset = self.intern_static(bytes);
        let len = u32::try_from(bytes.len()).unwrap_or_default();
        let display = self.display_id(symbol);
        let key = (offset, len, layout, display);
        *self.static_string_ids.entry(key).or_insert_with(|| {
            let id = u32::try_from(self.static_strings.len()).unwrap_or_default();
            self.static_strings.push(StaticString {
                offset,
                len,
                layout,
                display,
            });
            id
        })
    }
}

/// Emit the immutable descriptor cache shared by both native backends.
/// The cache's malloc-backed aggregates intentionally have process lifetime:
/// module statics and every Static value referring to them have the same
/// lifetime, including across native library calls that clear the arena.
pub fn static_strings(out: &mut String, interners: &Interners) {
    let count = interners.static_strings.len().max(1);
    let _ = writeln!(out, "static TalkValue talk_static_string_cache[{count}];");
    let _ = writeln!(
        out,
        "static TalkValue talk_static_string_tagged_cache[{count}];"
    );
    let _ = writeln!(
        out,
        "static const uint32_t talk_static_string_count = {};",
        interners.static_strings.len()
    );
    out.push_str(
        "typedef struct { uint32_t offset, len, layout, display; } TalkStaticStringDesc;\n",
    );
    let _ = writeln!(
        out,
        "static const TalkStaticStringDesc talk_static_string_descs[{count}] = {{"
    );
    if interners.static_strings.is_empty() {
        out.push_str("    { 0, 0, 0, 0 },\n");
    } else {
        for string in &interners.static_strings {
            let _ = writeln!(
                out,
                "    {{ {}, {}, {}, {} }},",
                string.offset, string.len, string.layout, string.display
            );
        }
    }
    out.push_str("};\n");
    out.push_str(
        "static TalkValue talk_static_string(uint32_t id) {\n\
         \x20   if (id >= talk_static_string_count) talk_trap(\"static string index out of range\");\n\
         \x20   if (talk_static_string_cache[id].tag != TALK_NATIVE) {\n\
         \x20       const TalkStaticStringDesc *desc = &talk_static_string_descs[id];\n\
         \x20       talk_static_string_cache[id] = talk_static_string_value(\n\
         \x20           desc->layout, desc->display, talk_statics + desc->offset, (int64_t)desc->len);\n\
         \x20   }\n\
         \x20   return talk_static_string_cache[id];\n\
         }\n\
         static TalkValue talk_static_string_tagged(uint32_t id) {\n\
         \x20   if (id >= talk_static_string_count) talk_trap(\"static string index out of range\");\n\
         \x20   if (talk_static_string_tagged_cache[id].tag != TALK_AGG) {\n\
         \x20       const TalkStaticStringDesc *desc = &talk_static_string_descs[id];\n\
         \x20       TalkValue value = talk_static_agg(desc->layout, desc->display, 0, 3);\n\
         \x20       value.v.agg->fields[0] = talk_pointer(talk_statics + desc->offset);\n\
         \x20       value.v.agg->fields[1] = talk_int((int64_t)desc->len);\n\
         \x20       value.v.agg->fields[2] = talk_int((int64_t)desc->len);\n\
         \x20       talk_static_string_tagged_cache[id] = value;\n\
         \x20   }\n\
         \x20   return talk_static_string_tagged_cache[id];\n\
         }\n",
    );
}

/// The display-id-to-module-symbol table (ADR 0048): one row per type
/// table entry, so a host bridge can validate record identity against
/// an ABI descriptor's module symbols.
pub fn symbol_rows(out: &mut String, interners: &Interners) {
    out.push_str(crate::library::symbol_row_type());
    let mut rows = vec![(255u8, 0u32, 0u32); interners.display_ids.len() + 1];
    for (symbol, id) in &interners.display_ids {
        let kind = match symbol.kind {
            MirSymbolKind::Struct => 0u8,
            MirSymbolKind::Enum => 1,
            MirSymbolKind::Effect => 2,
            MirSymbolKind::Protocol => 3,
        };
        rows[*id as usize] = (kind, u32::from(symbol.module), symbol.local);
    }
    out.push_str("static const TalkLibSymbolRow talk_lib_symbols[] = {\n");
    for (kind, module, local) in rows {
        let _ = writeln!(out, "    {{ {kind}, {module}, {local} }},");
    }
    out.push_str("};\n");
}

/// The display table, indexed by the ids handed out while emitting. Slot
/// zero is the anonymous product, so `symbol` zero renders as a tuple.
pub fn type_table(out: &mut String, interners: &Interners, display: &DisplayNames) {
    let mut ordered: Vec<_> = interners.display_ids.iter().collect();
    ordered.sort_by_key(|(_, id)| **id);
    for (symbol, id) in &ordered {
        let members = display
            .entries
            .get(*symbol)
            .map(|entry| entry.members.as_slice())
            .unwrap_or_default();
        if members.is_empty() {
            continue;
        }
        let rendered: Vec<String> = members
            .iter()
            .map(|member| format!("\"{}\"", c_escape(member)))
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
        if interners.existential_ids.contains(id) {
            let _ = writeln!(out, "    {{ \"\", TALK_TYPE_EXISTENTIAL, 0, NULL }},");
            continue;
        }
        let Some(entry) = display.entries.get(*symbol) else {
            // A symbol with no catalog entry renders structurally.
            let _ = writeln!(out, "    {{ \"\", TALK_TYPE_TUPLE, 0, NULL }},");
            continue;
        };
        let kind = match entry.kind {
            TypeKind::Record => "TALK_TYPE_RECORD",
            TypeKind::Enum => "TALK_TYPE_ENUM",
            TypeKind::String => "TALK_TYPE_STRING",
        };
        let members_ref = if entry.members.is_empty() {
            "NULL".to_string()
        } else {
            format!("talk_members_{id}")
        };
        let _ = writeln!(
            out,
            "    {{ \"{}\", {kind}, {}, {members_ref} }},",
            c_escape(&entry.name),
            entry.members.len()
        );
    }
    let _ = writeln!(out, "}};");
}

/// Whether the function reifies its own frame. Continuations only ever
/// name the frame that created them, so a function with no `MakeCont` and
/// no `PushHandler` can neither be an unwind target nor own a handler.
/// The functions a native backend must compile in resumable form
/// (ADR 0065): a suspension's return-status propagates through every
/// activation between the perform and its installer, so every function
/// that can dynamically sit on such a path needs a heap frame and
/// re-entry dispatch. Seeds are the `Suspend` sites of *capturable*
/// effects — those with a resumption-binding `PushHandler` anywhere in
/// the finalized program (ADR 0068: the clause kind is derived at the
/// handler, so a perform of an effect nobody binds can never suspend,
/// and its suspend arm is emitted as a trap). Propagation is a
/// call-graph fixpoint over direct calls, with the conservative
/// indirect rule: once any address-taken function is marked, every
/// function containing an indirect call is too. Propagation runs all
/// the way up — a position-aware cutoff at installers is a later
/// precision win, not a correctness need. Sound by construction: an
/// unmarked function contains no reachable suspend and calls only
/// unmarked code, so no suspension can ever arise inside it.
pub fn resumable_functions(functions: &[Function]) -> Vec<bool> {
    let mut capturable: HashSet<MirSymbol> = HashSet::new();
    for function in functions {
        for block in &function.blocks {
            for inst in &block.insts {
                if let Inst::PushHandler {
                    effect,
                    binds: true,
                    ..
                } = inst
                {
                    capturable.insert(*effect);
                }
            }
        }
    }
    let mut marked = vec![false; functions.len()];
    let mut address_taken: Vec<usize> = Vec::new();
    let mut has_indirect = vec![false; functions.len()];
    let mut direct: Vec<Vec<usize>> = vec![Vec::new(); functions.len()];
    for (id, function) in functions.iter().enumerate() {
        for block in &function.blocks {
            for inst in &block.insts {
                match inst {
                    Inst::Suspend { effect, .. } if capturable.contains(effect) => {
                        marked[id] = true
                    }
                    Inst::Suspend { .. } => {}
                    Inst::Call { func, .. } => direct[id].push(*func),
                    Inst::MakeClosure { func, .. } => address_taken.push(*func),
                    Inst::CallIndirect { .. } => has_indirect[id] = true,
                    _ => {}
                }
            }
        }
    }
    loop {
        let mut changed = false;
        let closure_suspends = address_taken
            .iter()
            .any(|&func| marked.get(func).copied().unwrap_or(false));
        for id in 0..functions.len() {
            if marked[id] {
                continue;
            }
            let calls_marked = direct[id]
                .iter()
                .any(|&callee| marked.get(callee).copied().unwrap_or(false));
            if calls_marked || (closure_suspends && has_indirect[id]) {
                marked[id] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    marked
}

pub fn needs_identity(function: &Function) -> bool {
    function.blocks.iter().any(|block| {
        block.insts.iter().any(|inst| {
            matches!(
                inst,
                Inst::MakeCont { .. } | Inst::PushHandler { .. } | Inst::AbortTo { .. }
            )
        })
    })
}

pub fn c_escape(text: &str) -> String {
    text.replace('\\', "\\\\").replace('"', "\\\"")
}
