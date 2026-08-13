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
    /// Struct and enum symbols numbered densely from one; zero is the
    /// anonymous product.
    pub display_ids: HashMap<MirSymbol, u32>,
    /// Of those, the ids belonging to protocol existentials, which have
    /// no catalog entry and render as their payload.
    pub existential_ids: HashSet<u32>,
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
