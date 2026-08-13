//! The compiled procedural-macro artifact as pure data (ADR 0057
//! slice 3): what a module carries and caches. Loading it into an
//! executable service — which runs the VM — lives root-side in
//! `procedural_macros`.

use std::collections::BTreeMap;

/// The macro-unit file suffix, also used by the stdlib's embedded
/// source set (wasm has no directory to scan for it).
pub const MACRO_SUFFIX: &str = ".macro.tlk";

/// Serializable compile-time portion of a package module. Dependency modules
/// carry this beside their runtime interface, so macro implementations never
/// need to be rebuilt in the importing package.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct ProceduralMacroArtifact {
    pub image: Vec<u8>,
    pub schema: String,
    pub wrappers: BTreeMap<String, String>,
}

impl std::fmt::Debug for ProceduralMacroArtifact {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ProceduralMacroArtifact")
            .field("macros", &self.wrappers.keys().collect::<Vec<_>>())
            .field("image_bytes", &self.image.len())
            .finish()
    }
}

impl ProceduralMacroArtifact {
    pub fn exported_names(&self) -> impl Iterator<Item = &str> {
        self.wrappers.keys().map(String::as_str)
    }
}
