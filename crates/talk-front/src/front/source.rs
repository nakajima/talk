//! Frontend source vocabulary (ADR 0057 slice 3): the source handle the
//! parser and checker key their inputs by, the frontend's compile error,
//! the export table shape, and the compilation's shared fact table. The
//! driver re-exports these under its historical paths; the frontend
//! modules reference them here and never see the driver.

use std::borrow::Cow;
use std::hash::{Hash, Hasher};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use indexmap::IndexMap;

use crate::name_resolution::symbol::Symbol;
use crate::parser_error::ParserError;

/// Exported names, each carrying its full overload set (ADR 0041):
/// public declarations with one base but different full callable names
/// must not overwrite one another in the export table.
pub type Exports = IndexMap<String, Vec<Symbol>>;

#[derive(Debug)]
pub enum CompileError {
    IO(io::Error),
    Parsing(ParserError),
    Macro(String),
    ImportOutsideWorkspace {
        source: String,
        import_path: String,
        workspace_root: PathBuf,
    },
}

/// The compilation's one fact table (ADR 0053): every module's typecheck
/// reads and writes this catalog; imported modules' slices are seeded
/// exactly once, in import order. Shared across the drivers of one
/// compilation (package graphs, workspaces) via `DriverConfig::catalog`.
#[derive(Default)]
pub struct SharedCatalog {
    pub types: crate::types::catalog::TypeCatalog,
    seeded: rustc_hash::FxHashSet<crate::front::module::StableModuleId>,
}

impl SharedCatalog {
    /// Insert a module's fact slice unless this table has already seen
    /// it. Slices are own-filtered at export, so inserts are disjoint.
    pub fn seed(&mut self, module: &crate::front::module::Module) {
        if self.seeded.insert(module.id) {
            self.types.insert_slice(&module.types.catalog);
        }
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum SourceKind {
    File(PathBuf),
    // Just a string
    String(Arc<str>),
    // Used for core, since they're not necessarily going to be on the fs
    InMemory { path: PathBuf, text: Arc<str> },
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Source {
    kind: SourceKind,
}

impl PartialEq for Source {
    fn eq(&self, other: &Self) -> bool {
        use SourceKind::*;

        match (&self.kind, &other.kind) {
            (File(a), File(b)) => a == b,
            (File(a), InMemory { path: b, .. }) => a == b,
            (InMemory { path: a, .. }, File(b)) => a == b,
            (InMemory { path: a, .. }, InMemory { path: b, .. }) => a == b,

            (String(a), String(b)) => a == b,

            _ => false,
        }
    }
}

impl Eq for Source {}

impl Hash for Source {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use SourceKind::*;

        match &self.kind {
            File(path) | InMemory { path, .. } => {
                0u8.hash(state);
                path.hash(state);
            }
            String(s) => {
                1u8.hash(state);
                s.hash(state);
            }
        }
    }
}

impl From<PathBuf> for Source {
    fn from(value: PathBuf) -> Self {
        Source {
            kind: SourceKind::File(value),
        }
    }
}

impl From<&str> for Source {
    fn from(value: &str) -> Self {
        Source {
            kind: SourceKind::String(Arc::from(value)),
        }
    }
}

impl Source {
    /// The on-disk path of an in-memory source, if it has one (the
    /// driver canonicalizes these against real files when present).
    pub fn in_memory_path(&self) -> Option<&Path> {
        match &self.kind {
            SourceKind::InMemory { path, .. } => Some(path),
            _ => None,
        }
    }

    pub fn in_memory(path: PathBuf, text: impl Into<Arc<str>>) -> Self {
        Self {
            kind: SourceKind::InMemory {
                path,
                text: text.into(),
            },
        }
    }

    pub fn path(&self) -> Cow<'_, str> {
        match &self.kind {
            SourceKind::File(path) => path.to_string_lossy(),
            SourceKind::String(..) => Cow::Borrowed(":memory:"),
            SourceKind::InMemory { path, .. } => path.to_string_lossy(),
        }
    }

    pub fn source_path(&self) -> Option<&Path> {
        match &self.kind {
            SourceKind::File(path) | SourceKind::InMemory { path, .. } => Some(path),
            SourceKind::String(_) => None,
        }
    }

    pub fn read(&self) -> Result<Arc<str>, CompileError> {
        match &self.kind {
            SourceKind::File(path) => std::fs::read_to_string(path).map(Arc::from).map_err(|e| {
                CompileError::IO(std::io::Error::new(
                    e.kind(),
                    format!("{}: {e}", path.display()),
                ))
            }),
            SourceKind::String(string) => Ok(string.clone()),
            SourceKind::InMemory { text, .. } => Ok(text.clone()),
        }
    }
}
