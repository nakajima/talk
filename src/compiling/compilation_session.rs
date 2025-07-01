use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
    sync::{Arc, Mutex},
};

use crate::diagnostic::Diagnostic;

pub type SharedCompilationSession = Arc<Mutex<CompilationSession>>;

// A shared object for all of compilation, across units
#[derive(Debug, PartialEq, Eq, Default)]
pub struct CompilationSession {
    diagnostics: HashMap<PathBuf, HashSet<Diagnostic>>,
}

impl CompilationSession {
    pub fn new() -> Self {
        Self {
            diagnostics: Default::default(),
        }
    }

    pub fn clear_diagnostics_for(&mut self, path: &PathBuf) {
        if let Some(diagnostics) = self.diagnostics.get_mut(path) {
            diagnostics.clear()
        }
    }

    pub fn diagnostics(&self) -> &HashMap<PathBuf, HashSet<Diagnostic>> {
        &self.diagnostics
    }

    pub fn add_diagnostic(&mut self, path: PathBuf, diagnostic: Diagnostic) {
        if diagnostic.is_unhandled() {
            log::info!("adding diagnostic to {path:?}: {diagnostic:?}");
            self.diagnostics.entry(path).or_default().insert(diagnostic);
        }
    }
}
