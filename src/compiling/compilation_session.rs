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
    pub(crate) diagnostics: HashMap<PathBuf, HashSet<Diagnostic>>,
}

impl CompilationSession {
    pub fn new() -> Self {
        Self {
            diagnostics: Default::default(),
        }
    }

    pub fn clear_diagnostics(&mut self) {
        self.diagnostics.clear();
    }

    pub fn diagnostics_for(&self, path: &PathBuf) -> Option<&HashSet<Diagnostic>> {
        self.diagnostics.get(path)
    }

    pub fn _diagnostics(&self) -> &HashMap<PathBuf, HashSet<Diagnostic>> {
        &self.diagnostics
    }

    pub fn add_diagnostic(&mut self, path: PathBuf, diagnostic: Diagnostic) {
        if diagnostic.is_unhandled() {
            log::info!("adding diagnostic to {path:?}: {diagnostic:?}");
            self.diagnostics.entry(path).or_default().insert(diagnostic);
        }
    }
}
