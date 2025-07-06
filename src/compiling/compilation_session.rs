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

    pub fn add_diagnostic(&mut self, diagnostic: Diagnostic) {
        if diagnostic.is_unhandled() {
            tracing::info!("adding diagnostic to {:?}: {diagnostic:?}", diagnostic.path);
            self.diagnostics
                .entry(diagnostic.path.clone())
                .or_default()
                .insert(diagnostic);
        }
    }
}
