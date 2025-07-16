use std::{
    collections::HashSet,
    path::PathBuf,
    sync::{Arc, Mutex},
};

use crate::diagnostic::Diagnostic;

pub type SharedCompilationSession = Arc<Mutex<CompilationSession>>;

// A shared object for all of compilation, across units
#[derive(Debug, PartialEq, Eq, Default)]
pub struct CompilationSession {
    pub(crate) diagnostics: HashSet<Diagnostic>,
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

    pub fn diagnostics_for(&self, path: &PathBuf) -> HashSet<&Diagnostic> {
        self.diagnostics
            .iter()
            .filter(|d| d.path == *path)
            .collect()
    }

    pub fn _diagnostics(&self) -> &HashSet<Diagnostic> {
        &self.diagnostics
    }

    pub fn add_diagnostic(&mut self, diagnostic: Diagnostic) {
        if diagnostic.is_unhandled() {
            if self.diagnostics.contains(&diagnostic) {
                return;
            }

            tracing::warn!("adding diagnostic to {:?}: {diagnostic:?}", diagnostic.path);
            self.diagnostics.insert(diagnostic);
        }
    }
}
