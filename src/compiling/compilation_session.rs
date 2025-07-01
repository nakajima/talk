use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
    sync::{Arc, Mutex},
};

use crate::diagnostic::Diagnostic;

pub type SharedCompilationSession = Arc<Mutex<CompilationSession>>;

// A shared object for all of compilation, across units
#[derive(Debug, Default, PartialEq, Eq)]
pub struct CompilationSession {
    diagnostics: HashMap<PathBuf, HashSet<Diagnostic>>,
}

impl CompilationSession {
    pub fn diagnostics(&self) -> &HashMap<PathBuf, HashSet<Diagnostic>> {
        &self.diagnostics
    }

    pub fn add_diagnostic(&mut self, path: PathBuf, diagnostic: Diagnostic) {
        self.diagnostics.entry(path).or_default().insert(diagnostic);
    }
}
