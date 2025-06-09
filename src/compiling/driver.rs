use std::path::PathBuf;

use crate::{
    FileStore,
    compiling::compilation_unit::{CompilationError, CompilationUnit, Lowered},
};

pub struct Driver {
    units: Vec<CompilationUnit>,
}

impl Driver {
    pub fn with_files(files: Vec<PathBuf>) -> Self {
        let store = FileStore::new(files);
        let unit = CompilationUnit::new(store);
        Self { units: vec![unit] }
    }

    pub fn lower(self) -> Result<Vec<CompilationUnit<Lowered>>, CompilationError> {
        let mut result = vec![];
        for unit in self.units {
            result.push(unit.lower()?);
        }
        Ok(result)
    }
}
