use std::path::PathBuf;

use crate::{
    FileStore, SourceFile,
    compiling::compilation_unit::{CompilationError, CompilationUnit, Lowered},
    source_file,
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

    pub fn lower(&mut self) -> Result<Vec<CompilationUnit<Lowered>>, CompilationError> {
        let mut result = vec![];
        for unit in &mut self.units {
            result.push(unit.lower()?);
        }
        Ok(result)
    }

    pub fn source_file(&mut self, path: &PathBuf) -> Option<SourceFile<source_file::Lowered>> {
        for unit in &mut self.units {
            if let Some(lowered) = unit.lower().ok() {
                for file in lowered.stage.files {
                    if unit.input.id(path) == file.file_id {
                        return Some(file);
                    }
                }
            }
        }

        None
    }
}
