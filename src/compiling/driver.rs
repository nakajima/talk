use std::path::PathBuf;

use crate::{
    FileStore, SourceFile,
    compiling::compilation_unit::{CompilationError, CompilationUnit, Lowered, Parsed},
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

    pub fn parse(&mut self) -> Result<Vec<CompilationUnit<Parsed>>, CompilationError> {
        let mut result = vec![];
        for unit in &mut self.units {
            result.push(unit.parse());
        }
        Ok(result)
    }

    pub fn lower(&mut self) -> Result<Vec<CompilationUnit<Lowered>>, CompilationError> {
        let mut result = vec![];
        for unit in &mut self.units {
            result.push(unit.lower());
        }
        Ok(result)
    }

    pub fn source_file(&mut self, path: &PathBuf) -> Option<SourceFile<source_file::Lowered>> {
        for unit in &mut self.units {
            if let Some(lowered) = unit.lower() {
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

#[cfg(test)]
mod tests {
    use crate::compiling::driver::Driver;

    #[test]
    fn handle_parse_err() {
        let mut driver = Driver::with_files(vec!["../../dev/fixtures/parse_err/fizz.tlk".into()]);
        driver.parse().ok();
    }
}
