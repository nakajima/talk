use std::path::PathBuf;

use async_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};

use crate::{
    SourceFile, SymbolID, SymbolTable,
    compiling::compilation_unit::{CompilationUnit, Lowered, Parsed, Typed},
    prelude::compile_prelude,
    source_file,
};

pub struct Driver {
    pub units: Vec<CompilationUnit>,
    pub symbol_table: SymbolTable,
}

impl Default for Driver {
    fn default() -> Self {
        Self::new()
    }
}

impl Driver {
    pub fn new() -> Self {
        let mut driver = Self {
            units: vec![CompilationUnit::new(vec![])],
            symbol_table: compile_prelude().symbols.clone(),
        };

        // Create a default unit
        driver.units.push(CompilationUnit::new(vec![]));

        driver
    }

    pub fn with_str(string: &str) -> Self {
        let mut driver = Driver::new();
        driver.update_file(&PathBuf::from("-"), string.into());
        driver
    }

    pub fn with_files(files: Vec<PathBuf>) -> Self {
        let unit = CompilationUnit::new(files);
        Self {
            units: vec![unit],
            symbol_table: compile_prelude().symbols.clone(),
        }
    }

    pub fn update_file(&mut self, path: &PathBuf, contents: String) {
        for unit in &mut self.units {
            if unit.has_file(path) {
                unit.src_cache.insert(path.clone(), contents.clone());
                return;
            }
        }

        // We don't have this file, so add it to the default unit
        log::info!("adding {path:?} to default unit");
        self.units[0].input.push(path.to_path_buf());
        self.units[0]
            .src_cache
            .insert(path.clone(), contents.clone());
    }

    pub fn parse(&mut self) -> Vec<CompilationUnit<Parsed>> {
        let mut result = vec![];
        for unit in &mut self.units {
            result.push(unit.parse());
        }
        result
    }

    pub fn lower(&mut self) -> Vec<CompilationUnit<Lowered>> {
        let mut result = vec![];
        for unit in &mut self.units {
            result.push(unit.lower(&mut self.symbol_table));
        }
        result
    }

    pub fn check(&mut self) -> Vec<CompilationUnit<Typed>> {
        let mut result = vec![];
        for unit in &mut self.units {
            let checked = unit
                .parse()
                .resolved(&mut self.symbol_table)
                .typed(&mut self.symbol_table);
            result.push(checked);
        }

        result
    }

    pub fn symbol_from_position(&self, position: Position, path: &PathBuf) -> Option<&SymbolID> {
        for (span, sym) in &self.symbol_table.symbol_map {
            if span.contains(&crate::diagnostic::Position {
                line: position.line,
                col: position.character,
            }) && span.path == *path
            {
                return Some(sym);
            }
        }

        None
    }

    pub fn diagnostics(&mut self, path: &PathBuf) -> Vec<Diagnostic> {
        let lowered = self.lower();
        let mut result = vec![];

        for unit in lowered {
            if unit.has_file(path)
                && let Some(source_file) = unit.source_file(path)
            {
                for diag in &source_file.diagnostics() {
                    let diag_range = diag.range(source_file);
                    let range = Range::new(
                        Position::new(diag_range.0.line, diag_range.0.col),
                        Position::new(diag_range.1.line, diag_range.1.col),
                    );
                    result.push(Diagnostic::new(
                        range,
                        Some(DiagnosticSeverity::ERROR),
                        None,
                        None,
                        diag.message(),
                        None,
                        None,
                    ));
                }
            }
        }

        result
    }

    pub fn has_file(&self, path: &PathBuf) -> bool {
        for unit in &self.units {
            if unit.has_file(path) {
                return true;
            }
        }

        false
    }

    pub fn contents(&self, path: &PathBuf) -> String {
        for unit in &self.units {
            if unit.has_file(path)
                && let Some(contents) = unit.src_cache.get(path)
            {
                return contents.clone();
            }
        }

        "".into()
    }

    pub fn typed_source_file(&mut self, path: &PathBuf) -> Option<SourceFile<source_file::Typed>> {
        let checked = self.check();
        for unit in checked.into_iter() {
            for file in unit.stage.files {
                if *path == file.path {
                    return Some(file);
                }
            }
        }

        None
    }

    pub fn parsed_source_file(
        &mut self,
        path: &PathBuf,
    ) -> Option<SourceFile<source_file::Parsed>> {
        let parsed = self.parse();
        for unit in parsed.into_iter() {
            for file in unit.stage.files {
                if *path == file.path {
                    return Some(file);
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
        driver.parse();
    }
}
