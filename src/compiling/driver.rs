use std::{
    collections::HashSet,
    path::{Path, PathBuf},
};

use async_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};

use crate::{
    SourceFile, SymbolID, SymbolTable,
    compiling::{
        compilation_session::{CompilationSession, SharedCompilationSession},
        compilation_unit::{CompilationUnit, Lowered, Parsed, StageTrait, Typed},
    },
    environment::Environment,
    lowering::ir_module::IRModule,
    prelude::compile_prelude,
    source_file,
};

#[derive(Debug)]
pub struct DriverConfig {
    pub executable: bool,
    pub include_prelude: bool,
}

impl DriverConfig {
    pub fn new_environment(&self, session: SharedCompilationSession) -> Environment {
        if self.include_prelude {
            compile_prelude().environment.clone()
        } else {
            Environment::new(session)
        }
    }
}

impl Default for DriverConfig {
    fn default() -> Self {
        DriverConfig {
            executable: true,
            include_prelude: true,
        }
    }
}

#[derive(Debug)]
pub struct Driver {
    pub units: Vec<CompilationUnit>,
    pub symbol_table: SymbolTable,
    pub config: DriverConfig,
    pub session: SharedCompilationSession,
}

impl Default for Driver {
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl Driver {
    pub fn new(config: DriverConfig) -> Self {
        let session = SharedCompilationSession::new(CompilationSession::new().into());
        let environment = config.new_environment(session.clone());

        Self {
            units: vec![CompilationUnit::new(session.clone(), vec![], environment)],
            symbol_table: if config.include_prelude {
                compile_prelude().symbols.clone()
            } else {
                SymbolTable::base()
            },
            config,
            session,
        }
    }

    pub fn with_str(string: &str) -> Self {
        let mut driver = Driver::default();
        driver.update_file(&PathBuf::from("-"), string.into());
        driver
    }

    pub fn with_files(files: Vec<PathBuf>) -> Self {
        let mut driver = Driver::default();

        for file in files {
            let contents = std::fs::read_to_string(&file).unwrap_or_default();
            driver.update_file(&file, contents);
        }

        driver
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

    pub fn parse(&self) -> Vec<CompilationUnit<Parsed>> {
        let mut result = vec![];
        for unit in self.units.clone() {
            result.push(unit.parse());
        }
        result
    }

    pub fn lower(&mut self) -> Vec<CompilationUnit<Lowered>> {
        let mut result = vec![];

        for unit in self.units.clone() {
            let parsed = unit.parse();
            let resolved = parsed.resolved(&mut self.symbol_table);
            let typed = resolved.typed(&mut self.symbol_table, &self.config);

            let module = if self.config.include_prelude {
                compile_prelude().module.clone()
            } else {
                IRModule::new()
            };

            result.push(typed.lower(&mut self.symbol_table, &self.config, module));
        }

        result
    }

    pub fn check(&mut self) -> Vec<CompilationUnit<Typed>> {
        let mut result = vec![];
        for unit in self.units.clone() {
            let parsed = unit.parse();
            let resolved = parsed.resolved(&mut self.symbol_table);
            let typed = resolved.typed(&mut self.symbol_table, &self.config);
            result.push(typed);
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
        let mut result = vec![];
        let mut round = 0;

        while result.is_empty() && round < 3 {
            let diagnostics = match round {
                0 => {
                    let parsed = self.parse();
                    round += 1;
                    self.diagnostics_from(path, parsed).unwrap_or_default()
                }
                1 => {
                    let checked = self.check();
                    round += 1;
                    self.diagnostics_from(path, checked).unwrap_or_default()
                }
                _ => {
                    let lowered = self.lower();
                    round += 1;
                    self.diagnostics_from(path, lowered).unwrap_or_default()
                }
            };

            result.extend(diagnostics);
        }

        result
    }

    fn diagnostics_from<S: StageTrait>(
        &self,
        path: &PathBuf,
        units: Vec<CompilationUnit<S>>,
    ) -> Option<Vec<Diagnostic>> {
        let mut result = vec![];
        for unit in units {
            log::info!("checking for diagnostics in {path:?}");
            if unit.has_file(path)
                && let Some(source_file) = unit.source_file(path)
            {
                for diag in self
                    .session
                    .lock()
                    .ok()?
                    .diagnostics()
                    .get(path)
                    .unwrap_or(&HashSet::default())
                {
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

        Some(result)
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
        for unit in self.units.clone() {
            let typed = unit
                .parse()
                .resolved(&mut self.symbol_table)
                .typed(&mut self.symbol_table, &self.config);
            for file in typed.stage.files {
                if *path == file.path {
                    return Some(file);
                }
            }
        }

        None
    }

    pub fn resolved_source_file(
        &mut self,
        path: &Path,
    ) -> Option<SourceFile<source_file::NameResolved>> {
        for unit in self.units.clone() {
            let typed = unit.parse().resolved(&mut self.symbol_table);
            if let Some(file) = typed.source_file(&PathBuf::from(path)) {
                return Some(file.clone());
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
        let driver = Driver::with_files(vec!["../../dev/fixtures/parse_err/fizz.tlk".into()]);
        driver.parse();
    }
}
