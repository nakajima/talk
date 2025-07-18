use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

use crate::{
    SourceFile, SymbolID, SymbolTable,
    compiling::{
        compilation_session::{CompilationSession, SharedCompilationSession},
        compilation_unit::{CompilationError, CompilationUnit, Lowered, Parsed, Typed},
        imported_module::ImportedModule,
    },
    diagnostic::{Diagnostic, Position},
    environment::Environment,
    lowering::ir_module::IRModule,
    source_file,
};

#[derive(Debug)]
pub struct DriverConfig {
    pub executable: bool,
    pub include_prelude: bool,
    pub include_comments: bool,
}

pub type ModuleEnvironment = HashMap<String, ImportedModule>;

impl DriverConfig {
    pub fn new_environment(&self) -> Environment {
        if self.include_prelude {
            crate::prelude::compile_prelude().environment.clone()
        } else {
            Environment::new()
        }
    }
}

impl Default for DriverConfig {
    fn default() -> Self {
        DriverConfig {
            executable: true,
            include_prelude: true,
            include_comments: false,
        }
    }
}

#[derive(Debug)]
pub struct Driver {
    pub units: Vec<CompilationUnit>,
    pub symbol_table: SymbolTable,
    pub config: DriverConfig,
    pub session: SharedCompilationSession,
    module_env: HashMap<String, ImportedModule>,
}

impl Default for Driver {
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl Driver {
    pub fn new(config: DriverConfig) -> Self {
        let session = SharedCompilationSession::new(CompilationSession::new().into());
        let environment = config.new_environment();

        Self {
            units: vec![CompilationUnit::new(session.clone(), vec![], environment)],
            symbol_table: if config.include_prelude {
                crate::prelude::compile_prelude().symbols.clone()
            } else {
                SymbolTable::base()
            },
            config,
            session,
            module_env: Default::default(),
        }
    }

    pub fn with_str(string: &str) -> Self {
        let mut driver = Driver::default();
        driver.update_file(&PathBuf::from("-"), string.into());
        driver
    }

    pub fn with_files(files: Vec<PathBuf>) -> Self {
        let mut driver = Driver::default();

        #[allow(clippy::expect_used)]
        #[allow(clippy::expect_fun_call)]
        for file in files {
            let contents =
                std::fs::read_to_string(&file).expect(format!("File not found: {file:?}").as_str());
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
        tracing::info!("adding {path:?} to default unit");
        self.units[0].input.push(path.to_path_buf());
        self.units[0]
            .src_cache
            .insert(path.clone(), contents.clone());
    }

    pub fn parse(&self) -> Vec<CompilationUnit<Parsed>> {
        let mut result = vec![];
        for unit in self.units.clone() {
            result.push(unit.parse(self.config.include_comments));
        }
        result
    }

    pub fn lower(&mut self) -> Vec<CompilationUnit<Lowered>> {
        let mut result = vec![];

        for unit in self.units.clone() {
            let parsed = unit.parse(self.config.include_comments);
            let resolved = parsed.resolved(&mut self.symbol_table, &self.config, &self.module_env);
            let typed = resolved.typed(&mut self.symbol_table, &self.config, &self.module_env);

            let module = if self.config.include_prelude {
                crate::prelude::compile_prelude().module.clone()
            } else {
                IRModule::new()
            };

            result.push(typed.lower(
                &mut self.symbol_table,
                &self.config,
                module,
                &self.module_env,
            ));
        }

        result
    }

    pub fn check(&mut self) -> Vec<CompilationUnit<Typed>> {
        let mut result = vec![];

        for unit in self.units.clone() {
            let parsed = unit.parse(self.config.include_comments);
            let resolved = parsed.resolved(&mut self.symbol_table, &self.config, &self.module_env);
            let typed = resolved.typed(&mut self.symbol_table, &self.config, &self.module_env);
            result.push(typed);
        }

        result
    }

    pub fn symbol_from_position(&self, position: Position, path: &PathBuf) -> Option<&SymbolID> {
        let mut result = None;

        // We want to find the smallest possible span
        let mut min = u32::MAX;

        for (span, sym) in &self.symbol_table.symbol_map {
            if span.contains(&Position {
                line: position.line,
                col: position.col,
            }) && span.path == *path
                && span.length() < min
            {
                min = span.length();
                result = Some(sym);
            }
        }

        result
    }

    pub fn refresh_diagnostics_for(
        &mut self,
        path: &PathBuf,
    ) -> Result<HashSet<Diagnostic>, CompilationError> {
        if let Ok(session) = &mut self.session.lock() {
            session.clear_diagnostics()
        } else {
            tracing::error!("Unable to clear diagnostics")
        }

        self.lower();

        #[allow(clippy::unwrap_used)]
        match self.session.lock() {
            Ok(session) => Ok(session.diagnostics_for(path).into_iter().cloned().collect()),
            Err(err) => {
                tracing::error!("Could not lock session: {err:?}");
                Err(CompilationError::UnknownError("Could not lock session"))
            }
        }
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
                .parse(self.config.include_comments)
                .resolved(&mut self.symbol_table, &self.config, &self.module_env)
                .typed(&mut self.symbol_table, &self.config, &self.module_env);
            for file in typed.stage.files {
                if *path == file.path {
                    return Some(file);
                }
            }
        }

        None
    }

    pub fn import_modules(&mut self, modules: Vec<ImportedModule>) {
        for module in modules.into_iter() {
            self.module_env
                .insert(module.module_name.to_string(), module);
        }
    }

    pub fn resolved_source_file(
        &mut self,
        path: &Path,
    ) -> Option<SourceFile<source_file::NameResolved>> {
        for unit in self.units.clone() {
            let typed = unit.parse(self.config.include_comments).resolved(
                &mut self.symbol_table,
                &self.config,
                &self.module_env,
            );
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
