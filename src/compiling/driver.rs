use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

use crate::{
    SourceFile, SymbolID, SymbolInfo, SymbolKind, SymbolTable,
    compiling::{
        compilation_session::{CompilationSession, SharedCompilationSession},
        compilation_unit::{CompilationError, CompilationUnit, Lowered, Parsed, Typed},
        compiled_module::{CompiledModule, ImportedSymbol, ImportedSymbolKind},
    },
    diagnostic::{Diagnostic, Position},
    environment::Environment,
    lowering::ir_module::IRModule,
    name::ResolvedName,
    prelude::compile_prelude,
    source_file,
    ty::Ty,
    typed_expr::TypedExpr,
};

#[derive(Debug)]
pub struct DriverConfig {
    pub executable: bool,
    pub include_prelude: bool,
    pub include_comments: bool,
}

pub type ModuleEnvironment = HashMap<String, CompiledModule>;

impl DriverConfig {
    pub fn new_environment(&self) -> Environment {
        Environment::new()
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
    pub module_env: HashMap<String, CompiledModule>,
}

impl Default for Driver {
    fn default() -> Self {
        Self::new("default", Default::default())
    }
}

impl Driver {
    pub fn new(name: impl Into<String>, config: DriverConfig) -> Self {
        let session = SharedCompilationSession::new(CompilationSession::new().into());
        let environment = config.new_environment();

        let mut driver = Self {
            units: vec![CompilationUnit::new(
                name.into(),
                session.clone(),
                vec![],
                environment,
            )],
            symbol_table: SymbolTable::base(),
            config,
            session,
            module_env: Default::default(),
        };

        if driver.config.include_prelude {
            driver.import_modules(vec![compile_prelude().clone()]);
        }

        driver
    }

    pub fn with_str(string: &str) -> Self {
        let mut driver = Driver::default();
        driver.update_file(&PathBuf::from("-"), string);
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

    pub fn update_file(&mut self, path: &PathBuf, contents: impl Into<String>) {
        let contents: String = contents.into();
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

            let module = IRModule::new();

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

    pub fn import_modules(&mut self, modules: Vec<CompiledModule>) {
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

    #[allow(clippy::expect_used)]
    #[allow(clippy::panic)]
    pub fn compile_modules(&mut self) -> Result<Vec<CompiledModule>, CompilationError> {
        let mut modules = vec![];

        for unit in self.units.iter() {
            let resolved = unit
                .clone()
                .parse(false /* don't include comments */)
                .resolved(&mut self.symbol_table, &self.config, &self.module_env);

            let mut symbols = HashMap::<String, ImportedSymbol>::new();
            for (name, symbol_id) in &resolved.stage.global_scope {
                let Some(info) = self.symbol_table.get(symbol_id) else {
                    continue;
                };

                if info.kind.is_builtin() {
                    continue;
                }

                let imported_kind = match info {
                    SymbolInfo {
                        kind: SymbolKind::FuncDef,
                        ..
                    } => ImportedSymbolKind::Function { index: 0 },
                    _ => continue,
                };
                symbols.insert(
                    name.clone(),
                    ImportedSymbol {
                        module: unit.name.clone(),
                        name: name.clone(),
                        symbol: *symbol_id,
                        kind: imported_kind,
                    },
                );
            }

            let typed = resolved.typed(&mut self.symbol_table, &self.config, &self.module_env);

            let mut typed_symbols = HashMap::<SymbolID, Ty>::new();
            for (_, imported) in symbols.iter() {
                let info = self
                    .symbol_table
                    .get(&imported.symbol)
                    .expect("didn't get symbol for exported ty");

                if info.kind.is_builtin() {
                    continue;
                }

                // TODO: This is gonna be slow.
                for file in &typed.stage.files {
                    let Some(typed_expr) = TypedExpr::find_in(file.roots(), info.expr_id) else {
                        tracing::warn!("did not find type for compiled module export: {info:?}");
                        continue;
                    };

                    typed_symbols.insert(imported.symbol, typed_expr.ty.clone());
                }
            }

            let types = typed.env.types.clone();

            let lowered = typed
                .lower(
                    &mut self.symbol_table,
                    &self.config,
                    IRModule::new(),
                    &self.module_env,
                )
                .module();

            // Go back and fill in indexes
            // TODO: This too, will be slow
            for (i, function) in lowered.functions.iter().enumerate() {
                for symbol in symbols.values_mut() {
                    if ResolvedName(symbol.symbol, symbol.name.clone()).mangled(
                        typed_symbols
                            .get(&symbol.symbol)
                            .unwrap_or_else(|| panic!("how tho: {symbol:?}")),
                    ) == function.name
                        && let ImportedSymbolKind::Function { index } = &mut symbol.kind
                    {
                        *index = i;
                    }
                }
            }

            let module = CompiledModule {
                module_name: unit.name.clone(),
                symbols,
                types,
                typed_symbols,
                ir_module: lowered,
            };

            modules.push(module);
        }

        Ok(modules)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        SymbolID,
        compiling::{
            compiled_module::{ImportedSymbol, ImportedSymbolKind},
            driver::Driver,
        },
        ty::Ty,
    };

    #[test]
    fn compiles_a_module() {
        let mut driver = Driver::with_str(
            "
            func foo(x: Int) { x }
            func bar(x: Float) { x }
            ",
        );

        let modules = driver.compile_modules().unwrap();
        assert_eq!(modules.len(), 1);
        let module = &modules[0];
        assert_eq!("default", module.module_name);
        assert_eq!(
            module.symbols.get("foo").unwrap(),
            &ImportedSymbol {
                module: "default".into(),
                name: "foo".into(),
                symbol: SymbolID::resolved(1),
                kind: ImportedSymbolKind::Function { index: 0 }
            }
        );
        assert_eq!(
            module.symbols.get("bar").unwrap(),
            &ImportedSymbol {
                module: "default".into(),
                name: "bar".into(),
                symbol: SymbolID::resolved(2),
                kind: ImportedSymbolKind::Function { index: 1 }
            }
        );

        assert_eq!(
            module.typed_symbols.get(&SymbolID::resolved(1)).unwrap(),
            &Ty::Func(vec![Ty::Int], Ty::Int.into(), vec![])
        );

        assert_eq!(
            module.typed_symbols.get(&SymbolID::resolved(2)).unwrap(),
            &Ty::Func(vec![Ty::Float], Ty::Float.into(), vec![])
        );
    }
}
