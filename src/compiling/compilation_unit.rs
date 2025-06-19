use std::{collections::HashMap, path::PathBuf};

use crate::{
    NameResolved, SourceFile, SymbolTable,
    compiling::driver::DriverConfig,
    constraint_solver::ConstraintSolver,
    environment::Environment,
    lexer::LexerError,
    lowering::{ir_error::IRError, ir_module::IRModule, lowerer::Lowerer},
    name_resolver::NameResolver,
    parser::{ParserError, parse},
    source_file,
    type_checker::{TypeChecker, TypeError},
};

pub trait StageTrait: std::fmt::Debug {
    type SourceFilePhase: source_file::Phase;
    fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<Self::SourceFilePhase>>;
}

#[derive(Debug)]
pub enum CompilationError {
    LexerError(LexerError),
    ParserError(ParserError),
    TypeError(TypeError),
    IRError(IRError),
    IOError(std::io::Error),
    UnknownError(&'static str),
}

impl<Stage: StageTrait> CompilationUnit<Stage> {
    fn read(&mut self, path: &PathBuf) -> Result<&str, CompilationError> {
        if self.src_cache.contains_key(path) {
            return Ok(self.src_cache.get(path).unwrap());
        }

        let src = std::fs::read_to_string(path).map_err(CompilationError::IOError)?;
        self.src_cache.insert(path.clone(), src);
        Ok(self.src_cache.get(path).expect("src cache bad").as_str())
    }

    pub fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<Stage::SourceFilePhase>> {
        self.stage.source_file(path)
    }
}

#[derive(Debug, Clone)]
pub struct Raw {}
impl StageTrait for Raw {
    type SourceFilePhase = source_file::Parsed;
    fn source_file(&self, _path: &PathBuf) -> Option<&SourceFile> {
        None
    }
}

#[derive(Debug, Clone)]
pub struct CompilationUnit<Stage = Raw>
where
    Stage: StageTrait,
{
    pub src_cache: HashMap<PathBuf, String>,
    pub input: Vec<PathBuf>,
    pub stage: Stage,
    pub env: Environment,
}

impl<S: StageTrait> CompilationUnit<S> {
    pub fn has_file(&self, path: &PathBuf) -> bool {
        self.input.contains(path)
    }
}

impl CompilationUnit<Raw> {
    pub fn new(input: Vec<PathBuf>, env: Environment) -> Self {
        Self {
            src_cache: Default::default(),
            input,
            stage: Raw {},
            env,
        }
    }

    pub fn parse(mut self) -> CompilationUnit<Parsed> {
        let mut files = vec![];

        for path in self.input.clone() {
            match self.read(&path) {
                Ok(source) => {
                    let parsed = parse(source, path);
                    files.push(parsed);
                }
                Err(e) => {
                    log::error!("read error: {e:?}");
                }
            }
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Parsed { files },
            env: self.env,
        }
    }

    pub fn lower(
        self,
        symbol_table: &mut SymbolTable,
        driver_config: &DriverConfig,
        module: IRModule,
    ) -> CompilationUnit<Lowered> {
        let parsed = self.parse();
        let resolved = parsed.resolved(symbol_table);
        let typed = resolved.typed(symbol_table, driver_config);
        typed.lower(symbol_table, driver_config, module)
    }
}

#[derive(Debug)]
pub struct Parsed {
    pub files: Vec<SourceFile<source_file::Parsed>>,
}

impl StageTrait for Parsed {
    type SourceFilePhase = source_file::Parsed;
    fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::Parsed>> {
        self.files.iter().find(|f| f.path == *path)
    }
}

impl CompilationUnit<Parsed> {
    pub fn resolved(self, symbol_table: &mut SymbolTable) -> CompilationUnit<Resolved> {
        let mut files = vec![];
        for file in self.stage.files {
            let resolved = NameResolver::new(symbol_table).resolve(file, symbol_table);
            files.push(resolved);
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Resolved { files },
            env: self.env,
        }
    }
}

#[derive(Debug)]
pub struct Resolved {
    files: Vec<SourceFile<NameResolved>>,
}
impl StageTrait for Resolved {
    type SourceFilePhase = source_file::NameResolved;
    fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::NameResolved>> {
        self.files.iter().find(|f| f.path == *path)
    }
}

impl CompilationUnit<Resolved> {
    pub fn typed(
        mut self,
        symbol_table: &mut SymbolTable,
        driver_config: &DriverConfig,
    ) -> CompilationUnit<Typed> {
        let mut files: Vec<SourceFile<source_file::Typed>> = vec![];

        for file in self.stage.files {
            let mut typed = if driver_config.include_prelude {
                TypeChecker.infer(file, symbol_table, &mut self.env)
            } else {
                TypeChecker.infer_without_prelude(&mut self.env, file, symbol_table)
            };
            let mut solver = ConstraintSolver::new(&mut typed, &mut self.env, symbol_table);
            solver.solve();
            files.push(typed);
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Typed { files },
            env: self.env,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Typed {
    pub files: Vec<SourceFile<source_file::Typed>>,
}
impl StageTrait for Typed {
    type SourceFilePhase = source_file::Typed;
    fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::Typed>> {
        self.files.iter().find(|f| f.path == *path)
    }
}

impl CompilationUnit<Typed> {
    pub fn lower(
        mut self,
        symbol_table: &mut SymbolTable,
        driver_config: &DriverConfig,
        mut module: IRModule,
    ) -> CompilationUnit<Lowered> {
        let mut files = vec![];
        for file in self.stage.files {
            let lowered =
                Lowerer::new(file, symbol_table, &mut self.env).lower(&mut module, driver_config);
            files.push(lowered);
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Lowered {
                module: module.clone(),
                files,
            },
            env: self.env,
        }
    }
}

#[derive(Debug)]
pub struct Lowered {
    pub module: IRModule,
    pub files: Vec<SourceFile<source_file::Lowered>>,
}

impl StageTrait for Lowered {
    type SourceFilePhase = source_file::Lowered;
    fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::Lowered>> {
        self.files.iter().find(|f| f.path == *path)
    }
}

impl CompilationUnit<Lowered> {
    pub fn module(&self) -> IRModule {
        self.stage.module.clone()
    }
}
