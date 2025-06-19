use std::{collections::HashMap, path::PathBuf};

use crate::{
    NameResolved, SourceFile, SymbolID, SymbolTable,
    compiling::driver::DriverConfig,
    constraint_solver::ConstraintSolver,
    environment::{Environment, TypedExprs},
    lexer::LexerError,
    lowering::{ir_error::IRError, ir_module::IRModule, lowerer::Lowerer},
    name_resolver::NameResolver,
    parser::{ParserError, parse},
    prelude::compile_prelude,
    source_file,
    type_checker::{Scheme, TypeChecker, TypeDefs, TypeError},
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

#[derive(Debug)]
pub struct Raw {}
impl StageTrait for Raw {
    type SourceFilePhase = source_file::Parsed;
    fn source_file(&self, _path: &PathBuf) -> Option<&SourceFile> {
        None
    }
}

#[derive(Debug)]
pub struct CompilationUnit<Stage = Raw>
where
    Stage: StageTrait,
{
    pub src_cache: HashMap<PathBuf, String>,
    pub input: Vec<PathBuf>,
    pub stage: Stage,
}

impl<S: StageTrait> CompilationUnit<S> {
    pub fn has_file(&self, path: &PathBuf) -> bool {
        self.input.contains(path)
    }
}

impl CompilationUnit<Raw> {
    pub fn new(input: Vec<PathBuf>) -> Self {
        Self {
            src_cache: Default::default(),
            input,
            stage: Raw {},
        }
    }

    pub fn parse(&mut self) -> CompilationUnit<Parsed> {
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
            src_cache: self.src_cache.clone(),
            input: self.input.clone(),
            stage: Parsed { files },
        }
    }

    pub fn lower(
        &mut self,
        symbol_table: &mut SymbolTable,
        driver_config: &DriverConfig,
    ) -> CompilationUnit<Lowered> {
        let parsed = self.parse();
        let resolved = parsed.resolved(symbol_table);
        let typed = resolved.typed(symbol_table, &driver_config);
        let lowered = typed.lower(symbol_table, &driver_config);
        lowered
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
        self,
        symbol_table: &mut SymbolTable,
        driver_config: &DriverConfig,
    ) -> CompilationUnit<Typed> {
        let mut env = Environment::new();

        if driver_config.include_prelude {
            let prelude = compile_prelude();
            env.import_prelude(prelude);
        }

        let mut files: Vec<SourceFile<source_file::Typed>> = vec![];

        for file in self.stage.files {
            let mut typed = if driver_config.include_prelude {
                TypeChecker.infer(file, symbol_table, &mut env)
            } else {
                TypeChecker.infer_without_prelude(&mut env, file, symbol_table)
            };
            let mut solver = ConstraintSolver::new(&mut typed, symbol_table);
            solver.solve();
            files.push(typed);
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Typed {
                environment: env,
                files,
            },
        }
    }
}

#[derive(Debug)]
pub struct Typed {
    pub environment: Environment,
    pub files: Vec<SourceFile<source_file::Typed>>,
}
impl StageTrait for Typed {
    type SourceFilePhase = source_file::Typed;
    fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::Typed>> {
        self.files.iter().find(|f| f.path == *path)
    }
}

impl CompilationUnit<Typed> {
    pub fn type_defs(&self) -> TypeDefs {
        let mut type_defs = HashMap::new();
        for file in &self.stage.files {
            type_defs.extend(file.type_defs());
        }
        type_defs
    }

    pub fn schemes(&self) -> HashMap<SymbolID, Scheme> {
        let mut type_defs = HashMap::new();
        for file in &self.stage.files {
            type_defs.extend(file.clone().export().1);
        }
        type_defs
    }

    pub fn typed_exprs(&self) -> TypedExprs {
        let mut type_defs = HashMap::new();
        for file in &self.stage.files {
            type_defs.extend(file.clone().export().2);
        }
        type_defs
    }

    pub fn lower(
        self,
        symbol_table: &mut SymbolTable,
        driver_config: &DriverConfig,
    ) -> CompilationUnit<Lowered> {
        let mut module = IRModule::new();
        let mut files = vec![];
        for file in self.stage.files {
            let lowered = Lowerer::new(file, symbol_table).lower(&mut module, driver_config);
            files.push(lowered);
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Lowered {
                module: module.clone(),
                files,
            },
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
    pub fn module(self) -> IRModule {
        self.stage.module
    }
}
