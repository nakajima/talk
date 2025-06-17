use std::{collections::HashMap, path::PathBuf};

use crate::{
    NameResolved, SourceFile, SymbolTable,
    constraint_solver::ConstraintSolver,
    environment::Environment,
    file_store::FileStore,
    lexer::LexerError,
    lowering::{
        ir_module::IRModule,
        lowerer::{IRError, Lowerer},
    },
    name_resolver::NameResolver,
    parser::{ParserError, parse},
    prelude::compile_prelude,
    source_file,
    type_checker::{TypeChecker, TypeError},
};

pub trait StageTrait {}

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
}

pub struct Raw {}
impl StageTrait for Raw {}

#[allow(unused)]
pub struct CompilationUnit<Stage = Raw>
where
    Stage: StageTrait,
{
    pub src_cache: HashMap<PathBuf, String>,
    pub input: FileStore,
    pub stage: Stage,
}

impl<S: StageTrait> CompilationUnit<S> {
    pub fn has_file(&self, path: &PathBuf) -> bool {
        self.input.id(path).is_some()
    }
}

impl CompilationUnit<Raw> {
    pub fn new(input: FileStore) -> Self {
        Self {
            src_cache: Default::default(),
            input,
            stage: Raw {},
        }
    }

    pub fn parse(&mut self) -> CompilationUnit<Parsed> {
        let mut files = vec![];

        for file in self.input.files.clone() {
            let Some(file_id) = self.input.id(&file) else {
                continue;
            };
            match self.read(&file) {
                Ok(source) => {
                    let parsed = parse(source, file_id);
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
    ) -> Result<CompilationUnit<Lowered>, CompilationError> {
        let parsed = self.parse();
        let resolved = parsed.resolved(symbol_table);
        let typed = resolved.typed(symbol_table);
        let lowered = typed.lower(symbol_table)?;
        Ok(lowered)
    }
}

#[allow(unused)]
pub struct Parsed {
    pub files: Vec<SourceFile<source_file::Parsed>>,
}

impl StageTrait for Parsed {}

impl CompilationUnit<Parsed> {
    pub fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::Parsed>> {
        self.stage
            .files
            .iter()
            .find(|f| Some(f.file_id) == self.input.id(path))
    }

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

pub struct Resolved {
    files: Vec<SourceFile<NameResolved>>,
}
impl StageTrait for Resolved {}

impl CompilationUnit<Resolved> {
    pub fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::NameResolved>> {
        self.stage
            .files
            .iter()
            .find(|f| Some(f.file_id) == self.input.id(path))
    }

    pub fn typed(self, symbol_table: &mut SymbolTable) -> CompilationUnit<Typed> {
        let prelude = compile_prelude();
        let mut env = Environment::new();
        env.import_prelude(prelude);

        let mut files: Vec<SourceFile<source_file::Typed>> = vec![];

        for file in self.stage.files {
            let mut typed = TypeChecker.infer(file, symbol_table, &mut env);
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

pub struct Typed {
    pub environment: Environment,
    pub files: Vec<SourceFile<source_file::Typed>>,
}
impl StageTrait for Typed {}

impl CompilationUnit<Typed> {
    pub fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::Typed>> {
        self.stage
            .files
            .iter()
            .find(|f| Some(f.file_id) == self.input.id(path))
    }

    pub fn lower(
        self,
        symbol_table: &mut SymbolTable,
    ) -> Result<CompilationUnit<Lowered>, CompilationError> {
        let mut module = IRModule::new();
        let mut files = vec![];
        for file in self.stage.files {
            let lowered = Lowerer::new(file, symbol_table)
                .lower(&mut module)
                .map_err(CompilationError::IRError)?;
            files.push(lowered);
        }

        Ok(CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Lowered { module, files },
        })
    }
}

pub struct Lowered {
    pub module: IRModule,
    pub files: Vec<SourceFile<source_file::Lowered>>,
}

impl StageTrait for Lowered {}

impl CompilationUnit<Lowered> {
    pub fn module(self) -> IRModule {
        self.stage.module
    }

    pub fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::Lowered>> {
        self.stage
            .files
            .iter()
            .find(|f| Some(f.file_id) == self.input.id(path))
    }
}
