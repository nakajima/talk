use std::{collections::HashMap, path::PathBuf};

use crate::{
    NameResolved, SourceFile, SymbolTable,
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

#[derive(Debug)]
pub enum CompilationError {
    LexerError(LexerError),
    ParserError(ParserError),
    TypeError(TypeError),
    IRError(IRError),
    IOError(std::io::Error),
    UnknownError(&'static str),
}

impl<Stage> CompilationUnit<Stage> {
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

#[allow(unused)]
pub struct CompilationUnit<Stage = Raw> {
    src_cache: HashMap<PathBuf, String>,
    pub input: FileStore,
    pub stage: Stage,
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
        let symbol_table = SymbolTable::default();
        for file in self.input.files.clone() {
            let file_id = self.input.id(&file);
            match self.read(&file) {
                Ok(source) => {
                    let parsed = parse(source, file_id);
                    files.push(parsed);
                }
                Err(e) => {
                    log::error!("read error: {:?}", e);
                }
            }
        }

        CompilationUnit {
            src_cache: self.src_cache.clone(),
            input: self.input.clone(),
            stage: Parsed {
                symbol_table,
                files,
            },
        }
    }

    pub fn lower(&mut self) -> Result<CompilationUnit<Lowered>, CompilationError> {
        let parsed = self.parse();
        let resolved = parsed.resolved();
        let typed = resolved.typed();
        let lowered = typed.lower()?;
        Ok(lowered)
    }
}

#[allow(unused)]
pub struct Parsed {
    symbol_table: SymbolTable,
    files: Vec<SourceFile<source_file::Parsed>>,
}

impl CompilationUnit<Parsed> {
    pub fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::Parsed>> {
        self.stage
            .files
            .iter()
            .find(|f| f.file_id == self.input.id(path))
    }

    pub fn resolved(self) -> CompilationUnit<Resolved> {
        let mut symbol_table = self.stage.symbol_table;
        let mut files = vec![];
        for file in self.stage.files {
            let (resolved, sym) = NameResolver::new(symbol_table).resolve(file);
            files.push(resolved);
            symbol_table = sym;
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Resolved {
                symbol_table,
                files,
            },
        }
    }
}

pub struct Resolved {
    symbol_table: SymbolTable,
    files: Vec<SourceFile<NameResolved>>,
}

impl CompilationUnit<Resolved> {
    pub fn typed(self) -> CompilationUnit<Typed> {
        let prelude = compile_prelude();
        let mut env = Environment::new();
        env.import_prelude(prelude);

        let mut files: Vec<SourceFile<source_file::Typed>> = vec![];
        let mut symbol_table = self.stage.symbol_table;

        for file in self.stage.files {
            let typed = TypeChecker.infer(file, &mut symbol_table, &mut env);
            files.push(typed);
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Typed {
                symbol_table,
                environment: env,
                files,
            },
        }
    }
}

pub struct Typed {
    symbol_table: SymbolTable,
    pub environment: Environment,
    files: Vec<SourceFile<source_file::Typed>>,
}

impl CompilationUnit<Typed> {
    pub fn source_file(&self, path: &PathBuf) -> Option<&SourceFile<source_file::Typed>> {
        self.stage
            .files
            .iter()
            .find(|f| f.file_id == self.input.id(path))
    }

    pub fn lower(self) -> Result<CompilationUnit<Lowered>, CompilationError> {
        let mut symbol_table = self.stage.symbol_table;
        let mut module = IRModule::new();
        let mut files = vec![];
        for file in self.stage.files {
            let lowered = Lowerer::new(file, &mut symbol_table)
                .lower(&mut module)
                .map_err(CompilationError::IRError)?;
            files.push(lowered);
        }

        Ok(CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Lowered {
                module,
                symbol_table,
                files,
            },
        })
    }
}

pub struct Lowered {
    pub module: IRModule,
    pub symbol_table: SymbolTable,
    pub files: Vec<SourceFile<source_file::Lowered>>,
}

impl CompilationUnit<Lowered> {}
