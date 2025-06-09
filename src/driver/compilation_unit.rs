use std::{collections::HashMap, path::PathBuf};

use crate::{
    SourceFile, SymbolTable,
    environment::Environment,
    file_store::FileStore,
    lexer::LexerError,
    lowering::lowerer::IRError,
    parser::{ParserError, parse},
    source_file,
    type_checker::TypeError,
};

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

        let src = std::fs::read_to_string(&path).map_err(CompilationError::IOError)?;
        self.src_cache.insert(path.clone(), src);
        Ok(self.src_cache.get(path).expect("src cache bad").as_str())
    }
}

pub struct Raw {}

#[allow(unused)]
pub struct CompilationUnit<Stage = Raw> {
    src_cache: HashMap<PathBuf, String>,
    input: FileStore,
    stage: Stage,
}

impl CompilationUnit<Raw> {
    pub fn parse(mut self) -> Result<CompilationUnit<Parsed>, CompilationError> {
        let mut files = vec![];
        let symbol_table = SymbolTable::default();
        for file in self.input.files.clone() {
            let file_id = self.input.id(&file).clone();
            let source = self.read(&file)?;
            let parsed = parse(source, file_id).map_err(CompilationError::ParserError)?;
            files.push(parsed);
        }

        Ok(CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Parsed {
                symbol_table,
                files,
            },
        })
    }
}

#[allow(unused)]
pub struct Parsed {
    symbol_table: SymbolTable,
    files: Vec<SourceFile<source_file::Parsed>>,
}

impl CompilationUnit<Parsed> {
    pub fn resolve_names(self) -> Result<CompilationUnit<Resolved>, CompilationError> {
        todo!()
    }
}

pub struct Resolved {
    _symbol_table: SymbolTable,
}

impl CompilationUnit<Resolved> {
    pub fn type_check(self) -> Result<CompilationUnit<Typed>, CompilationError> {
        todo!()
    }
}

pub struct Typed {
    _symbol_table: SymbolTable,
    _environment: Environment,
}

impl CompilationUnit<Typed> {
    pub fn lower(self) -> Result<CompilationUnit<Lowered>, CompilationError> {
        todo!()
    }
}

pub struct Lowered {}

impl CompilationUnit<Lowered> {}
