use std::{
    collections::{BTreeMap, HashMap},
    path::{Path, PathBuf},
};

use crate::{
    NameResolved, SourceFile, SymbolID, SymbolTable,
    compiling::{compilation_session::SharedCompilationSession, driver::DriverConfig},
    constraint_solver::ConstraintSolver,
    diagnostic::Diagnostic,
    environment::Environment,
    lexer::{Lexer, LexerError},
    lowering::{ir_error::IRError, ir_module::IRModule, lowerer::Lowerer},
    name_resolver::NameResolver,
    parser::{Parser, ParserError},
    source_file,
    type_checker::{TypeChecker, TypeError},
    typed_expr::TypedExpr,
};

pub trait StageTrait: std::fmt::Debug {
    type SourceFilePhase: source_file::Phase;
    fn source_file(&self, path: &Path) -> Option<&SourceFile<Self::SourceFilePhase>>;
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
            #[allow(clippy::unwrap_used)]
            return Ok(self.src_cache.get(path).unwrap());
        }

        let src = std::fs::read_to_string(path).map_err(CompilationError::IOError)?;
        self.src_cache.insert(path.clone(), src);

        #[allow(clippy::expect_used)]
        Ok(self.src_cache.get(path).expect("src cache bad").as_str())
    }

    pub fn source_file(&self, path: &Path) -> Option<&SourceFile<Stage::SourceFilePhase>> {
        self.stage.source_file(path)
    }
}

#[derive(Debug, Clone)]
pub struct Raw {}
impl StageTrait for Raw {
    type SourceFilePhase = source_file::Parsed;
    fn source_file(&self, _path: &Path) -> Option<&SourceFile> {
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
    pub session: SharedCompilationSession,
}

impl<S: StageTrait> CompilationUnit<S> {
    pub fn has_file(&self, path: &PathBuf) -> bool {
        self.input.contains(path)
    }
}

impl CompilationUnit<Raw> {
    pub fn new(session: SharedCompilationSession, input: Vec<PathBuf>, env: Environment) -> Self {
        Self {
            src_cache: Default::default(),
            input,
            stage: Raw {},
            env,
            session,
        }
    }

    pub fn parse(mut self, include_comments: bool) -> CompilationUnit<Parsed> {
        let mut files = vec![];

        for path in self.input.clone() {
            self.session
                .lock()
                .map(|mut t| t.clear_diagnostics())
                .unwrap_or_else(|e| tracing::error!("could not clear diagnostics: {e:?}"));

            let source = match self.read(&path) {
                Ok(source) => source.to_string(),
                Err(e) => {
                    tracing::error!("read error: {e:?}");
                    continue;
                }
            };

            let lexer = if include_comments {
                Lexer::preserving_comments(&source)
            } else {
                Lexer::new(&source)
            };
            let mut parser = Parser::new(self.session.clone(), lexer, path, &mut self.env);
            parser.parse();
            files.push(parser.parse_tree);
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Parsed { files },
            env: self.env,
            session: self.session,
        }
    }

    pub fn lower(
        self,
        symbol_table: &mut SymbolTable,
        driver_config: &DriverConfig,
        module: IRModule,
    ) -> CompilationUnit<Lowered> {
        let parsed = self.parse(driver_config.include_comments);
        let resolved = parsed.resolved(symbol_table, driver_config);
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
    fn source_file(&self, path: &Path) -> Option<&SourceFile<source_file::Parsed>> {
        self.files.iter().find(|f| f.path == *path)
    }
}

impl CompilationUnit<Parsed> {
    pub fn resolved(
        self,
        symbol_table: &mut SymbolTable,
        config: &DriverConfig,
    ) -> CompilationUnit<Resolved> {
        let mut files = vec![];
        let mut global_scope = if config.include_prelude {
            crate::prelude::compile_prelude().global_scope.clone()
        } else {
            crate::builtins::default_name_scope() // Builtins like Int, Float
        };
        for file in self.stage.files {
            let mut resolver = NameResolver::new(
                global_scope.clone(),
                self.session.clone(),
                file.path.clone(),
            );
            let resolved = resolver.resolve(file, symbol_table);

            for (name, symbol) in resolver.scopes[0].clone().into_iter() {
                global_scope.insert(name, symbol);
            }

            files.push(resolved);
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Resolved {
                global_scope,
                files,
            },
            env: self.env,
            session: self.session,
        }
    }
}

#[derive(Debug)]
pub struct Resolved {
    files: Vec<SourceFile<NameResolved>>,
    pub global_scope: BTreeMap<String, SymbolID>,
}
impl StageTrait for Resolved {
    type SourceFilePhase = source_file::NameResolved;
    fn source_file(&self, path: &Path) -> Option<&SourceFile<source_file::NameResolved>> {
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

        for mut file in self.stage.files {
            let path = file.path.clone();
            let meta = file.meta.borrow().clone();

            let mut typed = if driver_config.include_prelude {
                TypeChecker::new(self.session.clone(), symbol_table, file.path.clone(), &meta)
                    .infer(&mut file, &mut self.env)
            } else {
                TypeChecker::new(self.session.clone(), symbol_table, file.path.clone(), &meta)
                    .infer_without_prelude(&mut self.env, &mut file)
            };
            let mut solver = ConstraintSolver::new(&mut self.env, symbol_table);
            let mut solution = solver.solve();

            TypedExpr::apply_mult(
                typed.roots_mut(),
                &mut solution.substitutions,
                &mut self.env,
            );

            for (expr_id, err) in solution.errors {
                if let Ok(session) = &mut self.session.lock() {
                    session.add_diagnostic(Diagnostic::typing(path.clone(), expr_id, err));
                }
            }

            files.push(typed);
        }

        CompilationUnit {
            src_cache: self.src_cache,
            input: self.input,
            stage: Typed { files },
            env: self.env,
            session: self.session,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Typed {
    pub files: Vec<SourceFile<source_file::Typed>>,
}
impl StageTrait for Typed {
    type SourceFilePhase = source_file::Typed;
    fn source_file(&self, path: &Path) -> Option<&SourceFile<source_file::Typed>> {
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
            let lowered = Lowerer::new(file, symbol_table, &mut self.env, self.session.clone())
                .lower(&mut module, driver_config);
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
            session: self.session,
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
    fn source_file(&self, path: &Path) -> Option<&SourceFile<source_file::Lowered>> {
        self.files.iter().find(|f| f.path == *path)
    }
}

impl CompilationUnit<Lowered> {
    pub fn module(&self) -> IRModule {
        self.stage.module.clone()
    }
}
