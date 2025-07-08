#[cfg(test)]
use crate::{
    SourceFile, SymbolTable, Typed, compiling::compilation_session::SharedCompilationSession,
    diagnostic::{Diagnostic, DiagnosticKind}, environment::Environment, expr::Expr, parser::ExprID, ty::Ty,
    type_checker::TypeError, typed_expr::TypedExpr,
};

pub mod conformance_checker;
pub mod constraint;
pub mod constraint_solver;
pub mod environment;
pub mod name_resolver;
pub mod scope_tree;
pub mod substitutions;
pub mod synthesis;
pub mod ty;
pub mod type_checker;
pub mod type_checker_hoisting;
pub mod type_constraint;
pub mod type_defs;
pub mod type_var_context;
pub mod type_var_id;
pub mod typed_expr;

#[cfg(test)]
pub mod type_checker_tests;

#[cfg(test)]
#[derive(Debug)]
pub struct CheckResult {
    pub session: SharedCompilationSession,
    pub source_file: SourceFile<Typed>,
    pub env: Environment,
    pub symbols: SymbolTable,
}

#[cfg(test)]
impl CheckResult {
    pub fn first(&self) -> Option<Ty> {
        self.type_for(&self.root_ids()[0])
    }

    pub fn nth(&self, i: usize) -> Option<Ty> {
        self.type_for(&self.root_ids()[i])
    }

    pub fn type_for(&self, id: &ExprID) -> Option<Ty> {
        self.source_file.type_for(*id, &self.env)
    }

    pub fn expr(&self, id: &ExprID) -> Option<&Expr> {
        self.source_file.get(id)
    }

    pub fn typed_expr(&self, id: &ExprID) -> Option<TypedExpr> {
        self.source_file.typed_expr(id, &self.env)
    }

    pub fn diagnostics(&self) -> Vec<Diagnostic> {
        use std::path::PathBuf;

        let diagnostics = self
            .session
            .lock()
            .unwrap()
            .diagnostics_for(&PathBuf::from("-"))
            .cloned();

        if let Some(diagnostics) = diagnostics {
            let mut collected: Vec<_> = diagnostics
                .iter()
                .filter(|d| d.is_unhandled())
                .cloned()
                .collect();

            collected.sort_by_key(|d| match &d.kind {
                DiagnosticKind::Typing(_, TypeError::Mismatch(_, _)) => 0,
                _ => 1,
            });

            collected
        } else {
            vec![]
        }
    }

    pub fn root_ids(&self) -> Vec<ExprID> {
        self.source_file.root_ids()
    }

    pub fn roots(&self) -> Vec<Ty> {
        self.source_file
            .root_ids()
            .iter()
            .filter_map(|id| self.type_for(id))
            .collect()
    }
}

#[cfg(test)]
pub fn check(input: &str) -> Result<CheckResult, TypeError> {
    use crate::compiling::driver::Driver;
    use std::path::PathBuf;

    let path = &PathBuf::from("-");
    let mut driver = Driver::new(Default::default());
    driver.update_file(path, input.into());
    let typed_compilation_unit = driver.check().into_iter().next().unwrap();
    let source_file = typed_compilation_unit.source_file(path).unwrap().clone();

    for diagnostic in driver
        .session
        .lock()
        .unwrap()
        .diagnostics_for(path)
        .unwrap_or(&Default::default())
    {
        tracing::error!("{diagnostic:?}");
    }

    Ok(CheckResult {
        session: driver.session,
        source_file,
        env: typed_compilation_unit.env,
        symbols: driver.symbol_table,
    })
}

// pub fn check_with_symbols(input: &str) -> Result<(SourceFile<Typed>, SymbolTable), TypeError> {
//     use crate::{
//         constraint_solver::ConstraintSolver, environment::Environment, name_resolver::NameResolver,
//         parser::parse, prelude::compile_prelude, type_checker::TypeChecker,
//     };

//     let mut symbol_table = compile_prelude().symbols.clone();
//     let parsed = parse(input, "-".into());
//     let resolver = NameResolver::new(&mut symbol_table);
//     let resolved = resolver.resolve(parsed, &mut symbol_table);
//     let checker = TypeChecker;
//     let mut env = Environment::new();
//     let mut inferred = checker.infer(resolved, &mut symbol_table, &mut env);
//     let mut constraint_solver = ConstraintSolver::new(&mut inferred, &mut symbol_table);
//     constraint_solver.solve();
//     Ok((inferred, symbol_table.clone()))
// }
