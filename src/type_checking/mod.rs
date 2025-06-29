#[cfg(test)]
use crate::{
    SourceFile, SymbolTable, Typed, diagnostic::Diagnostic, environment::Environment, expr::Expr,
    parser::ExprID, ty::Ty, type_checker::TypeError, typed_expr::TypedExpr,
};

pub mod conformance_checker;
pub mod constraint_solver;
pub mod environment;
pub mod name_resolver;
pub mod predecls;
pub mod scope_tree;
pub mod synthesis;
pub mod ty;
pub mod type_checker;
#[cfg(test)]
pub mod type_checker_tests;
pub mod typed_expr;

#[cfg(test)]
pub struct CheckResult {
    pub source_file: SourceFile<Typed>,
    pub env: Environment,
    pub symbols: SymbolTable,
}

#[cfg(test)]
impl CheckResult {
    pub fn type_for(&self, id: &ExprID) -> Option<Ty> {
        self.source_file.type_for(*id, &self.env)
    }

    pub fn expr(&self, id: &ExprID) -> Option<&Expr> {
        self.source_file.get(id)
    }

    pub fn typed_expr(&self, id: &ExprID) -> Option<TypedExpr> {
        self.source_file.typed_expr(id, &self.env)
    }

    pub fn diagnostics(&self) -> Vec<&Diagnostic> {
        self.source_file.diagnostics()
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

    for diagnostic in source_file.diagnostics() {
        log::error!("{:?}", diagnostic);
    }

    Ok(CheckResult {
        source_file,
        env: typed_compilation_unit.env,
        symbols: driver.symbol_table,
    })
}

#[cfg(test)]
pub fn check_without_prelude(input: &str) -> Result<CheckResult, TypeError> {
    use crate::compiling::driver::{Driver, DriverConfig};
    use std::path::PathBuf;

    let path = &PathBuf::from("-");
    let mut driver = Driver::new(DriverConfig {
        executable: false,
        include_prelude: false,
    });
    driver.update_file(path, input.into());
    let typed_compilation_unit = driver.check().into_iter().next().unwrap().clone();
    let source_file = typed_compilation_unit.source_file(path).unwrap().clone();
    Ok(CheckResult {
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
