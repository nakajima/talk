#[cfg(test)]
use crate::{
    ExprMetaStorage, SourceFile, SymbolTable, Typed,
    compiling::{compilation_session::SharedCompilationSession, compiled_module::CompiledModule},
    diagnostic::Diagnostic,
    environment::Environment,
    parsing::expr_id::ExprID,
    ty::Ty,
    type_checker::TypeError,
    type_var_context::TypeVarContext,
    typed_expr::TypedExpr,
};

pub mod conformance;
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
pub mod type_def;
pub mod type_var_context;
pub mod type_var_id;
pub mod typed_expr;

#[cfg(test)]
pub mod dumb_dot;
#[cfg(test)]
pub mod type_checker_tests;

#[cfg(test)]
#[derive(Debug)]
pub struct CheckResult {
    pub session: SharedCompilationSession,
    pub source_file: SourceFile<Typed>,
    pub env: Environment,
    pub symbols: SymbolTable,
    pub type_var_context: TypeVarContext,
    pub meta: ExprMetaStorage,
}

#[cfg(test)]
impl CheckResult {
    pub fn diagnostics(&self) -> Vec<Diagnostic> {
        use std::path::PathBuf;

        let Ok(session) = self.session.lock() else {
            tracing::error!("Could not unlock session");
            return vec![];
        };

        let diagnostics = session.diagnostics_for(&PathBuf::from("-"));

        diagnostics
            .into_iter()
            .filter_map(|d| {
                if d.is_unhandled() {
                    Some(d.to_owned())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn first_root(&self) -> TypedExpr {
        self.source_file.phase_data.roots.first().unwrap().clone()
    }

    pub fn roots(&self) -> &[TypedExpr] {
        &self.source_file.phase_data.roots
    }

    pub fn root_ids(&self) -> Vec<ExprID> {
        self.source_file.roots().iter().map(|r| r.id).collect()
    }

    pub fn typed_expr(&self, expr_id: ExprID) -> Option<&TypedExpr> {
        self.source_file.typed_expr(expr_id)
    }

    pub fn nth(&self, idx: usize) -> Option<Ty> {
        self.source_file
            .phase_data
            .roots
            .get(idx)
            .map(|t| t.ty.clone())
    }

    pub fn type_for(&self, expr_id: ExprID) -> Option<Ty> {
        self.source_file
            .typed_expr(expr_id)
            .map(|typed_expr| typed_expr.ty.clone())
    }
}

#[cfg(test)]
pub fn check(input: &str) -> Result<CheckResult, TypeError> {
    use crate::{ExprMetaStorage, compiling::driver::Driver};
    use std::path::PathBuf;

    let path = &PathBuf::from("-");
    let mut driver = Driver::new("TypeTests", Default::default());
    driver.update_file(path, input);
    let units = driver.check();
    let typed_compilation_unit = units.clone().into_iter().next().unwrap();
    let source_file = typed_compilation_unit.source_file(path).unwrap().clone();

    let mut merged = ExprMetaStorage::default();

    for unit in units {
        for file in unit.stage.files {
            merged.merge(&file.meta.borrow());
        }
    }

    for diagnostic in driver.session.lock().unwrap().diagnostics_for(path) {
        tracing::error!("{diagnostic:?}");
    }

    Ok(CheckResult {
        session: driver.session,
        source_file,
        type_var_context: typed_compilation_unit.env.context.clone(),
        env: typed_compilation_unit.env,
        symbols: driver.symbol_table,
        meta: merged,
    })
}

#[cfg(test)]
pub fn check_with_imports(
    imports: &[CompiledModule],
    input: &str,
) -> Result<CheckResult, TypeError> {
    use crate::{ExprMetaStorage, compiling::driver::Driver};
    use std::path::PathBuf;

    let path = &PathBuf::from("-");
    let mut driver = Driver::new("-", Default::default());
    driver.update_file(path, input);
    driver.import_modules(imports.to_vec());
    let units = driver.check();
    let typed_compilation_unit = units.clone().into_iter().next().unwrap();
    let source_file = typed_compilation_unit.source_file(path).unwrap().clone();

    let mut merged = ExprMetaStorage::default();

    for unit in units {
        for file in unit.stage.files {
            merged.merge(&file.meta.borrow());
        }
    }

    let diagnostics = driver.session.lock().unwrap()._diagnostics().clone();

    assert!(diagnostics.is_empty(), "{diagnostics:#?}");

    Ok(CheckResult {
        session: driver.session,
        source_file,
        type_var_context: typed_compilation_unit.env.context.clone(),
        env: typed_compilation_unit.env,
        symbols: driver.symbol_table,
        meta: merged,
    })
}

#[cfg(test)]
pub fn check_without_prelude(input: &str) -> Result<CheckResult, TypeError> {
    use crate::compiling::driver::{Driver, DriverConfig};
    use std::path::PathBuf;

    let path = &PathBuf::from("-");
    let mut driver = Driver::new(
        "TypeTests",
        DriverConfig {
            executable: false,
            include_prelude: false,
            include_comments: false,
        },
    );
    driver.update_file(path, input);
    let typed_compilation_unit = driver.check().into_iter().next().unwrap();

    let mut merged = ExprMetaStorage::default();

    let source_file = typed_compilation_unit.source_file(path).unwrap().clone();

    for file in &typed_compilation_unit.stage.files {
        merged.merge(&file.meta.borrow());
    }

    for diagnostic in driver.session.lock().unwrap().diagnostics_for(path) {
        tracing::error!("{diagnostic:?}");
    }

    Ok(CheckResult {
        session: driver.session,
        source_file,
        type_var_context: typed_compilation_unit.env.context.clone(),
        env: typed_compilation_unit.env,
        symbols: driver.symbol_table,
        meta: merged,
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
