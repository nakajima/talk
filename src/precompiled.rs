use serde::{Serialize, Deserialize};
use std::{collections::BTreeMap, path::Path};

use crate::{
    SymbolID, SymbolTable,
    environment::Environment,
    lowering::ir_module::IRModule,
    prelude::Prelude,
    type_checking::type_defs::TypeDef,
    type_checking::type_checker::Scheme,
};

#[derive(Serialize, Deserialize)]
pub struct EnvironmentData {
    pub scopes: Vec<BTreeMap<SymbolID, Scheme>>,
    pub types: BTreeMap<SymbolID, TypeDef>,
    pub next_id: i32,
}

impl From<&Environment> for EnvironmentData {
    fn from(env: &Environment) -> Self {
        Self {
            scopes: env.scopes.clone(),
            types: env.types.clone(),
            next_id: env.next_id,
        }
    }
}

impl From<EnvironmentData> for Environment {
    fn from(data: EnvironmentData) -> Self {
        let mut env = Environment::default();
        env.scopes = data.scopes;
        env.types = data.types;
        env.next_id = data.next_id;
        env
    }
}

#[derive(Serialize, Deserialize)]
pub struct CachedModule {
    pub symbols: SymbolTable,
    pub environment: EnvironmentData,
    pub module: IRModule,
    pub global_scope: BTreeMap<String, SymbolID>,
}

impl From<&Prelude> for CachedModule {
    fn from(prelude: &Prelude) -> Self {
        Self {
            symbols: prelude.symbols.clone(),
            environment: (&prelude.environment).into(),
            module: prelude.module.clone(),
            global_scope: prelude.global_scope.clone(),
        }
    }
}

impl From<CachedModule> for Prelude {
    fn from(c: CachedModule) -> Self {
        Self {
            symbols: c.symbols,
            environment: c.environment.into(),
            module: c.module,
            global_scope: c.global_scope,
        }
    }
}

pub fn save_module(module: &CachedModule, path: &Path) -> std::io::Result<()> {
    let bytes = bincode::serialize(module).unwrap();
    std::fs::write(path, bytes)
}

pub fn load_module(path: &Path) -> std::io::Result<CachedModule> {
    let bytes = std::fs::read(path)?;
    Ok(bincode::deserialize(&bytes).unwrap())
}

