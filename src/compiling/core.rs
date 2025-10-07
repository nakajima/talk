use std::path::PathBuf;

use crate::compiling::{
    driver::{Driver, DriverConfig, Source},
    module::{Module, ModuleId},
};

pub fn compile() -> Module {
    let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let config = DriverConfig {
        module_id: ModuleId::Core,
        ..Default::default()
    };
    let driver = Driver::new_bare(
        vec![
            Source::from(current_dir.join("core/Optional.tlk")),
            Source::from(current_dir.join("core/Operators.tlk")),
            Source::from(current_dir.join("core/Equals.tlk")),
        ],
        config,
    );
    let name_resolved = driver.parse().unwrap().resolve_names().unwrap();
    let exports = name_resolved.exports();
    let typed = name_resolved.typecheck().unwrap();
    let types = typed.phase.type_session.finalize().unwrap();

    Module {
        name: "Core".into(),
        types,
        exports,
    }
}
