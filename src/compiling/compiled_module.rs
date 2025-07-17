pub struct CompiledModule {
    pub name: String,
}

#[cfg(test)]
mod tests {
    use crate::lowering::lowerer_tests::lowering_tests::lower;

    use super::*;

    fn compile(name: &str, code: &str) -> CompiledModule {
        CompiledModule {
            name: name.to_string(),
        }
    }
}
