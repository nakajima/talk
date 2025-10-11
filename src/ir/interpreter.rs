use crate::ir::{program::Program, value::Value};

pub struct Interpreter {
    #[allow(dead_code)]
    program: Program,
}

impl Interpreter {
    pub fn new(program: Program) -> Self {
        Self { program }
    }

    pub fn run(&mut self) -> Value {
        Value::Void
    }
}

#[cfg(test)]
pub mod tests {
    use crate::ir::lowerer::tests::lower;

    use super::*;

    pub fn interpret(input: &str) -> Value {
        let program = lower(input);
        let mut interpreter = Interpreter::new(program);
        interpreter.run()
    }

    #[test]
    pub fn empty_is_void() {}
}
