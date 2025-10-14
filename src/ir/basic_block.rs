use crate::ir::{instruction::Instruction, terminator::Terminator};

#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct BasicBlockId(pub u32);

#[derive(Clone, PartialEq)]
pub struct BasicBlock<T, F> {
    pub id: BasicBlockId,
    pub instructions: Vec<Instruction<T, F>>,
    pub terminator: Terminator<T>,
}

impl<T, F> std::fmt::Debug for BasicBlock<T, F>
where
    T: std::fmt::Display,
    F: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl<T, F> std::fmt::Display for BasicBlock<T, F>
where
    T: std::fmt::Display,
    F: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        parts.push(format!("#{}:", self.id.0));
        for instr in self.instructions.iter() {
            parts.push(format!("  {instr}"));
        }

        parts.push(format!("  {}", self.terminator));

        write!(f, "{}", parts.join("\n"))
    }
}
