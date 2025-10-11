use crate::ir::{instruction::Instruction, terminator::Terminator};

#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct BasicBlockId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock<T> {
    pub id: BasicBlockId,
    pub instructions: Vec<Instruction<T>>,
    pub terminator: Terminator<T>,
}

impl<T> std::fmt::Display for BasicBlock<T>
where
    T: std::fmt::Display,
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
