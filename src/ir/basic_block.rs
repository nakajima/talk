use std::{fmt::Display, str::FromStr};

use crate::ir::{instruction::Instruction, ir_error::IRError, terminator::Terminator};

#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct BasicBlockId(pub u32);

impl Display for BasicBlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

impl FromStr for BasicBlockId {
    type Err = IRError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let i = str::parse::<u32>(&s[1..]).map_err(|e| IRError::CouldNotParse(format!("{e:?}")))?;
        Ok(BasicBlockId(i))
    }
}

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
