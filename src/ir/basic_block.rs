use std::{fmt::Display, str::FromStr};

use itertools::Itertools;

use crate::ir::{
    instruction::Instruction, ir_error::IRError, list::List, register::Register,
    terminator::Terminator,
};

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
pub struct PhiSource {
    pub from_id: BasicBlockId,
    pub register: Register,
}

impl std::fmt::Display for PhiSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.from_id, self.register)
    }
}

impl From<(BasicBlockId, Register)> for PhiSource {
    fn from(value: (BasicBlockId, Register)) -> Self {
        Self {
            from_id: value.0,
            register: value.1,
        }
    }
}

impl FromStr for PhiSource {
    type Err = IRError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts = s.split(":").collect_vec();
        if parts.len() != 2 {
            return Err(IRError::CouldNotParse(
                "Invalid PhiSource format".to_string(),
            ));
        }

        let from_id = str::parse::<BasicBlockId>(parts[0])
            .map_err(|e| IRError::CouldNotParse(format!("{e:?}")))?;
        let register = str::parse::<Register>(parts[1])
            .map_err(|e| IRError::CouldNotParse(format!("{e:?}")))?;

        Ok(Self { from_id, register })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Phi<T> {
    pub dest: Register,
    pub ty: T,
    pub sources: List<PhiSource>,
}

impl<T: Display> std::fmt::Display for Phi<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = phi {} {}", self.dest, self.ty, self.sources)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock<T> {
    pub id: BasicBlockId,
    pub phis: Vec<Phi<T>>,
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
        for phi in self.phis.iter() {
            parts.push(format!("  {phi}"));
        }

        for instr in self.instructions.iter() {
            parts.push(format!("  {instr}"));
        }

        parts.push(format!("  {}", self.terminator));

        write!(f, "{}", parts.join("\n"))
    }
}
