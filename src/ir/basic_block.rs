use std::{fmt::Display, str::FromStr};

use itertools::Itertools;

use crate::ir::{
    instruction::Instruction, ir_error::IRError, ir_ty::IrTy, list::List, register::Register,
    terminator::Terminator, value::Value,
};

#[derive(Debug, Clone, Copy, PartialEq, Default, serde::Serialize, serde::Deserialize)]
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

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct PhiSource {
    pub from_id: BasicBlockId,
    pub value: Value,
}

impl std::fmt::Display for PhiSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.from_id, self.value)
    }
}

impl From<(BasicBlockId, Register)> for PhiSource {
    fn from(value: (BasicBlockId, Register)) -> Self {
        Self {
            from_id: value.0,
            value: value.1.into(),
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
        let value =
            str::parse::<Value>(parts[1]).map_err(|e| IRError::CouldNotParse(format!("{e:?}")))?;

        Ok(Self { from_id, value })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(bound(
    serialize = "T: serde::Serialize",
    deserialize = "T: serde::de::DeserializeOwned"
))]
pub struct Phi<T> {
    pub dest: Register,
    pub ty: T,
    pub sources: List<PhiSource>,
}

impl FromStr for Phi<IrTy> {
    type Err = IRError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let lhs_rhs = s.split("=").collect_vec();
        if lhs_rhs.len() != 2 {
            return Err(IRError::CouldNotParse("invalid phi".into()));
        }

        let dest = Register::from_str(lhs_rhs[0])?;
        let ty_sources = lhs_rhs[1].trim().splitn(2, " ").collect_vec();
        if ty_sources.len() != 2 {
            return Err(IRError::CouldNotParse("invalid phi".into()));
        }

        let ty = IrTy::from_str(ty_sources[0])?;
        let sources = List::<PhiSource>::from_str(ty_sources[1])?;

        Ok(Phi { dest, ty, sources })
    }
}

impl<T: Display> std::fmt::Display for Phi<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = phi {} {}", self.dest, self.ty, self.sources)
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(bound(
    serialize = "T: serde::Serialize",
    deserialize = "T: serde::de::DeserializeOwned"
))]
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

impl FromStr for BasicBlock<IrTy> {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut lines = s.trim().lines();

        let Some(first_line) = lines.next() else {
            return Err(IRError::CouldNotParse("no input".into()));
        };

        let Some(without_colon) = first_line.trim().strip_suffix(":") else {
            return Err(IRError::CouldNotParse("no input".into()));
        };

        let id = BasicBlockId::from_str(without_colon)?;
        let mut phis = vec![];
        let mut instructions = vec![];
        let mut terminator = Terminator::Unreachable;
        for line in lines {
            let line = line.trim();
            if let Ok(phi) = Phi::from_str(line) {
                phis.push(phi);
                continue;
            }

            if let Ok(instr) = Instruction::from_str(line) {
                instructions.push(instr);
                continue;
            }

            if let Ok(term) = Terminator::from_str(line) {
                terminator = term;
                continue;
            }

            return Err(IRError::CouldNotParse(format!(
                "Could not parse IR line: {line:?}"
            )));
        }

        Ok(BasicBlock {
            id,
            phis,
            instructions,
            terminator,
        })
    }
}
