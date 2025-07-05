use std::str::FromStr;

use crate::lowering::{ir_error::IRError, lowerer::BasicBlockID, register::Register};

#[derive(Debug, Clone, PartialEq)]
pub struct PhiPredecessors(pub Vec<(Register, BasicBlockID)>);

impl std::fmt::Display for PhiPredecessors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[")?;
        for (i, (reg, id)) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{id}: {reg}")?;
        }
        f.write_str("]")?;
        Ok(())
    }
}

impl FromStr for PhiPredecessors {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let inner = s
            .trim()
            .strip_prefix('[')
            .and_then(|s| s.strip_suffix(']'))
            .ok_or(IRError::ParseError(
                "Unable to parse phi predecessors".to_string(),
            ))?;

        if inner.trim().is_empty() {
            return Ok(PhiPredecessors(vec![]));
        }

        inner
            .split(',')
            .map(|pair_str| {
                let mut parts = pair_str.trim().splitn(2, ':');

                let bb_str = parts
                    .next()
                    .ok_or(IRError::ParseError(
                        "Did not get phi basic block".to_string(),
                    ))?
                    .trim();
                let reg_str = parts
                    .next()
                    .ok_or(IRError::ParseError("Did not get phi register".to_string()))?
                    .trim();

                let bb = bb_str.parse::<BasicBlockID>()?;
                let reg = reg_str.parse::<Register>()?;

                Ok((reg, bb))
            })
            .collect::<Result<Vec<_>, _>>()
            .map(PhiPredecessors)
    }
}
