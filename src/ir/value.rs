use std::str::FromStr;

use crate::ir::ir_error::IRError;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    Reg(u32),
    Int(i64),
    Float(f64),
    Void,
}

impl FromStr for Value {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(s) = s.trim().strip_prefix("%") {
            return Ok(Self::Reg(str::parse(s).map_err(|e| {
                IRError::CouldNotParse(format!("Value::Reg: {e:?}"))
            })?));
        }

        if s.contains(".") {
            return Ok(Self::Float(
                str::parse(s).map_err(|e| IRError::CouldNotParse(format!("Value: {e:?}")))?,
            ));
        }

        if s == "void" {
            return Ok(Self::Void);
        }

        Ok(Self::Int(str::parse(s).map_err(|e| {
            IRError::CouldNotParse(format!("Value: {e:?}"))
        })?))
    }
}
