use std::{num::ParseIntError, str::FromStr};

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub struct Register(pub i32);
impl FromStr for Register {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let reg = Register(str::parse(&s[1..])?);
        Ok(reg)
    }
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("%{}", self.0))?;
        Ok(())
    }
}
