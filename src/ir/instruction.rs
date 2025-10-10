use std::str::FromStr;

use crate::{
    ir::{ir_error::IRError, ir_ty::IrTy, list::List, register::Register, value::Value},
    node_id::{FileID, NodeID},
    types::ty::Ty,
};

#[derive(Debug, Clone, PartialEq)]
pub enum InstructionMeta {
    #[doc = "id:$file_id:$id"]
    Source(NodeID),
}

impl FromStr for InstructionMeta {
    type Err = IRError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        println!("s: {s:?}");
        if let Some(s) = s.strip_prefix("id:") {
            let split = s.split(":").collect::<Vec<_>>();
            println!("s: {s:?} split: {split:?}");
            let file_id: u32 =
                str::parse(split[0]).map_err(|e| IRError::CouldNotParse(format!("{e:?}")))?;
            let id: u32 =
                str::parse(split[1]).map_err(|e| IRError::CouldNotParse(format!("{e:?}")))?;
            return Ok(Self::Source(NodeID(FileID(file_id), id)));
        }

        Err(IRError::CouldNotParse(format!(
            "No match for instruction meta: {s:?}"
        )))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction<T> {
    #[doc = "$dest = int $val $meta"]
    ConstantInt {
        dest: Register,
        val: i64,
        meta: List<InstructionMeta>,
    },
    #[doc = "$dest = float $val $meta"]
    ConstantFloat {
        dest: Register,
        val: f64,
        meta: List<InstructionMeta>,
    },
    #[doc = "$dest = add $ty $a $b $meta"]
    Add {
        dest: Register,
        ty: T,
        a: Value,
        b: Value,
        meta: List<InstructionMeta>,
    },
    #[doc = "$dest = sub $ty $a $b $meta"]
    Sub {
        dest: Register,
        ty: T,
        a: Value,
        b: Value,
        meta: List<InstructionMeta>,
    },
    #[doc = "$dest = mul $ty $a $b $meta"]
    Mul {
        dest: Register,
        ty: T,
        a: Value,
        b: Value,
        meta: List<InstructionMeta>,
    },
    #[doc = "$dest = div $ty $a $b $meta"]
    Div {
        dest: Register,
        ty: T,
        a: Value,
        b: Value,
        meta: List<InstructionMeta>,
    },
}

#[allow(clippy::from_over_into)]
impl Into<Instruction<Ty>> for Instruction<IrTy> {
    fn into(self) -> Instruction<Ty> {
        match self {
            Instruction::ConstantInt { dest, val, meta } => {
                Instruction::ConstantInt { dest, val, meta }
            }
            Instruction::ConstantFloat { dest, val, meta } => {
                Instruction::ConstantFloat { dest, val, meta }
            }
            Instruction::Add {
                dest,
                ty,
                a,
                b,
                meta,
            } => Instruction::Add {
                dest,
                ty: ty.into(),
                a,
                b,
                meta,
            },
            Instruction::Sub {
                dest,
                ty,
                a,
                b,
                meta,
            } => Instruction::Sub {
                dest,
                ty: ty.into(),
                a,
                b,
                meta,
            },
            Instruction::Mul {
                dest,
                ty,
                a,
                b,
                meta,
            } => Instruction::Mul {
                dest,
                ty: ty.into(),
                a,
                b,
                meta,
            },
            Instruction::Div {
                dest,
                ty,
                a,
                b,
                meta,
            } => Instruction::Div {
                dest,
                ty: ty.into(),
                a,
                b,
                meta,
            },
        }
    }
}

pub fn parse_vec<T>(s: &str) -> Result<Vec<T>, anyhow::Error>
where
    T: FromStr,
    <T as FromStr>::Err: std::fmt::Display,
{
    // Accepts:
    // - plain tokens:            `a b c`
    // - comma / semicolon:       `a,b,c` or `a; b; c`
    // - optional wrappers:       `[a, b]` or `(a b)` or `{a;b}`
    // - arbitrary whitespace
    let s = s
        .trim()
        .trim_start_matches(|c| "([{".contains(c))
        .trim_end_matches(|c| ")]}".contains(c));
    let mut out = Vec::new();

    // Split on commas/semicolons OR whitespace (one or more)
    // This treats runs of separators as one.
    for chunk in s
        .split(|c: char| c == ',' || c == ';' || c.is_whitespace())
        .filter(|t| !t.is_empty())
    {
        out.push(
            chunk
                .parse::<T>()
                .map_err(|e| anyhow::anyhow!("failed to parse list item `{chunk}`: {e}"))?,
        );
    }
    Ok(out)
}

#[cfg(test)]
pub mod tests {
    use crate::ir::{
        instruction::Instruction, ir_ty::IrTy, parse_instruction, register::Register, value::Value,
    };

    #[test]
    fn parses_constant_int() {
        assert_eq!(
            parse_instruction::<IrTy>("%1 = int 123"),
            Instruction::ConstantInt {
                dest: Register(1),
                val: 123,
                meta: vec![].into(),
            }
        )
    }

    #[test]
    fn parses_constant_float() {
        assert_eq!(
            parse_instruction::<IrTy>("%1 = float 1.23"),
            Instruction::ConstantFloat {
                dest: Register(1),
                val: 1.23,
                meta: vec![].into(),
            }
        )
    }

    #[test]
    fn parses_add() {
        assert_eq!(
            parse_instruction::<IrTy>("%1 = add int %2 %3"),
            Instruction::Add {
                dest: 1.into(),
                ty: IrTy::Int,
                a: Value::Reg(2),
                b: Value::Reg(3),
                meta: vec![].into()
            }
        )
    }

    #[test]
    fn parses_sub() {
        assert_eq!(
            parse_instruction::<IrTy>("%1 = sub int %2 %3"),
            Instruction::Sub {
                dest: 1.into(),
                ty: IrTy::Int,
                a: Value::Reg(2),
                b: Value::Reg(3),
                meta: vec![].into()
            }
        )
    }

    #[test]
    fn parses_mul() {
        assert_eq!(
            parse_instruction::<IrTy>("%1 = mul int %2 %3"),
            Instruction::Mul {
                dest: 1.into(),
                ty: IrTy::Int,
                a: Value::Reg(2),
                b: Value::Reg(3),
                meta: vec![].into()
            }
        )
    }

    #[test]
    fn parses_div() {
        assert_eq!(
            parse_instruction::<IrTy>("%1 = div int %2 %3"),
            Instruction::Div {
                dest: 1.into(),
                ty: IrTy::Int,
                a: Value::Reg(2),
                b: Value::Reg(3),
                meta: vec![].into()
            }
        )
    }
}
