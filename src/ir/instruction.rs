use std::str::FromStr;

use crate::{
    ir::{ir_error::IRError, ir_ty::IrTy, list::List, register::Register, value::Value},
    label::Label,
    node_id::{FileID, NodeID},
    types::ty::Ty,
};

#[derive(Debug, Clone, PartialEq)]
pub enum InstructionMeta {
    #[doc = "id:$file_id:$id"]
    Source(NodeID),
}

impl std::fmt::Display for InstructionMeta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source(id) => write!(f, "id:{}:{}", id.0.0, id.1),
        }
    }
}

impl FromStr for InstructionMeta {
    type Err = IRError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(s) = s.strip_prefix("id:") {
            let split = s.split(":").collect::<Vec<_>>();
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
pub enum CmpOperator {
    Greater,
    GreaterEquals,
    Less,
    LessEquals,
    Equals,
    NotEquals,
}

impl std::fmt::Display for CmpOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CmpOperator::Greater => write!(f, ">"),
            CmpOperator::GreaterEquals => write!(f, ">="),
            CmpOperator::Less => write!(f, "<"),
            CmpOperator::LessEquals => write!(f, "<="),
            CmpOperator::Equals => write!(f, "=="),
            CmpOperator::NotEquals => write!(f, "!="),
        }
    }
}

impl FromStr for CmpOperator {
    type Err = IRError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with(">=") {
            return Ok(CmpOperator::GreaterEquals);
        }
        if s.starts_with(">") {
            return Ok(CmpOperator::Greater);
        }
        if s.starts_with("<=") {
            return Ok(CmpOperator::LessEquals);
        }
        if s.starts_with("<") {
            return Ok(CmpOperator::Less);
        }
        if s.starts_with("==") {
            return Ok(CmpOperator::Equals);
        }
        if s.starts_with("!=") {
            return Ok(CmpOperator::NotEquals);
        }
        Err(IRError::CouldNotParse(format!(
            "No match cmp operator: {s:?}"
        )))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction<T> {
    #[doc = "$dest = const $ty $val $meta"]
    Constant {
        dest: Register,
        ty: T,
        val: Value,
        meta: List<InstructionMeta>,
    },
    #[doc = "$dest = cmp $ty $lhs $op $rhs $meta"]
    Cmp {
        dest: Register,
        lhs: Value,
        rhs: Value,
        ty: T,
        op: CmpOperator,
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
    #[doc = "$dest = ref $ty $val"]
    Ref { dest: Register, ty: T, val: Value },
    #[doc = "$dest = call $ty $callee $args $meta"]
    Call {
        dest: Register,
        ty: T,
        callee: Value,
        args: List<Value>,
        meta: List<InstructionMeta>,
    },
    #[doc = "$dest = record $ty $record $meta"]
    Record {
        dest: Register,
        ty: T,
        record: List<Value>,
        meta: List<InstructionMeta>,
    },
    #[doc = "$dest = getfield $ty $record $field $meta"]
    GetField {
        dest: Register,
        ty: T,
        record: Register,
        field: Label,
        meta: List<InstructionMeta>,
    },
    #[doc = "$dest = setfield $ty $record $field $val $meta"]
    SetField {
        dest: Register,
        val: Value,
        ty: T,
        record: Register,
        field: Label,
        meta: List<InstructionMeta>,
    },
}

impl<T> Instruction<T> {
    pub fn map_type<U>(self, mut map: impl FnMut(T) -> U) -> Instruction<U> {
        match self {
            Instruction::Constant {
                dest,
                val,
                meta,
                ty,
            } => Instruction::Constant {
                dest,
                val,
                meta,
                ty: map(ty),
            },
            Instruction::Record {
                dest,
                ty,
                record,
                meta,
            } => Instruction::Record {
                dest,
                ty: map(ty),
                record,
                meta,
            },
            Instruction::GetField {
                dest,
                ty,
                record,
                field,
                meta,
            } => Instruction::GetField {
                dest,
                ty: map(ty),
                record,
                field,
                meta,
            },
            Instruction::SetField {
                dest,
                val,
                ty,
                record,
                field,
                meta,
            } => Instruction::SetField {
                dest,
                val,
                ty: map(ty),
                record,
                field,
                meta,
            },
            Instruction::Ref { dest, ty, val } => Instruction::Ref {
                dest,
                ty: map(ty),
                val,
            },
            Instruction::Add {
                dest,
                ty,
                a,
                b,
                meta,
            } => Instruction::Add {
                dest,
                ty: map(ty),
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
                ty: map(ty),
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
                ty: map(ty),
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
                ty: map(ty),
                a,
                b,
                meta,
            },
            Instruction::Call {
                dest,
                ty,
                callee,
                args,
                meta,
            } => Instruction::Call {
                dest,
                ty: map(ty),
                callee,
                args,
                meta,
            },
            Instruction::Cmp {
                dest,
                lhs,
                rhs,
                op,
                meta,
                ty,
            } => Instruction::Cmp {
                dest,
                lhs,
                rhs,
                op,
                meta,
                ty: map(ty),
            },
        }
    }
}

#[allow(clippy::from_over_into)]
impl Into<Instruction<Ty>> for Instruction<IrTy> {
    fn into(self) -> Instruction<Ty> {
        self.map_type(Into::into)
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
            parse_instruction::<IrTy>("%1 = const int 123"),
            Instruction::Constant {
                dest: Register(1),
                val: Value::Int(123),
                ty: IrTy::Int,
                meta: vec![].into(),
            }
        )
    }

    #[test]
    fn parses_constant_float() {
        assert_eq!(
            parse_instruction::<IrTy>("%1 = const float 1.23"),
            Instruction::Constant {
                dest: Register(1),
                val: Value::Float(1.23),
                ty: IrTy::Float,
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
