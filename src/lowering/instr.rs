use std::{fmt::Display, str::FromStr};

use crate::lowering::{
    ir_error::IRError,
    ir_type::IRType,
    ir_value::IRValue,
    lowerer::{BasicBlockID, RefKind, RegisterList},
    phi_predecessors::PhiPredecessors,
    register::{self, Register},
};

// Newtypes for complex arguments to make formatting unambiguous
#[derive(Debug, Clone, PartialEq)]
pub struct FuncName(pub String);

#[derive(Debug, Clone, PartialEq)]
pub enum Callee {
    Register(Register),
    Name(String),
}

impl From<&str> for Callee {
    fn from(value: &str) -> Self {
        Self::Name(value.to_string())
    }
}

impl Display for Callee {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Name(name) => write!(f, "{name}"),
            Self::Register(reg) => write!(f, "{reg}"),
        }
    }
}

impl FromStr for Callee {
    type Err = <register::Register as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(if s.trim().starts_with("@") {
            Callee::Name(s.trim().into())
        } else {
            Callee::Register(Register::from_str(s.trim())?)
        })
    }
}

impl From<Register> for Callee {
    fn from(value: Register) -> Self {
        Self::Register(value)
    }
}

impl Callee {
    pub fn try_register(&self) -> Result<Register, IRError> {
        match self {
            Self::Register(reg) => Ok(*reg),
            _ => Err(IRError::Unknown(format!("Invalid IR Value: {self:?}"))),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instr {
    #[doc = "$0 = int $1;"]
    ConstantInt(Register, i64),

    #[doc = "$0 = float $1;"]
    ConstantFloat(Register, f64),

    #[doc = "$0 = bool $1;"]
    ConstantBool(Register, bool),

    #[doc = "$0 = add $1 $2, $3;"]
    Add(Register, IRType, Register, Register),

    #[doc = "$0 = sub $1 $2, $3;"]
    Sub(Register, IRType, Register, Register),

    #[doc = "$0 = mul $1 $2, $3;"]
    Mul(Register, IRType, Register, Register),

    #[doc = "$0 = div $1 $2, $3;"]
    Div(Register, IRType, Register, Register),

    #[doc = "store $1 $0, $2;"]
    StoreLocal(Register, IRType, Register),

    #[doc = "load $1 $0, $2;"]
    LoadLocal(Register, IRType, Register),

    #[doc = "$0 = phi $1 $2;"]
    Phi(Register, IRType, PhiPredecessors),

    #[doc = "$0 = ref $1 $2;"]
    Ref(Register, IRType, RefKind),

    #[doc = "$0 = eq $1 $2, $3;"]
    Eq(Register, IRType, Register, Register),

    #[doc = "$0 = ne $1 $2, $3;"]
    Ne(Register, IRType, Register, Register),

    #[doc = "$0 = lt $1 $2, $3;"]
    LessThan(Register, IRType, Register, Register),

    #[doc = "$0 = lte $1 $2, $3;"]
    LessThanEq(Register, IRType, Register, Register),

    #[doc = "$0 = gt $1 $2, $3;"]
    GreaterThan(Register, IRType, Register, Register),

    #[doc = "$0 = gte $1 $2, $3;"]
    GreaterThanEq(Register, IRType, Register, Register),

    #[doc = "$dest = alloc $ty $count;"]
    Alloc {
        dest: Register,
        ty: IRType,
        count: Option<IRValue>,
    },

    #[doc = "$dest = const $ty $val;"]
    Const {
        dest: Register,
        ty: IRType,
        val: IRValue,
    },

    #[doc = "store $ty $val $location;"]
    Store {
        ty: IRType,
        val: IRValue,
        location: Register,
    },

    #[doc = "$dest = load $ty $addr;"]
    Load {
        dest: Register,
        ty: IRType,
        addr: Register,
    },

    #[doc = "$dest = getelementptr $ty $base $index;"]
    GetElementPointer {
        dest: Register,
        base: Register,
        ty: IRType,
        index: IRValue,
    },

    #[doc = "$dest = struct $ty ($values);"]
    MakeStruct {
        dest: Register,
        ty: IRType,
        values: RegisterList,
    },

    #[doc = "$dest = getvalueof $ty $structure $index;"]
    GetValueOf {
        dest: Register,
        ty: IRType,
        structure: Register,
        index: usize,
    },

    #[doc = "$dest_reg = call $ty $callee($args);"]
    Call {
        dest_reg: Register,
        ty: IRType,
        callee: Callee,
        args: RegisterList,
    },

    #[doc = "$0 = gettagof $1;"]
    GetEnumTag(Register /* tag */, Register /* scrutinee */),

    #[doc = "$0 = enumvalue $1 $2 $3 $4;"]
    GetEnumValue(
        Register, /* dest */
        IRType,
        Register, /* scrutinee register */
        u16,      /* tag */
        u16,      /* index of value */
    ),

    #[doc = "$0 = tagvar $1 $2 ($3);"]
    TagVariant(
        Register,     /* dest */
        IRType,       /* enum type */
        u16,          /* tag */
        RegisterList, /* associated values */
    ),

    // Flow control
    #[doc = "ret $0 $1;"]
    Ret(IRType, Option<IRValue>),

    #[doc = "jump $0;"]
    Jump(BasicBlockID),

    #[doc = "br $cond $true_target $false_target;"]
    Branch {
        cond: Register,
        true_target: BasicBlockID,
        false_target: BasicBlockID,
    },

    #[doc = "print $ty $val;"]
    Print { ty: IRType, val: IRValue },

    #[doc = "unreachable;"]
    Unreachable,
}

impl Instr {
    /// Returns a list of successor BasicBlockIDs for a terminator instruction.
    pub fn successors(&self) -> Vec<BasicBlockID> {
        match self {
            Instr::Jump(target) => vec![*target],
            Instr::Branch {
                true_target,
                false_target,
                ..
            } => vec![*true_target, *false_target],

            // Return and Unreachable terminate flow and have no successors.
            Instr::Ret(..) => vec![],
            Instr::Unreachable => vec![],

            // All other instructions are not terminators, so they have no successors.
            _ => vec![],
        }
    }

    /// Returns the register defined by this instruction, if any.
    pub fn dest(&self) -> Option<Register> {
        use Instr::*;
        match self {
            ConstantInt(r, _)
            | ConstantFloat(r, _)
            | ConstantBool(r, _)
            | Add(r, ..)
            | Sub(r, ..)
            | Mul(r, ..)
            | Div(r, ..)
            | StoreLocal(r, ..)
            | LoadLocal(r, ..)
            | Phi(r, ..)
            | Ref(r, ..)
            | Eq(r, ..)
            | Ne(r, ..)
            | LessThan(r, ..)
            | LessThanEq(r, ..)
            | GreaterThan(r, ..)
            | GreaterThanEq(r, ..)
            | Alloc { dest: r, .. }
            | Const { dest: r, .. }
            | Load { dest: r, .. }
            | GetElementPointer { dest: r, .. }
            | MakeStruct { dest: r, .. }
            | GetValueOf { dest: r, .. }
            | Call { dest_reg: r, .. }
            | GetEnumTag(r, _)
            | GetEnumValue(r, ..)
            | TagVariant(r, ..) => Some(*r),
            _ => None,
        }
    }

    /// Returns registers read by this instruction.
    pub fn read_regs(&self) -> Vec<Register> {
        use Instr::*;
        match self {
            Add(_, _, r1, r2)
            | Sub(_, _, r1, r2)
            | Mul(_, _, r1, r2)
            | Div(_, _, r1, r2)
            | Eq(_, _, r1, r2)
            | Ne(_, _, r1, r2)
            | LessThan(_, _, r1, r2)
            | LessThanEq(_, _, r1, r2)
            | GreaterThan(_, _, r1, r2)
            | GreaterThanEq(_, _, r1, r2) => vec![*r1, *r2],

            StoreLocal(_, _, r) | LoadLocal(_, _, r) | GetEnumTag(_, r) => vec![*r],

            Phi(_, _, preds) => preds.0.iter().map(|(r, _)| *r).collect(),

            Branch { cond, .. } => vec![*cond],

            Ret(_, Some(IRValue::Register(r))) => vec![*r],

            Call { callee, args, .. } => {
                let mut regs = Vec::new();
                if let Callee::Register(r) = callee {
                    regs.push(*r);
                }
                regs.extend(args.0.iter().map(|t| t.register));
                regs
            }

            Load { addr, .. } => vec![*addr],

            Store { val, location, .. } => {
                let mut regs = Vec::new();
                if let IRValue::Register(r) = val {
                    regs.push(*r);
                }
                regs.push(*location);
                regs
            }

            Alloc { count, .. } => match count {
                Some(IRValue::Register(r)) => vec![*r],
                _ => Vec::new(),
            },

            GetElementPointer { base, index, .. } => {
                let mut regs = vec![*base];
                if let IRValue::Register(r) = index {
                    regs.push(*r);
                }
                regs
            }

            MakeStruct { values, .. } => values.0.iter().map(|v| v.register).collect(),

            GetValueOf { structure, .. } => vec![*structure],

            TagVariant(_, _, _, values) => values.0.iter().map(|v| v.register).collect(),

            Print { val, .. } => match val {
                IRValue::Register(r) => vec![*r],
                _ => Vec::new(),
            },

            Const { val, .. } => match val {
                IRValue::Register(r) => vec![*r],
                _ => Vec::new(),
            },

            _ => Vec::new(),
        }
    }

    /// Returns true if this instruction has no side effects.
    pub fn is_pure(&self) -> bool {
        use Instr::*;
        match self {
            Call { .. }
            | Store { .. }
            | Print { .. }
            | Ret(..)
            | Jump(..)
            | Branch { .. }
            | Unreachable => false,
            _ => true,
        }
    }
}
