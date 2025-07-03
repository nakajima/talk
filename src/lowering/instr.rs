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

    #[doc = "print $val;"]
    Print {
        val: IRValue
    },

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
}
