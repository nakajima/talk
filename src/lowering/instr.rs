use std::{fmt::Display, str::FromStr};

use crate::lowering::lowerer::{
    BasicBlockID, IRError, IRType, PhiPredecessors, RefKind, Register, RegisterList,
};

// Newtypes for complex arguments to make formatting unambiguous
#[derive(Debug, Clone, PartialEq)]
pub struct FuncName(pub String);

#[derive(Debug, Clone, PartialEq)]
pub enum Callee {
    FuncName(String),
    Register(Register),
}

impl Display for Callee {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FuncName(name) => write!(f, "{}", name),
            Self::Register(reg) => write!(f, "{}", reg),
        }
    }
}

impl FromStr for Callee {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.trim().chars().next() {
            Some('@') => Ok(Self::FuncName(s.to_string())),
            Some('%') => Ok(Self::Register(Register::from_str(s)?)),
            _ => Err(IRError::CannotParse),
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

    #[doc = "$0 = store $1 $2;"]
    MakeBox(Register, IRType, Register),

    #[doc = "$0 = load $1 $2;"]
    LoadBox(Register, IRType, Register),

    #[doc = "$0 = add $1 $2, $3;"]
    Add(Register, IRType, Register, Register),

    #[doc = "$0 = sub $1 $2, $3;"]
    Sub(Register, IRType, Register, Register),

    #[doc = "$0 = mul $1 $2, $3;"]
    Mul(Register, IRType, Register, Register),

    #[doc = "$0 = div $1 $2, $3;"]
    Div(Register, IRType, Register, Register),

    #[doc = "$0 = stlocal $1 $2;"]
    StoreLocal(Register, IRType, Register),

    #[doc = "$0 = ldlocal $1 $2;"]
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

    #[doc = "$dest = mkclsr $func ($captures);"]
    MakeClosure {
        dest: Register,
        func: FuncName,
        captures: RegisterList,
    },

    // #[doc = "$dest = callclsr $closure ($args);"]
    // CallClosure {
    //     dest: Register,
    //     closure: Register,
    //     args: RegisterList,
    // },
    #[doc = "$dest = rcp $env $index;"]
    ReadCapture {
        dest: Register,
        env: Register,
        index: usize,
    },

    #[doc = "$dest = struct {{$values}};"]
    MakeStruct {
        dest: Register,
        values: RegisterList,
    },

    #[doc = "$dest = getfieldof $ty $structure $index;"]
    GetFieldOf {
        dest: Register,
        ty: IRType,
        structure: Register,
        index: usize,
    },

    #[doc = "wcp $env $index $value;"]
    WriteCapture {
        env: Register,
        index: usize,
        value: Register,
    },

    #[doc = "store $ty $pointer $val;"]
    StorePointer {
        ty: IRType,
        pointer: Register,
        val: Register,
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
    Ret(IRType, Option<Register>),

    #[doc = "jump $0;"]
    Jump(BasicBlockID),

    #[doc = "jmpif $0 $1;"]
    JumpIf(Register, BasicBlockID),

    #[doc = "jmpnl $0 $1;"]
    JumpUnless(Register, BasicBlockID),

    #[doc = "unreachable;"]
    Unreachable,
}
