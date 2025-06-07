use crate::lowering::lowerer::{BasicBlockID, IRType, RefKind, Register};

#[derive(Debug, Clone, PartialEq)]
pub enum Instr {
    ConstantInt(Register, i64),
    ConstantFloat(Register, f64),
    ConstantBool(Register, bool),
    Add(Register, IRType, Register, Register),
    Sub(Register, IRType, Register, Register),
    Mul(Register, IRType, Register, Register),
    Div(Register, IRType, Register, Register),
    StoreLocal(Register, IRType, Register),
    LoadLocal(Register, IRType, Register),
    Phi(Register, IRType, Vec<(Register, BasicBlockID)>),
    Ref(Register, IRType, RefKind),
    Eq(Register, IRType, Register, Register),
    Call {
        dest_reg: Option<Register>,
        callee: String,
        args: Vec<Register>,
        ty: IRType,
    },
    GetEnumTag(Register /* tag */, Register /* scrutinee */),
    GetEnumValue(
        Register, /* dest */
        IRType,
        Register, /* scrutinee register */
        u16,      /* tag */
        u16,      /* index of value */
    ),

    TagVariant(
        Register,      /* dest */
        IRType,        /* enum type */
        u16,           /* tag */
        Vec<Register>, /* associated values */
    ),

    // Flow control
    Ret(Option<(IRType, Register)>),
    Jump(BasicBlockID),
    JumpIf(Register, BasicBlockID),
    JumpUnless(Register, BasicBlockID),
    Unreachable,
}
