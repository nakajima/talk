use crate::{ir::register::Register, types::ty::Ty};

pub enum Instruction {
    ConstantInt(Register, i64),
    ConstantFloat(Register, f64),
    Add {
        dest: Register,
        ty: Ty,
        a: Register,
        b: Register,
    },
    Sub {
        dest: Register,
        ty: Ty,
        a: Register,
        b: Register,
    },
    Mul {
        dest: Register,
        ty: Ty,
        a: Register,
        b: Register,
    },
    Div {
        dest: Register,
        ty: Ty,
        a: Register,
        b: Register,
    },
}
