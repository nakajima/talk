use crate::{
    ir::{register::Register, value::Value},
    node_id::NodeID,
};

#[derive(Debug, Clone, PartialEq)]
pub enum InstructionMeta {
    NodeID(NodeID),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction<T> {
    ConstantInt(Register, i64, Vec<InstructionMeta>),
    ConstantFloat(Register, f64, Vec<InstructionMeta>),
    Add {
        dest: Register,
        ty: T,
        a: Value,
        b: Value,
        meta: Vec<InstructionMeta>,
    },
    Sub {
        dest: Register,
        ty: T,
        a: Value,
        b: Value,
        meta: Vec<InstructionMeta>,
    },
    Mul {
        dest: Register,
        ty: T,
        a: Value,
        b: Value,
        meta: Vec<InstructionMeta>,
    },
    Div {
        dest: Register,
        ty: T,
        a: Value,
        b: Value,
        meta: Vec<InstructionMeta>,
    },
}
