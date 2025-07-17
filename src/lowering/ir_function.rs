use crate::lowering::{
    ir_type::IRType,
    lowerer::{BasicBlock, DebugInfo},
    register::Register,
};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct IRFunction {
    pub ty: IRType,
    pub name: String,
    pub blocks: Vec<BasicBlock>,
    pub env_ty: Option<IRType>,
    pub env_reg: Option<Register>,
    pub size: i32,
    #[serde(skip)]
    pub debug_info: DebugInfo,
}

impl IRFunction {
    pub(crate) fn args(&self) -> &[IRType] {
        let (IRType::Func(ref args, _) | IRType::Struct(_, ref args, _)) = self.ty else {
            unreachable!("didn't get func for ty: {:?}", self.ty)
        };

        args
    }

    pub(crate) fn ret(&self) -> &IRType {
        if let IRType::Func(_, ref ret) = self.ty {
            return ret;
        };

        if let IRType::Struct(_, _, _) = self.ty {
            return &self.ty;
        };

        unreachable!()
    }
}
