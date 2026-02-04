use std::fmt::{Debug, Display};

use crate::{
    ir::{basic_block::BasicBlock, ir_ty::IrTy, list::List, register::Register, value::Value},
    name_resolution::symbol::Symbol,
};

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(bound(serialize = "T: serde::Serialize", deserialize = "T: serde::de::DeserializeOwned"))]
pub struct Function<T: Debug + Display> {
    pub name: Symbol,
    pub params: List<Value>,
    pub blocks: Vec<BasicBlock<T>>,
    pub ty: IrTy,
    pub register_count: usize,
    /// For methods, the register containing the final self value (after mutations).
    /// Used by the interpreter to write back mutated self to the caller.
    pub self_out: Option<Register>,
}

impl<T> Display for Function<T>
where
    T: Display + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        parts.push(format!("func @{}{}", self.name, self.params));
        for block in self.blocks.iter() {
            parts.push(format!("{block}"));
        }
        write!(f, "{}", parts.join("\n"))
    }
}
