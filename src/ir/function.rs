use std::fmt::{Debug, Display};

use crate::{
    ir::{basic_block::BasicBlock, ir_ty::IrTy, list::List, value::Value},
    name::Name,
};

#[derive(Debug, Clone, PartialEq)]
pub struct Function<T: Debug + Display, F: Debug + Display> {
    pub name: Name,
    pub params: List<Value>,
    pub blocks: Vec<BasicBlock<T, F>>,
    pub ty: IrTy,
}

impl<T, F> Display for Function<T, F>
where
    T: Display + Debug,
    F: Display + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        parts.push(format!("func @{}{}", self.name.name_str(), self.params));
        for block in self.blocks.iter() {
            parts.push(format!("{block:?}"));
        }
        write!(f, "{}", parts.join("\n"))
    }
}
