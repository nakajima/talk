use crate::ir::value::Value;

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator<T> {
    Ret { val: Value, ty: T },
}
