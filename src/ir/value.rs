#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    Reg(u32),
    Int(i64),
    Float(f64),
    Void,
}
