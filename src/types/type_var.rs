#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, std::cmp::Ord)]
pub struct TypeVar(u32);

impl TypeVar {
    pub fn new(id: u32) -> Self {
        Self(id)
    }
}
