use derive_visitor::{Drive, DriveMut};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct TypeConstructor {}
