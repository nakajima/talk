use derive_visitor::{Drive, DriveMut};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct TypeConstructor {}
