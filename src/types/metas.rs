use ena::unify::{UnifyKey, UnifyValue};

use crate::types::type_error::TypeError;

#[derive(Default, PartialEq, PartialOrd, Clone, Copy, Debug, Eq, Hash)]
pub struct Level(pub u32);
impl Level {
    pub fn next(&self) -> Level {
        Level(self.0 + 1)
    }

    pub fn prev(&self) -> Level {
        Level(self.0.saturating_sub(1))
    }
}

impl UnifyValue for Level {
    type Error = TypeError;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, Self::Error> {
        Ok(if lhs.0 > rhs.0 { *rhs } else { *lhs })
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct RowMetaId(pub u32);
impl From<u32> for RowMetaId {
    fn from(value: u32) -> Self {
        RowMetaId(value)
    }
}

impl From<RowMetaId> for Meta {
    fn from(val: RowMetaId) -> Self {
        Meta::Row(val)
    }
}

impl UnifyKey for RowMetaId {
    type Value = Level;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "meta"
    }
}

impl std::fmt::Debug for RowMetaId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "π{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Meta {
    Ty(MetaVarId),
    Row(RowMetaId),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct MetaVarId(u32);
impl From<u32> for MetaVarId {
    fn from(value: u32) -> Self {
        MetaVarId(value)
    }
}

impl UnifyKey for MetaVarId {
    type Value = Level;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "meta"
    }
}

impl std::fmt::Debug for MetaVarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "meta({})", self.0)
    }
}
