#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Default, Clone, Copy, Hash, Eq, PartialOrd, Ord)]
pub struct NodeID(pub i32);

impl NodeID {
    #[cfg(test)]
    pub const ANY: NodeID = NodeID(i32::MIN);
}

impl std::fmt::Debug for NodeID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 == i32::MIN {
            write!(f, "NodeID(ANY)")?;
        } else {
            write!(f, "NodeID({})", self.0)?;
        }

        Ok(())
    }
}

impl std::fmt::Display for NodeID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl From<i32> for NodeID {
    fn from(other: i32) -> Self {
        Self(other)
    }
}

pub type VariableID = u32;

#[cfg(not(test))]
impl PartialEq for NodeID {
    fn eq(&self, other: &Self) -> bool {
        other.0 == self.0
    }
}

#[cfg(test)]
impl PartialEq for NodeID {
    fn eq(&self, other: &Self) -> bool {
        if other.0 == Self::ANY.0 {
            true
        } else {
            other.0 == self.0
        }
    }
}
