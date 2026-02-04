#[derive(Default, Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct FileID(pub u32);

impl FileID {
    pub const SYNTHESIZED: FileID = FileID(u32::MAX - 1);
}

#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Default, Clone, Copy, Hash, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct NodeID(pub FileID, pub u32);

impl NodeID {
    pub const SYNTHESIZED: NodeID = NodeID(FileID(u32::MAX - 1), u32::MAX - 1);
    #[cfg(test)]
    pub const ANY: NodeID = NodeID(FileID(u32::MAX), u32::MAX);
}

impl std::fmt::Debug for NodeID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.1 == u32::MAX {
            write!(f, "NodeID(ANY)")?;
        } else {
            write!(f, "NodeID({}, {})", self.0.0, self.1)?;
        }

        Ok(())
    }
}

impl std::fmt::Display for NodeID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.0.0, self.1)
    }
}

impl From<(u32, u32)> for NodeID {
    fn from(other: (u32, u32)) -> Self {
        Self(FileID(other.0), other.1)
    }
}

pub type VariableID = u32;

#[cfg(not(test))]
impl PartialEq for NodeID {
    fn eq(&self, other: &Self) -> bool {
        other.0 == self.0 && other.1 == self.1
    }
}

#[cfg(test)]
impl PartialEq for NodeID {
    fn eq(&self, other: &Self) -> bool {
        if other.1 == u32::MAX || self.1 == u32::MAX {
            true
        } else {
            other.0 == self.0 && other.1 == self.1
        }
    }
}
