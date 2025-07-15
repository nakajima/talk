#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Default, Clone, Copy, Hash, Eq)]
pub struct ExprID(pub i32);

impl ExprID {
    #[cfg(test)]
    pub const ANY: ExprID = ExprID(i32::MIN);
}

impl std::fmt::Debug for ExprID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 == i32::MIN {
            write!(f, "ExprID(ANY)")?;
        } else {
            write!(f, "ExprID({})", self.0)?;
        }

        Ok(())
    }
}

impl From<i32> for ExprID {
    fn from(other: i32) -> Self {
        Self(other)
    }
}

pub type VariableID = u32;

#[cfg(not(test))]
impl PartialEq for ExprID {
    fn eq(&self, other: &Self) -> bool {
        other.0 == self.0
    }
}

#[cfg(test)]
impl PartialEq for ExprID {
    fn eq(&self, other: &Self) -> bool {
        if other.0 == Self::ANY.0 {
            true
        } else {
            other.0 == self.0
        }
    }
}
