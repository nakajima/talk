//! Variational type checking infrastructure for overload resolution.
//!
//! Based on "The Simple Essence of Overloading" (Benes & Brachthaeuser 2025).
//!
//! Key concepts:
//! - **DimensionId**: A choice point, typically tied to a call site where overload resolution is needed
//! - **AlternativeIndex**: Which alternative within a dimension is selected
//! - **ChoiceStore**: Maps (dimension, alternative) to witness information for resolution

use rustc_hash::FxHashMap;

use crate::{
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
};

/// Identifies a choice point in the program.
/// Each protocol method call site that needs resolution gets its own dimension.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DimensionId(pub NodeID);

/// Index into the alternatives of a choice.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AlternativeIndex(pub usize);

impl From<usize> for AlternativeIndex {
    fn from(value: usize) -> Self {
        AlternativeIndex(value)
    }
}

/// Information about a single alternative in a protocol method choice.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChoiceAlternative {
    /// The type that conforms to the protocol (determines when this alternative applies).
    pub conforming_type: Symbol,
    /// The concrete witness method symbol for this alternative.
    pub witness_sym: Symbol,
    /// The protocol this witness implements.
    pub protocol_id: ProtocolId,
}

/// Stores information about all choices and their alternatives.
#[derive(Clone, Debug, Default)]
pub struct ChoiceStore {
    /// Maps (dimension, alternative_index) -> information about that alternative
    alternatives: FxHashMap<(DimensionId, AlternativeIndex), ChoiceAlternative>,
    /// Maps dimension -> number of alternatives
    dimension_sizes: FxHashMap<DimensionId, usize>,
}

impl ChoiceStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an alternative for a dimension.
    pub fn register_alternative(
        &mut self,
        dimension: DimensionId,
        index: AlternativeIndex,
        alternative: ChoiceAlternative,
    ) {
        self.alternatives.insert((dimension, index), alternative);
        let size = self.dimension_sizes.entry(dimension).or_insert(0);
        *size = (*size).max(index.0 + 1);
    }

    /// Get information about an alternative.
    pub fn get_alternative(
        &self,
        dimension: DimensionId,
        index: AlternativeIndex,
    ) -> Option<&ChoiceAlternative> {
        self.alternatives.get(&(dimension, index))
    }

    /// Get the number of alternatives for a dimension.
    pub fn dimension_size(&self, dimension: &DimensionId) -> usize {
        self.dimension_sizes.get(dimension).copied().unwrap_or(0)
    }

    /// Get all dimensions that have choices registered.
    pub fn dimensions(&self) -> impl Iterator<Item = &DimensionId> {
        self.dimension_sizes.keys()
    }

    /// Find the alternative for a dimension that matches the given conforming type.
    /// Returns the witness symbol if found.
    pub fn resolve_for_type(
        &self,
        dimension: DimensionId,
        conforming_type: Symbol,
    ) -> Option<Symbol> {
        let size = self.dimension_size(&dimension);
        for i in 0..size {
            if let Some(alt) = self.get_alternative(dimension, AlternativeIndex(i)) {
                if alt.conforming_type == conforming_type {
                    return Some(alt.witness_sym);
                }
            }
        }
        None
    }
}
