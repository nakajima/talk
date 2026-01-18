//! Variational type checking infrastructure for overload resolution.
//!
//! Based on "The Simple Essence of Overloading" (Benes & Brachthaeuser 2025).
//!
//! Key concepts:
//! - **DimensionId**: A choice point, typically tied to a call site where overload resolution is needed
//! - **AlternativeIndex**: Which alternative within a dimension is selected
//! - **Configuration**: Maps dimensions to selected alternatives (represents a "world")
//! - **ChoiceStore**: Maps (dimension, alternative) to witness information for resolution

use rustc_hash::FxHashMap;

use crate::{
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    types::{constraints::store::ConstraintId, type_error::TypeError},
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

/// A configuration represents a "world" - an assignment of alternatives to dimensions.
///
/// In variational type checking, constraints can be annotated with configurations
/// that specify in which world(s) they apply. A universal configuration applies
/// in all worlds.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Configuration {
    /// Maps each dimension to its selected alternative.
    /// If a dimension is not in the map, the constraint applies to all alternatives.
    choices: FxHashMap<DimensionId, AlternativeIndex>,
}

impl Configuration {
    /// Create a universal configuration (applies in all worlds).
    pub fn universal() -> Self {
        Self::default()
    }

    /// Create a configuration with a single dimension selection.
    pub fn single(dimension: DimensionId, alternative: AlternativeIndex) -> Self {
        let mut choices = FxHashMap::default();
        choices.insert(dimension, alternative);
        Self { choices }
    }

    /// Check if this is the universal configuration.
    pub fn is_universal(&self) -> bool {
        self.choices.is_empty()
    }

    /// Get the selected alternative for a dimension, if any.
    pub fn get(&self, dimension: &DimensionId) -> Option<AlternativeIndex> {
        self.choices.get(dimension).copied()
    }

}

/// Stores the resolved choice for each dimension after constraint solving.
#[derive(Clone, Debug, Default)]
pub struct Resolution {
    resolved: FxHashMap<DimensionId, AlternativeIndex>,
}

impl Resolution {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a resolved choice for a dimension.
    pub fn resolve(&mut self, dimension: DimensionId, alternative: AlternativeIndex) {
        self.resolved.insert(dimension, alternative);
    }

    /// Get the resolved alternative for a dimension.
    pub fn get(&self, dimension: &DimensionId) -> Option<AlternativeIndex> {
        self.resolved.get(dimension).copied()
    }
}

/// An error constraint records a type error that occurred in a specific world.
///
/// During variational type checking, when a constraint fails in a configured
/// (non-universal) context, we don't immediately fail. Instead, we record the
/// error and continue solving. This allows us to rule out alternatives that
/// lead to type errors.
#[derive(Clone, Debug)]
pub struct ErrorConstraint {
    /// The configuration (world) where this error occurred.
    pub config: Configuration,
    /// The type error that occurred.
    pub error: TypeError,
    /// The ID of the constraint that failed.
    pub constraint_id: ConstraintId,
}

/// Stores collected error constraints during constraint solving.
#[derive(Clone, Debug, Default)]
pub struct ErrorConstraintStore {
    errors: Vec<ErrorConstraint>,
}

impl ErrorConstraintStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record an error constraint.
    pub fn record(&mut self, config: Configuration, error: TypeError, constraint_id: ConstraintId) {
        self.errors.push(ErrorConstraint {
            config,
            error,
            constraint_id,
        });
    }

    /// Get all recorded error constraints.
    pub fn errors(&self) -> &[ErrorConstraint] {
        &self.errors
    }

    /// Check if a specific alternative in a dimension is ruled out.
    pub fn is_alternative_ruled_out(
        &self,
        dimension: &DimensionId,
        alternative: AlternativeIndex,
    ) -> bool {
        self.errors.iter().any(|e| {
            e.config.get(dimension) == Some(alternative)
        })
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

/// Error that occurs when overload resolution fails.
#[derive(Clone, Debug)]
pub enum ResolutionError {
    /// All alternatives for a dimension were ruled out by type errors.
    NoValidAlternative {
        dimension: DimensionId,
        errors: Vec<TypeError>,
    },
    /// Multiple alternatives are valid (ambiguous overload).
    Ambiguous {
        dimension: DimensionId,
        valid_alternatives: Vec<AlternativeIndex>,
    },
}

/// Resolve overloads by analyzing which alternatives are ruled out by error constraints.
///
/// For each dimension (choice point) in the ChoiceStore:
/// - If exactly one alternative is valid (not ruled out), resolve to it
/// - If no alternatives are valid, return an error with all the type errors
/// - If multiple alternatives are valid, return an ambiguity error
pub fn resolve_overloads(
    choices: &ChoiceStore,
    errors: &ErrorConstraintStore,
) -> Result<Resolution, Vec<ResolutionError>> {
    let mut resolution = Resolution::new();
    let mut resolution_errors = vec![];

    for dimension in choices.dimensions() {
        let size = choices.dimension_size(dimension);
        if size == 0 {
            continue;
        }

        // Find which alternatives are still valid (not ruled out by errors)
        let valid: Vec<_> = (0..size)
            .map(AlternativeIndex)
            .filter(|alt| !errors.is_alternative_ruled_out(dimension, *alt))
            .collect();

        match valid.len() {
            0 => {
                // All alternatives ruled out - collect all errors for this dimension
                let dimension_errors: Vec<_> = errors
                    .errors()
                    .iter()
                    .filter(|e| e.config.get(dimension).is_some())
                    .map(|e| e.error.clone())
                    .collect();

                resolution_errors.push(ResolutionError::NoValidAlternative {
                    dimension: *dimension,
                    errors: dimension_errors,
                });
            }
            1 => {
                // Exactly one valid alternative - resolve to it
                resolution.resolve(*dimension, valid[0]);
            }
            _ => {
                // Multiple valid alternatives - ambiguous
                // For now, we'll pick the first one and continue
                // A stricter version would report this as an error
                tracing::debug!(
                    "Ambiguous resolution for {:?}: {} valid alternatives, picking first",
                    dimension,
                    valid.len()
                );
                resolution.resolve(*dimension, valid[0]);
                // Uncomment to report as error instead:
                // resolution_errors.push(ResolutionError::Ambiguous {
                //     dimension: *dimension,
                //     valid_alternatives: valid,
                // });
            }
        }
    }

    if resolution_errors.is_empty() {
        Ok(resolution)
    } else {
        Err(resolution_errors)
    }
}
