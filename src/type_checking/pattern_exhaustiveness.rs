//! Exhaustiveness checking for pattern matching with row-based enums

use std::collections::{BTreeSet, HashMap};

use crate::{environment::Environment, parsed_expr::Pattern, ty::{RowKind, Ty}, type_var_id::TypeVarID};

/// Result of exhaustiveness checking
#[derive(Debug, Clone, PartialEq)]
pub enum ExhaustivenessResult {
    /// Pattern matching is exhaustive
    Exhaustive,
    /// Pattern matching is not exhaustive, with missing patterns
    NonExhaustive(Vec<MissingPattern>),
}

/// Represents a pattern that is not covered
#[derive(Debug, Clone, PartialEq)]
pub enum MissingPattern {
    /// A specific variant is not covered
    Variant {
        enum_name: String,
        variant_name: String,
    },
    /// Multiple variants are not covered
    Variants {
        enum_name: String,
        variant_names: Vec<String>,
    },
    /// The enum is open (has row extension) so can't be exhaustive without wildcard
    OpenEnum { enum_name: String },
}

/// Checks exhaustiveness of pattern matching
pub struct ExhaustivenessChecker<'a> {
    env: &'a Environment,
}

impl<'a> ExhaustivenessChecker<'a> {
    pub fn new(env: &'a Environment) -> Self {
        Self { env }
    }

    /// Check if a match expression is exhaustive
    pub fn check_match(&self, scrutinee_ty: &Ty, patterns: &[Pattern]) -> ExhaustivenessResult {
        // First check if there's a wildcard or catch-all variable pattern
        if patterns
            .iter()
            .any(|p| matches!(p, Pattern::Wildcard | Pattern::Bind(_)))
        {
            return ExhaustivenessResult::Exhaustive;
        }

        match scrutinee_ty {
            Ty::Row { nominal_id: Some(enum_id), kind: RowKind::Enum, .. } => self.check_enum_exhaustiveness(enum_id, patterns),
            Ty::TypeVar(type_var) => self.check_type_var_exhaustiveness(type_var, patterns),
            Ty::Bool => self.check_bool_exhaustiveness(patterns),
            _ => {
                // For other types, we can't determine exhaustiveness without a wildcard
                ExhaustivenessResult::NonExhaustive(vec![])
            }
        }
    }

    /// Check exhaustiveness for boolean patterns
    fn check_bool_exhaustiveness(&self, patterns: &[Pattern]) -> ExhaustivenessResult {
        let mut has_true = false;
        let mut has_false = false;

        for pattern in patterns {
            match pattern {
                Pattern::LiteralTrue => has_true = true,
                Pattern::LiteralFalse => has_false = true,
                Pattern::Wildcard | Pattern::Bind(_) => return ExhaustivenessResult::Exhaustive,
                _ => {}
            }
        }

        if has_true && has_false {
            ExhaustivenessResult::Exhaustive
        } else {
            ExhaustivenessResult::NonExhaustive(vec![])
        }
    }

    /// Check exhaustiveness for traditional enum types
    fn check_enum_exhaustiveness(
        &self,
        enum_id: &crate::SymbolID,
        patterns: &[Pattern],
    ) -> ExhaustivenessResult {
        let Some(enum_def) = self.env.lookup_enum(enum_id) else {
            return ExhaustivenessResult::NonExhaustive(vec![]);
        };

        let all_variants: BTreeSet<_> =
            enum_def.variants().iter().map(|v| v.name.clone()).collect();

        let covered_variants: BTreeSet<_> = patterns
            .iter()
            .filter_map(|p| match p {
                Pattern::Variant { variant_name, .. } => Some(variant_name.clone()),
                _ => None,
            })
            .collect();

        let missing_variants: Vec<_> = all_variants
            .difference(&covered_variants)
            .cloned()
            .collect();

        if missing_variants.is_empty() {
            ExhaustivenessResult::Exhaustive
        } else {
            ExhaustivenessResult::NonExhaustive(vec![MissingPattern::Variants {
                enum_name: enum_def.name_str.clone(),
                variant_names: missing_variants,
            }])
        }
    }

    /// Check exhaustiveness for row-based enum types (type variables with enum variants)
    fn check_type_var_exhaustiveness(
        &self,
        type_var: &TypeVarID,
        patterns: &[Pattern],
    ) -> ExhaustivenessResult {
        // Get all enum variants from row constraints
        let variants = self.get_enum_variants_from_rows(type_var);

        if variants.is_empty() {
            // No enum variants found, can't determine exhaustiveness
            return ExhaustivenessResult::NonExhaustive(vec![]);
        }

        // Check if this is an exact row (closed enum) or has an extension (open enum)
        let is_exact = self.has_exact_row(type_var);

        if !is_exact {
            // Open enum - can't be exhaustive without wildcard
            return ExhaustivenessResult::NonExhaustive(vec![MissingPattern::OpenEnum {
                enum_name: format!("TypeVar({})", type_var.id),
            }]);
        }

        // For exact rows, check if all variants are covered
        let covered_variants: BTreeSet<_> = patterns
            .iter()
            .filter_map(|p| match p {
                Pattern::Variant { variant_name, .. } => Some(variant_name.clone()),
                _ => None,
            })
            .collect();

        let all_variant_names: BTreeSet<_> = variants.keys().cloned().collect();
        let missing_variants: Vec<_> = all_variant_names
            .difference(&covered_variants)
            .cloned()
            .collect();

        if missing_variants.is_empty() {
            ExhaustivenessResult::Exhaustive
        } else {
            ExhaustivenessResult::NonExhaustive(vec![MissingPattern::Variants {
                enum_name: format!("TypeVar({})", type_var.id),
                variant_names: missing_variants,
            }])
        }
    }

    /// Get enum variants from row constraints for a type variable
    fn get_enum_variants_from_rows(&self, _type_var: &TypeVarID) -> HashMap<String, usize> {
        // Look through stored row constraints
        // Note: In a real implementation, we'd need access to the constraint solver's
        // row constraints. For now, we'll use a simplified approach.

        // This is a placeholder - in the actual implementation, we'd need to:
        // 1. Access the ConstraintSolver's row_constraints field
        // 2. Filter for constraints on this type_var
        // 3. Extract EnumCase metadata

        HashMap::new()
    }

    /// Check if a type variable has an exact row constraint
    fn has_exact_row(&self, _type_var: &TypeVarID) -> bool {
        // This is a placeholder - in the actual implementation, we'd need to:
        // 1. Access the ConstraintSolver's row_constraints field
        // 2. Check for HasExactRow constraints on this type_var

        false
    }
}

/// Extension trait to add exhaustiveness checking to Environment
pub trait ExhaustivenessExt {
    /// Check pattern exhaustiveness in the current environment
    fn check_pattern_exhaustiveness(
        &self,
        scrutinee_ty: &Ty,
        patterns: &[Pattern],
    ) -> ExhaustivenessResult;
}

impl ExhaustivenessExt for Environment {
    fn check_pattern_exhaustiveness(
        &self,
        scrutinee_ty: &Ty,
        patterns: &[Pattern],
    ) -> ExhaustivenessResult {
        let checker = ExhaustivenessChecker::new(self);
        checker.check_match(scrutinee_ty, patterns)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name::Name;

    #[test]
    fn test_bool_exhaustiveness() {
        let env = Environment::new();
        let checker = ExhaustivenessChecker::new(&env);

        // Both true and false - exhaustive
        let patterns = vec![Pattern::LiteralTrue, Pattern::LiteralFalse];
        let result = checker.check_match(&Ty::Bool, &patterns);
        assert_eq!(result, ExhaustivenessResult::Exhaustive);

        // Only true - not exhaustive
        let patterns = vec![Pattern::LiteralTrue];
        let result = checker.check_match(&Ty::Bool, &patterns);
        assert!(matches!(result, ExhaustivenessResult::NonExhaustive(_)));

        // Wildcard - exhaustive
        let patterns = vec![Pattern::LiteralTrue, Pattern::Wildcard];
        let result = checker.check_match(&Ty::Bool, &patterns);
        assert_eq!(result, ExhaustivenessResult::Exhaustive);
    }

    #[test]
    fn test_wildcard_always_exhaustive() {
        let env = Environment::new();
        let checker = ExhaustivenessChecker::new(&env);

        let patterns = vec![Pattern::Wildcard];
        let result = checker.check_match(&Ty::Int, &patterns);
        assert_eq!(result, ExhaustivenessResult::Exhaustive);
    }

    #[test]
    fn test_bind_pattern_exhaustive() {
        let env = Environment::new();
        let checker = ExhaustivenessChecker::new(&env);

        let patterns = vec![Pattern::Bind(Name::Raw("x".to_string()))];
        let result = checker.check_match(&Ty::Int, &patterns);
        assert_eq!(result, ExhaustivenessResult::Exhaustive);
    }
}
