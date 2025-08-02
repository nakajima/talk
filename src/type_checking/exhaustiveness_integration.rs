//! Integration of exhaustiveness checking with row-based enums

use std::collections::HashMap;

use crate::{
    SymbolID,
    environment::Environment,
    expr_id::ExprID,
    row::{FieldMetadata, RowConstraint},
    ty::{RowKind, Ty2},
    type_var_id::{TypeVarID, TypeVarKind},
    typed_expr::{self, Pattern},
};

use super::{
    pattern_exhaustiveness::{ExhaustivenessResult, MissingPattern},
    pattern_matrix::{
        Constructor, PatternMatrix, all_constructors, constructors_match,
        format_constructor_witness, is_exhaustive,
    },
};

/// Information about enum variants gathered from row constraints
#[derive(Debug, Clone)]
pub struct RowEnumInfo {
    /// Map from variant name to tag number
    pub variants: HashMap<String, usize>,
    /// Whether this is an exact row (closed enum)
    pub is_exact: bool,
    /// The type variable this enum is based on
    pub type_var: TypeVarID,
}

/// Helper to extract enum information from row constraints
pub struct RowEnumAnalyzer<'a> {
    env: &'a Environment,
}

impl<'a> RowEnumAnalyzer<'a> {
    pub fn new(env: &'a Environment) -> Self {
        Self { env }
    }

    /// Analyze a type to extract enum variant information
    pub fn analyze_type(&self, ty: &Ty2) -> Option<RowEnumInfo> {
        match ty {
            Ty2::TypeVar(type_var) => self.analyze_type_var(type_var),
            Ty2::Row {
                nominal_id: Some(enum_id),
                kind: RowKind::Enum,
                ..
            } => self.analyze_traditional_enum(enum_id),
            _ => None,
        }
    }

    /// Analyze a type variable to see if it represents an enum through row constraints
    fn analyze_type_var(&self, type_var: &TypeVarID) -> Option<RowEnumInfo> {
        tracing::debug!("Analyzing type var: {:?}", type_var);
        tracing::debug!("Total row constraints: {}", self.env.row_constraints.len());

        let mut variants = HashMap::new();
        let mut is_exact = false;

        // Look for HasField constraints with EnumCase metadata in the environment
        for constraint in &self.env.row_constraints {
            match constraint {
                RowConstraint::HasField {
                    type_var: tv,
                    label,
                    metadata: FieldMetadata::EnumCase { tag },
                    ..
                } if tv == type_var => {
                    tracing::debug!("Found enum variant {} with tag {} for {:?}", label, tag, tv);
                    variants.insert(label.clone(), *tag);
                }
                RowConstraint::HasExactRow { type_var: tv, row } if tv == type_var => {
                    is_exact = true;
                    // Extract enum variants from the exact row
                    for (label, field_info) in &row.fields {
                        if let FieldMetadata::EnumCase { tag } = &field_info.metadata {
                            variants.insert(label.clone(), *tag);
                        }
                    }
                }
                RowConstraint::HasRow {
                    type_var: tv,
                    row,
                    extension,
                } if tv == type_var => {
                    // If there's an extension, it's not exact
                    is_exact = extension.is_none();
                    // Extract enum variants from the row
                    for (label, field_info) in &row.fields {
                        if let FieldMetadata::EnumCase { tag } = &field_info.metadata {
                            variants.insert(label.clone(), *tag);
                        }
                    }
                }
                _ => {}
            }
        }

        if variants.is_empty() {
            None
        } else {
            Some(RowEnumInfo {
                variants,
                is_exact,
                type_var: type_var.clone(),
            })
        }
    }

    /// Analyze a traditional enum type
    fn analyze_traditional_enum(&self, enum_id: &SymbolID) -> Option<RowEnumInfo> {
        let enum_def = self.env.lookup_enum(enum_id)?;

        let variants = enum_def
            .variants()
            .iter()
            .map(|v| (v.name.clone(), v.tag))
            .collect();

        Some(RowEnumInfo {
            variants,
            is_exact: true, // Traditional enums are always closed
            type_var: TypeVarID::new(0, TypeVarKind::Let, ExprID(0)), // Dummy type var for traditional enums
        })
    }
}

/// Enhanced exhaustiveness checker that understands row-based enums
pub struct RowAwareExhaustivenessChecker<'a> {
    analyzer: RowEnumAnalyzer<'a>,
}

impl<'a> RowAwareExhaustivenessChecker<'a> {
    pub fn new(env: &'a Environment) -> Self {
        Self {
            analyzer: RowEnumAnalyzer::new(env),
        }
    }

    /// Check if a match expression is exhaustive
    pub fn check_match(
        &self,
        scrutinee_ty: &Ty2,
        patterns: &[typed_expr::Pattern],
    ) -> ExhaustivenessResult {
        // Special handling for boolean types to match expected format
        if matches!(scrutinee_ty, Ty2::Bool) {
            return self.check_bool_exhaustiveness(patterns);
        }

        // Create a pattern matrix from the patterns
        let matrix = PatternMatrix::new(patterns.to_vec());

        // Check if the matrix is exhaustive
        if is_exhaustive(&matrix, scrutinee_ty, self.analyzer.env) {
            ExhaustivenessResult::Exhaustive
        } else {
            // Generate witnesses for missing patterns
            let all_missing = self.collect_missing_patterns(&matrix, scrutinee_ty);

            if !all_missing.is_empty() {
                // For enums, return Variants with all missing variant names
                if let Ty2::Row {
                    kind: RowKind::Enum,
                    nominal_id: Some(id),
                    ..
                } = scrutinee_ty
                    && let Some(enum_def) = self.analyzer.env.lookup_enum(id)
                {
                    return ExhaustivenessResult::NonExhaustive(vec![MissingPattern::Variants {
                        enum_name: enum_def.name_str.clone(),
                        variant_names: all_missing,
                    }]);
                }

                // For other types, return individual missing patterns
                ExhaustivenessResult::NonExhaustive(
                    all_missing
                        .into_iter()
                        .map(|witness| MissingPattern::Variant {
                            enum_name: format!("{scrutinee_ty:?}"),
                            variant_name: witness,
                        })
                        .collect(),
                )
            } else {
                // Fallback for cases where we can't generate a witness
                ExhaustivenessResult::NonExhaustive(vec![MissingPattern::Variant {
                    enum_name: "pattern".to_string(),
                    variant_name: "_".to_string(),
                }])
            }
        }
    }

    /// Collect all missing patterns
    fn collect_missing_patterns(&self, matrix: &PatternMatrix, ty: &Ty2) -> Vec<String> {
        let mut missing = Vec::new();

        // Get all constructors that need to be covered
        let all_ctors = all_constructors(ty, self.analyzer.env);
        let covered_ctors = matrix.column_constructors(self.analyzer.env, ty);

        for ctor in &all_ctors {
            if !covered_ctors.iter().any(|c| constructors_match(c, ctor))
                && let Some(witness) = format_constructor_witness(ctor)
            {
                missing.push(witness);
            }
        }

        // If we can't enumerate constructors and there's no wildcard, we need one
        if all_ctors.is_empty() && !covered_ctors.contains(&Constructor::Wildcard) {
            missing.push("_".to_string());
        }

        missing
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
            let mut missing = vec![];
            if !has_true {
                missing.push("true");
            }
            if !has_false {
                missing.push("false");
            }
            ExhaustivenessResult::NonExhaustive(vec![MissingPattern::Variants {
                enum_name: "Bool".to_string(),
                variant_names: missing.into_iter().map(|s| s.to_string()).collect(),
            }])
        }
    }
}

/// Function to check exhaustiveness during type checking
pub fn check_match_exhaustiveness(
    env: &Environment,
    scrutinee_ty: &Ty2,
    patterns: &[typed_expr::Pattern],
) -> Result<(), String> {
    let checker = RowAwareExhaustivenessChecker::new(env);

    match checker.check_match(scrutinee_ty, patterns) {
        ExhaustivenessResult::Exhaustive => Ok(()),
        ExhaustivenessResult::NonExhaustive(missing) => {
            let mut msg = "Pattern match is not exhaustive. Missing patterns:".to_string();
            for pattern in missing {
                match pattern {
                    MissingPattern::Variant { variant_name, .. } => {
                        msg.push_str(&format!("\n  - {variant_name}"));
                    }
                    MissingPattern::Variants { variant_names, .. } => {
                        for name in variant_names {
                            msg.push_str(&format!("\n  - {name}"));
                        }
                    }
                    MissingPattern::OpenEnum { enum_name } => {
                        msg.push_str(&format!(
                            "\n  - {enum_name} is an open enum and requires a wildcard pattern"
                        ));
                    }
                }
            }
            Err(msg)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{expr_id::ExprID, type_var_id::TypeVarKind};

    #[test]
    fn test_row_enum_analyzer() {
        let env = Environment::new();
        let analyzer = RowEnumAnalyzer::new(&env);

        // Test with a type variable (would need row constraints in real scenario)
        let type_var = TypeVarID::new(1, TypeVarKind::Let, ExprID(1));
        let result = analyzer.analyze_type_var(&type_var);
        assert!(result.is_none()); // No constraints, so no enum info
    }

    #[test]
    fn test_bool_exhaustiveness_detailed() {
        let env = Environment::new();
        let checker = RowAwareExhaustivenessChecker::new(&env);

        // Missing false
        let patterns = vec![Pattern::LiteralTrue];
        let result = checker.check_match(&Ty2::Bool, &patterns);

        match result {
            ExhaustivenessResult::NonExhaustive(missing) => {
                assert_eq!(missing.len(), 1);
                match &missing[0] {
                    MissingPattern::Variants { variant_names, .. } => {
                        assert!(variant_names.contains(&"false".to_string()));
                    }
                    _ => panic!("Expected Variants pattern"),
                }
            }
            _ => panic!("Expected non-exhaustive result"),
        }
    }
}
