//! Integration of exhaustiveness checking with row-based enums

use std::collections::{HashMap, BTreeSet};

use crate::{
    environment::Environment,
    expr_id::ExprID,
    parsed_expr::Pattern,
    row::{FieldMetadata, RowConstraint},
    ty::Ty,
    type_var_id::{TypeVarID, TypeVarKind},
    SymbolID,
};

use super::pattern_exhaustiveness::{ExhaustivenessResult, MissingPattern};

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
    /// Cached row constraints from the environment
    row_constraints: Vec<RowConstraint>,
}

impl<'a> RowEnumAnalyzer<'a> {
    pub fn new(env: &'a Environment) -> Self {
        Self {
            env,
            row_constraints: Vec::new(),
        }
    }
    
    /// Analyze a type to extract enum variant information
    pub fn analyze_type(&self, ty: &Ty) -> Option<RowEnumInfo> {
        match ty {
            Ty::TypeVar(type_var) => self.analyze_type_var(type_var),
            Ty::Enum(enum_id, _) => self.analyze_traditional_enum(enum_id),
            _ => None,
        }
    }
    
    /// Analyze a type variable to see if it represents an enum through row constraints
    fn analyze_type_var(&self, type_var: &TypeVarID) -> Option<RowEnumInfo> {
        let mut variants = HashMap::new();
        let mut is_exact = false;
        
        // In a real implementation, we'd need to access the constraint solver's
        // stored row constraints. For now, we'll simulate this.
        
        
        // Look for HasField constraints with EnumCase metadata
        for constraint in &self.row_constraints {
            match constraint {
                RowConstraint::HasField { type_var: tv, label, metadata: FieldMetadata::EnumCase { tag }, .. } 
                    if tv == type_var => {
                    variants.insert(label.clone(), *tag);
                }
                RowConstraint::HasExactRow { type_var: tv, row } 
                    if tv == type_var => {
                    is_exact = true;
                    // Extract enum variants from the exact row
                    for (label, field_info) in &row.fields {
                        if let FieldMetadata::EnumCase { tag } = &field_info.metadata {
                            variants.insert(label.clone(), *tag);
                        }
                    }
                }
                RowConstraint::HasRow { type_var: tv, row, extension } 
                    if tv == type_var => {
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
        scrutinee_ty: &Ty,
        patterns: &[Pattern],
    ) -> ExhaustivenessResult {
        // First check if there's a wildcard or catch-all variable pattern
        if patterns.iter().any(|p| matches!(p, Pattern::Wildcard | Pattern::Bind(_))) {
            return ExhaustivenessResult::Exhaustive;
        }
        
        // Try to get enum information from the type
        if let Some(enum_info) = self.analyzer.analyze_type(scrutinee_ty) {
            self.check_enum_exhaustiveness(enum_info, patterns)
        } else {
            // For non-enum types, check other cases
            match scrutinee_ty {
                Ty::Bool => self.check_bool_exhaustiveness(patterns),
                // For other types (Int, String, etc.), we can't determine exhaustiveness
                // without a wildcard, but we don't report it as an error - just return
                // that it's exhaustive since we can't enumerate all possible values
                _ => ExhaustivenessResult::Exhaustive,
            }
        }
    }
    
    /// Check exhaustiveness for enums (both traditional and row-based)
    fn check_enum_exhaustiveness(
        &self,
        enum_info: RowEnumInfo,
        patterns: &[Pattern],
    ) -> ExhaustivenessResult {
        // If it's an open enum (not exact), it can't be exhaustive without wildcard
        if !enum_info.is_exact {
            return ExhaustivenessResult::NonExhaustive(vec![
                MissingPattern::OpenEnum {
                    enum_name: format!("TypeVar({})", enum_info.type_var.id),
                }
            ]);
        }
        
        // Collect covered variants
        let covered_variants: BTreeSet<_> = patterns
            .iter()
            .filter_map(|p| match p {
                Pattern::Variant { variant_name, .. } => Some(variant_name.clone()),
                _ => None,
            })
            .collect();
            
        // Find missing variants
        let all_variant_names: BTreeSet<_> = enum_info.variants.keys().cloned().collect();
        let missing_variants: Vec<_> = all_variant_names
            .difference(&covered_variants)
            .cloned()
            .collect();
            
        if missing_variants.is_empty() {
            ExhaustivenessResult::Exhaustive
        } else {
            ExhaustivenessResult::NonExhaustive(vec![
                MissingPattern::Variants {
                    enum_name: format!("Enum"),
                    variant_names: missing_variants,
                }
            ])
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
            let mut missing = vec![];
            if !has_true {
                missing.push("true");
            }
            if !has_false {
                missing.push("false");
            }
            ExhaustivenessResult::NonExhaustive(vec![
                MissingPattern::Variants {
                    enum_name: "Bool".to_string(),
                    variant_names: missing.into_iter().map(|s| s.to_string()).collect(),
                }
            ])
        }
    }
}

/// Function to check exhaustiveness during type checking
pub fn check_match_exhaustiveness(
    env: &Environment,
    scrutinee_ty: &Ty,
    patterns: &[Pattern],
) -> Result<(), String> {
    
    let checker = RowAwareExhaustivenessChecker::new(env);
    
    match checker.check_match(scrutinee_ty, patterns) {
        ExhaustivenessResult::Exhaustive => Ok(()),
        ExhaustivenessResult::NonExhaustive(missing) => {
            let mut msg = "Pattern match is not exhaustive. Missing patterns:".to_string();
            for pattern in missing {
                match pattern {
                    MissingPattern::Variant { variant_name, .. } => {
                        msg.push_str(&format!("\n  - {}", variant_name));
                    }
                    MissingPattern::Variants { variant_names, .. } => {
                        for name in variant_names {
                            msg.push_str(&format!("\n  - {}", name));
                        }
                    }
                    MissingPattern::OpenEnum { enum_name } => {
                        msg.push_str(&format!("\n  - {} is an open enum and requires a wildcard pattern", enum_name));
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
    use crate::{
        expr_id::ExprID,
        type_var_id::TypeVarKind,
    };
    
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
        let result = checker.check_match(&Ty::Bool, &patterns);
        
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