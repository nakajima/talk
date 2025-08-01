//! Pattern exhaustiveness checking using pattern matrices
//!
//! Based on the algorithm described in "Warnings for pattern matching" by Luc Maranget (2007)
//! and used by Rust's exhaustiveness checker.

use std::collections::{HashMap, HashSet};

use crate::{
    SymbolID,
    environment::Environment,
    ty::{RowKind, Ty},
    typed_expr::Pattern,
};

/// A constructor in a pattern - represents the "head" of a pattern
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constructor {
    /// Integer literal
    Int(i64),
    /// Float literal  
    Float(String), // String to avoid float comparison issues
    /// Boolean literal
    Bool(bool),
    /// Enum variant
    Variant {
        enum_id: SymbolID,
        variant_name: String,
        arity: usize,
    },
    /// Struct constructor
    Struct {
        struct_id: Option<SymbolID>,
        fields: Vec<String>,
    },
    /// Wildcard - matches anything
    Wildcard,
}

/// A pattern represented as a constructor and its sub-patterns
#[derive(Debug, Clone)]
pub struct DeconstructedPat {
    pub ctor: Constructor,
    pub fields: Vec<PatternColumn>,
}

/// A column of patterns in the pattern matrix
#[derive(Debug, Clone)]
pub enum PatternColumn {
    Pattern(Pattern),
    /// A synthetic pattern used during specialization
    Synthetic(Box<DeconstructedPat>),
}

impl PatternColumn {
    fn to_deconstructed(&self, env: &Environment, ty: &Ty) -> DeconstructedPat {
        match self {
            PatternColumn::Pattern(p) => deconstruct_pattern(p, env, ty),
            PatternColumn::Synthetic(d) => (**d).clone(),
        }
    }
}

/// A matrix of patterns where each row represents a pattern and columns represent sub-patterns
#[derive(Debug)]
pub struct PatternMatrix {
    rows: Vec<Vec<PatternColumn>>,
}

impl PatternMatrix {
    pub fn new(patterns: Vec<Pattern>) -> Self {
        let rows = patterns
            .into_iter()
            .map(|p| vec![PatternColumn::Pattern(p)])
            .collect();
        PatternMatrix { rows }
    }

    /// Check if the matrix is empty (no patterns)
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Get the first column of patterns
    pub fn first_column(&self) -> Vec<&PatternColumn> {
        self.rows.iter().filter_map(|row| row.first()).collect()
    }

    /// Specialize the matrix with respect to a constructor
    /// This filters rows that match the constructor and expands their sub-patterns
    pub fn specialize(
        &self,
        ctor: &Constructor,
        arity: usize,
        env: &Environment,
        ty: &Ty,
    ) -> PatternMatrix {
        let mut new_rows = Vec::new();

        for row in &self.rows {
            if let Some(first) = row.first() {
                let deconstructed = first.to_deconstructed(env, ty);

                if constructors_match(&deconstructed.ctor, ctor) {
                    // This row matches - expand it
                    let mut new_row = deconstructed.fields;
                    new_row.extend_from_slice(&row[1..]);
                    new_rows.push(new_row);
                } else if matches!(deconstructed.ctor, Constructor::Wildcard) {
                    // Wildcard matches everything - create synthetic patterns
                    let mut new_row = vec![PatternColumn::Pattern(Pattern::Wildcard); arity];
                    new_row.extend_from_slice(&row[1..]);
                    new_rows.push(new_row);
                }
            }
        }

        PatternMatrix { rows: new_rows }
    }

    /// Get all constructors that appear in the first column
    pub fn column_constructors(&self, env: &Environment, ty: &Ty) -> HashSet<Constructor> {
        self.first_column()
            .into_iter()
            .map(|p| p.to_deconstructed(env, ty).ctor)
            .collect()
    }
}

/// Check if two constructors match (considering wildcards)
pub fn constructors_match(ctor1: &Constructor, ctor2: &Constructor) -> bool {
    match (ctor1, ctor2) {
        (Constructor::Wildcard, _) | (_, Constructor::Wildcard) => true,
        (Constructor::Int(a), Constructor::Int(b)) => a == b,
        (Constructor::Float(a), Constructor::Float(b)) => a == b,
        (Constructor::Bool(a), Constructor::Bool(b)) => a == b,
        (
            Constructor::Variant {
                variant_name: a, ..
            },
            Constructor::Variant {
                variant_name: b, ..
            },
        ) => a == b,
        (Constructor::Struct { fields: a, .. }, Constructor::Struct { fields: b, .. }) => a == b,
        _ => false,
    }
}

/// Deconstruct a pattern into a constructor and its fields
fn deconstruct_pattern(pattern: &Pattern, _env: &Environment, ty: &Ty) -> DeconstructedPat {
    match pattern {
        Pattern::LiteralInt(s) => {
            let val = s.parse::<i64>().unwrap_or(0);
            DeconstructedPat {
                ctor: Constructor::Int(val),
                fields: vec![],
            }
        }
        Pattern::LiteralFloat(s) => DeconstructedPat {
            ctor: Constructor::Float(s.clone()),
            fields: vec![],
        },
        Pattern::LiteralTrue => DeconstructedPat {
            ctor: Constructor::Bool(true),
            fields: vec![],
        },
        Pattern::LiteralFalse => DeconstructedPat {
            ctor: Constructor::Bool(false),
            fields: vec![],
        },
        Pattern::Wildcard | Pattern::Bind(_) => DeconstructedPat {
            ctor: Constructor::Wildcard,
            fields: vec![],
        },
        Pattern::Variant {
            variant_name,
            fields,
            ..
        } => {
            // Look up enum info from type
            let (enum_id, arity) = match ty {
                Ty::Row {
                    kind: RowKind::Enum(id, _),
                    ..
                } => (*id, fields.len()),
                _ => (SymbolID(0), fields.len()), // Fallback
            };

            DeconstructedPat {
                ctor: Constructor::Variant {
                    enum_id,
                    variant_name: variant_name.clone(),
                    arity,
                },
                fields: fields
                    .iter()
                    .map(|f| {
                        // Extract pattern from ParsedExpr
                        match &f.expr {
                            crate::typed_expr::Expr::ParsedPattern(p) => {
                                PatternColumn::Pattern(p.clone())
                            }
                            _ => PatternColumn::Pattern(Pattern::Wildcard),
                        }
                    })
                    .collect(),
            }
        }
        Pattern::Struct {
            field_names,
            fields,
            ..
        } => {
            let field_map: HashMap<_, _> = field_names
                .iter()
                .zip(fields.iter())
                .map(|(name, field)| {
                    let pattern = match &field.expr {
                        crate::typed_expr::Expr::ParsedPattern(p) => p.clone(),
                        _ => Pattern::Wildcard,
                    };
                    (name.name_str(), pattern)
                })
                .collect();

            // Get all field names from the type
            let all_fields = match ty {
                Ty::Row { fields, .. } => fields
                    .iter()
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>(),
                _ => field_names.iter().map(|n| n.name_str()).collect(),
            };

            // Create pattern columns for all fields (wildcard for missing ones)
            let field_patterns = all_fields
                .iter()
                .map(|name| field_map.get(name).cloned().unwrap_or(Pattern::Wildcard))
                .map(PatternColumn::Pattern)
                .collect();

            DeconstructedPat {
                ctor: Constructor::Struct {
                    struct_id: match ty {
                        Ty::Row {
                            kind:
                                RowKind::Enum(id, _) | RowKind::Struct(id, _) | RowKind::Protocol(id, _),
                            ..
                        } => Some(*id),
                        _ => None,
                    },
                    fields: all_fields,
                },
                fields: field_patterns,
            }
        }
    }
}

/// Get all possible constructors for a type
pub fn all_constructors(ty: &Ty, env: &Environment) -> Vec<Constructor> {
    match ty {
        Ty::Bool => vec![Constructor::Bool(true), Constructor::Bool(false)],
        Ty::Row {
            kind: RowKind::Enum(id, _),
            ..
        } => {
            // Get enum variants from environment
            if let Some(enum_def) = env.lookup_enum(id) {
                enum_def
                    .variants()
                    .iter()
                    .map(|v| Constructor::Variant {
                        enum_id: *id,
                        variant_name: v.name.clone(),
                        arity: if matches!(v.ty, Ty::Void) { 0 } else { 1 },
                    })
                    .collect()
            } else {
                vec![Constructor::Wildcard]
            }
        }
        Ty::Row {
            fields,
            kind: RowKind::Record,
            ..
        } => {
            // For structs, there's only one constructor
            vec![Constructor::Struct {
                struct_id: None,
                fields: fields.iter().map(|(name, _)| name.clone()).collect(),
            }]
        }
        Ty::Row {
            fields,
            kind: RowKind::Struct(struct_id, _),
            ..
        } => {
            // For structs, there's only one constructor
            vec![Constructor::Struct {
                struct_id: Some(*struct_id),
                fields: fields.iter().map(|(name, _)| name.clone()).collect(),
            }]
        }
        _ => {
            // For types with infinite constructors (Int, String, etc.),
            // we can't enumerate them all
            vec![]
        }
    }
}

/// Check if a pattern matrix is exhaustive
pub fn is_exhaustive(matrix: &PatternMatrix, ty: &Ty, env: &Environment) -> bool {
    is_exhaustive_with_types(matrix, &[ty], env)
}

/// Check if a pattern matrix is exhaustive with multiple column types
fn is_exhaustive_with_types(
    matrix: &PatternMatrix,
    column_types: &[&Ty],
    env: &Environment,
) -> bool {
    // Base case: empty matrix means nothing is covered
    if matrix.is_empty() {
        return false;
    }

    // Base case: no columns left means we've matched everything
    if column_types.is_empty() || matrix.rows.iter().all(|row| row.is_empty()) {
        return true;
    }

    let first_ty = column_types[0];

    // If any pattern starts with wildcard or bind, we need to check the rest
    let has_wildcard = matrix.first_column().iter().any(|p| {
        let deconstructed = p.to_deconstructed(env, first_ty);
        matches!(deconstructed.ctor, Constructor::Wildcard)
    });

    if has_wildcard {
        // Create a matrix with the remaining columns for wildcard rows
        let mut remaining_matrix_rows = Vec::new();
        for row in &matrix.rows {
            if let Some(first) = row.first() {
                let deconstructed = first.to_deconstructed(env, first_ty);
                if matches!(deconstructed.ctor, Constructor::Wildcard) {
                    remaining_matrix_rows.push(row[1..].to_vec());
                }
            }
        }
        let remaining_matrix = PatternMatrix {
            rows: remaining_matrix_rows,
        };
        return is_exhaustive_with_types(&remaining_matrix, &column_types[1..], env);
    }

    // Get all constructors that need to be covered
    let all_ctors = all_constructors(first_ty, env);

    // If we can't enumerate all constructors (e.g., integers),
    // we need a wildcard to be exhaustive
    if all_ctors.is_empty() {
        return false;
    }

    // Get constructors that appear in the patterns
    let covered_ctors = matrix.column_constructors(env, first_ty);

    // Check if all constructors are covered
    for ctor in &all_ctors {
        // Check if this constructor is covered
        let is_covered = covered_ctors.iter().any(|c| constructors_match(c, ctor));

        if !is_covered {
            return false;
        }

        // For covered constructors, check that the specialized matrix is exhaustive
        let arity = constructor_arity(ctor);
        let specialized = matrix.specialize(ctor, arity, env, first_ty);

        // Construct types for the subpatterns - collect into owned values first
        let mut sub_types_owned: Vec<Ty> = vec![];
        match ctor {
            Constructor::Variant {
                enum_id,
                variant_name,
                ..
            } => {
                // Look up variant payload type
                if let Some(enum_def) = env.lookup_enum(enum_id) {
                    let variants = enum_def.variants();
                    if let Some(variant) = variants.iter().find(|v| &v.name == variant_name)
                        && !matches!(variant.ty, Ty::Void)
                    {
                        sub_types_owned.push(variant.ty.clone());
                    }
                }
            }
            Constructor::Struct { struct_id, fields } => {
                // Look up struct field types
                if let Some(struct_id) = struct_id
                    && let Some(struct_def) = env.lookup_struct(struct_id)
                {
                    for field_name in fields {
                        if let Some(member) = struct_def.members.get(field_name) {
                            sub_types_owned.push(member.ty().clone());
                        }
                    }
                }
            }
            _ => {} // No sub-patterns for literals
        }

        // Convert to references and add remaining column types
        let mut sub_types: Vec<&Ty> = sub_types_owned.iter().collect();
        sub_types.extend_from_slice(&column_types[1..]);

        // Recursively check exhaustiveness
        if !is_exhaustive_with_types(&specialized, &sub_types, env) {
            return false;
        }
    }

    true
}

/// Get the arity (number of fields) of a constructor
fn constructor_arity(ctor: &Constructor) -> usize {
    match ctor {
        Constructor::Int(_)
        | Constructor::Float(_)
        | Constructor::Bool(_)
        | Constructor::Wildcard => 0,
        Constructor::Variant { arity, .. } => *arity,
        Constructor::Struct { fields, .. } => fields.len(),
    }
}

/// Generate a witness (counter-example) for non-exhaustive matches
pub fn generate_witness(matrix: &PatternMatrix, ty: &Ty, env: &Environment) -> Option<String> {
    if is_exhaustive(matrix, ty, env) {
        return None;
    }

    // Find a constructor that isn't covered
    let all_ctors = all_constructors(ty, env);
    let covered_ctors = matrix.column_constructors(env, ty);

    for ctor in &all_ctors {
        if !covered_ctors.contains(ctor) {
            return format_constructor_witness(ctor);
        }
    }

    // If we can't enumerate constructors, suggest wildcard
    if all_ctors.is_empty() && !covered_ctors.contains(&Constructor::Wildcard) {
        return Some("_".to_string());
    }

    None
}

/// Format a constructor as a pattern for error messages
pub fn format_constructor_witness(ctor: &Constructor) -> Option<String> {
    Some(match ctor {
        Constructor::Int(n) => n.to_string(),
        Constructor::Float(s) => s.clone(),
        Constructor::Bool(true) => "true".to_string(),
        Constructor::Bool(false) => "false".to_string(),
        Constructor::Variant {
            variant_name,
            arity,
            ..
        } => {
            if *arity == 0 {
                format!(".{variant_name}")
            } else {
                let fields = vec!["_"; *arity].join(", ");
                format!(".{variant_name}({fields})")
            }
        }
        Constructor::Struct { fields, .. } => {
            let field_patterns = fields
                .iter()
                .map(|f| format!("{f}: _"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{ {field_patterns} }}")
        }
        Constructor::Wildcard => "_".to_string(),
    })
}
