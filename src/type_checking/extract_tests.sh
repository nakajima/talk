#!/bin/bash

# List of files to process
files=(
    "test_exact_row_semantics.rs"
    "test_extension_explicit.rs"
    "test_integration_rows.rs"
    "test_qualified_rows.rs"
    "test_type_def_rows.rs"
    "test_hoisting_rows.rs"
    "test_single_source_rows.rs"
    "test_row_associated_types.rs"
    "test_row_polymorphism.rs"
    "test_row_pattern_matching.rs"
    "test_row_pattern_matching_integration.rs"
    "test_row_member_resolution.rs"
    "test_row_associated_types_integration.rs"
    "test_row_polymorphism_integration.rs"
    "test_row_extensions.rs"
    "test_row_constraint_persistence.rs"
    "test_row_typedef_integration.rs"
    "test_row_system_integration.rs"
    "test_row_composition.rs"
    "test_row_protocol_conformance.rs"
    "test_row_enum_variants.rs"
    "test_row_populate_robust.rs"
    "test_row_populate_real_world.rs"
    "test_row_populate_edge_case.rs"
    "example_row_usage.rs"
)

total_count=0

for file in "${files[@]}"; do
    if [ -f "$file" ]; then
        # Count test functions (including #[ignore] tests)
        count=$(grep -E '^\s*(#\[test\]|#\[ignore\])' "$file" | wc -l)
        echo "$file: $count tests"
        total_count=$((total_count + count))
    fi
done

echo "Total: $total_count tests"