#!/usr/bin/env python3
import os
import re

# List of test files to consolidate in order
test_files = [
    "test_exact_row_semantics.rs",
    "test_extension_explicit.rs", 
    "test_integration_rows.rs",
    "test_qualified_rows.rs",
    "test_type_def_rows.rs",
    "test_hoisting_rows.rs",
    "test_single_source_rows.rs",
    "test_row_associated_types.rs",
    "test_row_polymorphism.rs",
    "test_row_pattern_matching.rs",
    "test_row_pattern_matching_integration.rs",
    "test_row_member_resolution.rs",
    "test_row_associated_types_integration.rs",
    "test_row_polymorphism_integration.rs",
    "test_row_extensions.rs",
    "test_row_constraint_persistence.rs",
    "test_row_typedef_integration.rs",
    "test_row_system_integration.rs",
    "test_row_composition.rs",
    "test_row_protocol_conformance.rs",
    "test_row_enum_variants.rs",
    "test_row_populate_robust.rs",
    "test_row_populate_real_world.rs",
    "test_row_populate_edge_case.rs",
    "example_row_usage.rs"
]

def extract_tests_from_file(filepath):
    """Extract test functions and helper functions from a test file"""
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Find the tests module
    mod_match = re.search(r'#\[cfg\(test\)\]\s*mod\s+\w+\s*\{(.*)\}', content, re.DOTALL)
    if not mod_match:
        return [], []
    
    mod_content = mod_match.group(1)
    
    # Extract imports (combine unique imports)
    imports = []
    import_pattern = r'use\s+[^;]+;'
    for match in re.finditer(import_pattern, mod_content):
        imports.append(match.group(0))
    
    # Extract test functions (including #[test] and #[ignore])
    tests = []
    test_pattern = r'((?:\s*///[^\n]*\n)*\s*(?:#\[test\]|#\[ignore\])\s*(?:#\[test\])?\s*(?:pub\s+)?(?:async\s+)?fn\s+\w+[^{]*\{(?:[^{}]*\{[^{}]*\})*[^{}]*\})'
    
    for match in re.finditer(test_pattern, mod_content):
        test_func = match.group(1).strip()
        tests.append(test_func)
    
    # Extract helper functions (non-test functions)
    helper_pattern = r'((?:\s*///[^\n]*\n)*\s*(?:pub\s+)?(?:async\s+)?fn\s+\w+[^{]*\{(?:[^{}]*\{[^{}]*\})*[^{}]*\})'
    helpers = []
    
    for match in re.finditer(helper_pattern, mod_content):
        func = match.group(1).strip()
        # Skip if it's a test function
        if '#[test]' not in func and '#[ignore]' not in func:
            helpers.append(func)
    
    # Extract struct/enum definitions
    struct_pattern = r'((?:pub\s+)?(?:struct|enum)\s+\w+[^;{]*(?:\{[^}]*\}|;))'
    for match in re.finditer(struct_pattern, mod_content):
        helpers.append(match.group(1).strip())
    
    return tests, helpers, imports

# Process all files
all_tests = []
all_helpers = []
all_imports = set()

for test_file in test_files:
    if os.path.exists(test_file):
        print(f"Processing {test_file}...")
        tests, helpers, imports = extract_tests_from_file(test_file)
        
        # Add section comment
        section_comment = f"\n    // ===== From {test_file} ({len(tests)} tests) =====\n"
        all_tests.append(section_comment)
        
        # Add helpers first (if any)
        if helpers:
            all_tests.extend([f"    {helper}" for helper in helpers])
            all_tests.append("")  # Empty line
        
        # Add tests
        for test in tests:
            all_tests.append(f"    {test}")
            all_tests.append("")  # Empty line between tests
        
        # Collect unique imports
        for imp in imports:
            all_imports.add(imp.strip())

# Write consolidated file
print("\nWriting consolidated test file...")
with open('test_row_system_all_generated.rs', 'w') as f:
    # Write header
    f.write('''//! Comprehensive test suite for the row-based type system
//! 
//! This file consolidates all tests from the following 25 test files:
//! - test_exact_row_semantics.rs (3 tests)
//! - test_extension_explicit.rs (2 tests)
//! - test_integration_rows.rs (3 tests)
//! - test_qualified_rows.rs (2 tests)
//! - test_type_def_rows.rs (3 tests)
//! - test_hoisting_rows.rs (2 tests)
//! - test_single_source_rows.rs (2 tests)
//! - test_row_associated_types.rs (5 tests)
//! - test_row_polymorphism.rs (5 tests)
//! - test_row_pattern_matching.rs (5 tests)
//! - test_row_pattern_matching_integration.rs (8 tests)
//! - test_row_member_resolution.rs (3 tests)
//! - test_row_associated_types_integration.rs (5 tests)
//! - test_row_polymorphism_integration.rs (6 tests)
//! - test_row_extensions.rs (4 tests)
//! - test_row_constraint_persistence.rs (4 tests)
//! - test_row_typedef_integration.rs (2 tests)
//! - test_row_system_integration.rs (2 tests)
//! - test_row_composition.rs (3 tests)
//! - test_row_protocol_conformance.rs (2 tests)
//! - test_row_enum_variants.rs (3 tests)
//! - test_row_populate_robust.rs (2 tests)
//! - test_row_populate_real_world.rs (1 test)
//! - test_row_populate_edge_case.rs (2 tests)
//! - example_row_usage.rs (2 tests)
//! 
//! Total: 81 test functions
//! 
//! Note: test_row_system_consolidated.rs is excluded as it was a preliminary consolidation

#[cfg(test)]
mod tests {
''')
    
    # Write combined imports
    for imp in sorted(all_imports):
        if imp.strip():
            f.write(f"    {imp}\n")
    
    # Write test content
    f.write('\n'.join(all_tests))
    
    # Close module
    f.write('\n}')

print("Done! Created test_row_system_all_generated.rs")