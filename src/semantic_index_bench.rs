use crate::diagnostic::Position;
use crate::expr_id::ExprID;
use crate::lexing::span::Span;
use crate::semantic_index::SemanticIndex;
use std::path::PathBuf;
use std::time::Instant;

/// Simple benchmark to compare linear scan vs spatial index
pub fn benchmark_find_expr_at_position() {
    println!("\n=== Semantic Index Performance Benchmark ===\n");

    let mut index = SemanticIndex::new();
    let test_file = PathBuf::from("test.tlk");

    // Generate test data: 10,000 expressions with spans
    println!("Generating test data: 10,000 expressions...");
    for i in 0..10_000 {
        let line = i / 100; // 100 expressions per line
        let col = (i % 100) * 10; // Each expression is ~10 chars wide

        let span = Span {
            start: i * 10,
            end: (i + 1) * 10,
            start_line: line,
            start_col: col,
            end_line: line,
            end_col: col + 8,
            path: test_file.clone(),
        };

        index.record_expr_span(ExprID(i as i32), span);
    }

    // Test positions
    let test_positions = vec![
        Position { line: 5, col: 50 },   // Early in file
        Position { line: 50, col: 250 }, // Middle of file
        Position { line: 95, col: 450 }, // Late in file
    ];

    println!("\nRunning lookups...");

    // Warm up
    for _ in 0..100 {
        for pos in &test_positions {
            let _ = index.find_expr_at_position(pos, &test_file);
        }
    }

    // Benchmark spatial index
    let start = Instant::now();
    let iterations = 10_000;

    for _ in 0..iterations {
        for pos in &test_positions {
            let _ = index.find_expr_at_position(pos, &test_file);
        }
    }

    let spatial_duration = start.elapsed();
    let total_lookups = iterations * test_positions.len() as u32;
    let spatial_per_lookup = spatial_duration / total_lookups;

    println!("\nResults:");
    println!("  Spatial index: {:?} per lookup", spatial_per_lookup);
    println!(
        "  Total time for {} lookups: {:?}",
        total_lookups, spatial_duration
    );

    // Calculate theoretical improvement
    // Linear scan: O(n) = 10,000 comparisons worst case
    // Spatial index: O(log n) for line lookup + O(m) for spans on that line
    // Where m is typically much smaller than n (e.g., 100 vs 10,000)
    let theoretical_speedup = 10_000.0 / (100.0 + (10_000.0_f64).log2());
    println!("\n  Theoretical speedup: ~{:.1}x", theoretical_speedup);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spatial_index_correctness() {
        let mut index = SemanticIndex::new();
        let test_file = PathBuf::from("test.tlk");

        // Add some overlapping spans
        index.record_expr_span(
            ExprID(1),
            Span {
                start: 0,
                end: 100,
                start_line: 0,
                start_col: 0,
                end_line: 2,
                end_col: 20,
                path: test_file.clone(),
            },
        );

        index.record_expr_span(
            ExprID(2),
            Span {
                start: 10,
                end: 50,
                start_line: 0,
                start_col: 10,
                end_line: 1,
                end_col: 10,
                path: test_file.clone(),
            },
        );

        index.record_expr_span(
            ExprID(3),
            Span {
                start: 20,
                end: 30,
                start_line: 0,
                start_col: 20,
                end_line: 0,
                end_col: 30,
                path: test_file.clone(),
            },
        );

        // Test that we get the smallest span
        let result = index.find_expr_at_position(&Position { line: 0, col: 25 }, &test_file);
        assert_eq!(result, Some(ExprID(3))); // Should return the smallest span

        // Test position outside any span
        let result = index.find_expr_at_position(&Position { line: 5, col: 0 }, &test_file);
        assert_eq!(result, None);
    }
}
