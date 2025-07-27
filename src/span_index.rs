use crate::diagnostic::Position;
use crate::expr_id::ExprID;
use crate::lexing::span::Span;
use std::collections::HashMap;
use std::path::PathBuf;

/// A line-based index for efficient span lookups
///
/// This structure indexes spans by file and line number for fast lookups.
/// For each file, we maintain a sorted list of spans per line.
#[derive(Debug, Default, Clone)]
pub struct SpanIndex {
    /// Maps file path -> line number -> list of (ExprID, Span) sorted by start column
    by_file_and_line: HashMap<PathBuf, HashMap<u32, Vec<(ExprID, Span)>>>,
}

impl SpanIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a span into the index
    pub fn insert(&mut self, expr_id: ExprID, span: Span) {
        let file_index = self
            .by_file_and_line
            .entry(span.path.clone())
            .or_default();

        // Index by all lines the span covers
        for line in span.start_line..=span.end_line {
            let line_spans = file_index.entry(line).or_default();
            line_spans.push((expr_id, span.clone()));
        }
    }

    /// Build the index from a collection of spans, sorting for efficient lookup
    pub fn build_from(spans: &HashMap<ExprID, Span>) -> Self {
        let mut index = Self::new();

        for (expr_id, span) in spans {
            index.insert(*expr_id, span.clone());
        }

        // Sort all line entries by start column for binary search
        for file_index in index.by_file_and_line.values_mut() {
            for line_spans in file_index.values_mut() {
                line_spans.sort_by_key(|(_, span)| (span.start_col, span.start));
            }
        }

        index
    }

    /// Find the smallest span containing the given position
    pub fn find_at_position(&self, position: &Position, path: &PathBuf) -> Option<ExprID> {
        let file_index = self.by_file_and_line.get(path)?;
        let line_spans = file_index.get(&position.line)?;

        // Find all spans that contain the position
        let mut candidates: Vec<&(ExprID, Span)> = line_spans
            .iter()
            .filter(|(_, span)| span.contains(position))
            .collect();

        // Return the smallest span
        candidates.sort_by_key(|(_, span)| span.length());
        candidates.first().map(|(id, _)| *id)
    }

    /// Clear the index
    pub fn clear(&mut self) {
        self.by_file_and_line.clear();
    }
}
