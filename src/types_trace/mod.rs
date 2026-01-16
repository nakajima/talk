//! Type checker visualization.
//!
//! Generates an interactive HTML visualization showing inferred types
//! for each expression in the source code.

mod html;

use std::path::PathBuf;

use rustc_hash::FxHashMap;

use crate::node_id::NodeID;
use crate::span::Span;
use crate::types::types::Types;

/// Information needed to generate the visualization.
pub struct TypesVisualization {
    /// Source files: (path, content)
    pub sources: Vec<(PathBuf, String)>,
    /// Mapping from NodeID to source span
    pub node_spans: FxHashMap<NodeID, Span>,
    /// The inferred types
    pub types: Types,
}

/// Generate an HTML visualization of the type information.
pub fn generate_html(viz: &TypesVisualization) -> String {
    html::generate(viz)
}
