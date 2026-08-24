//! The shared immutable source snapshot (CLEAN-04): one `Arc<str>`
//! allocation per document plus its cached line index (CLEAN-07),
//! shared by the editor workspace, the compiler's source inputs, and
//! every position conversion. Cloning is cheap and never copies text.

use std::sync::Arc;

use crate::common::line_index::LineIndex;

#[derive(Clone, Debug)]
pub struct SourceSnapshot {
    text: Arc<str>,
    line_index: LineIndex,
}

impl SourceSnapshot {
    pub fn new(text: impl Into<Arc<str>>) -> Self {
        let text = text.into();
        let line_index = LineIndex::new(&text);
        Self { text, line_index }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn text_arc(&self) -> Arc<str> {
        self.text.clone()
    }

    pub fn line_index(&self) -> &LineIndex {
        &self.line_index
    }
}
