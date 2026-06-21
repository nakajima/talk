use super::*;

#[derive(Default)]
pub(super) struct DiagnosticSink {
    pub(super) errors: Vec<(TypeError, NodeID)>,
    pub(super) warnings: Vec<(TypeError, NodeID)>,
    pub(super) reported_where_diagnostics: FxHashSet<(NodeID, &'static str)>,
}

impl DiagnosticSink {
    pub(super) fn unsupported(&mut self, node: NodeID, what: &str) {
        self.errors
            .push((TypeError::Unsupported(what.to_string()), node));
    }

    pub(super) fn into_diagnostics(self) -> Vec<AnyDiagnostic> {
        self.errors
            .into_iter()
            .map(|(kind, id)| (kind, id, Severity::Error))
            .chain(
                self.warnings
                    .into_iter()
                    .map(|(kind, id)| (kind, id, Severity::Warn)),
            )
            .map(|(kind, id, severity)| AnyDiagnostic::Types(Diagnostic { id, severity, kind }))
            .collect()
    }
}
