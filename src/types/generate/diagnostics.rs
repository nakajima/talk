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

    pub(super) fn argument_arity(
        &mut self,
        node: NodeID,
        target: String,
        expected: usize,
        found: usize,
    ) {
        let error = (
            TypeError::ArgumentArityMismatch {
                target,
                expected,
                found,
            },
            node,
        );
        if !self.errors.contains(&error) {
            self.errors.push(error);
        }
    }

    pub(super) fn generic_argument_arity(
        &mut self,
        node: NodeID,
        target: String,
        expected: usize,
        found: usize,
    ) {
        let error = (
            TypeError::GenericArgumentArityMismatch {
                target,
                expected,
                found,
            },
            node,
        );
        if !self.errors.contains(&error) {
            self.errors.push(error);
        }
    }

    pub(super) fn into_diagnostics(
        self,
        synthetic_origins: &FxHashMap<NodeID, NodeID>,
    ) -> Vec<AnyDiagnostic> {
        self.errors
            .into_iter()
            .map(|(kind, id)| (kind, id, Severity::Error))
            .chain(
                self.warnings
                    .into_iter()
                    .map(|(kind, id)| (kind, id, Severity::Warn)),
            )
            .map(|(kind, mut id, severity)| {
                while let Some(owner) = synthetic_origins.get(&id).copied() {
                    if owner == id {
                        break;
                    }
                    id = owner;
                }
                AnyDiagnostic::Types(Diagnostic { id, severity, kind })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node_id::FileID;

    #[test]
    fn diagnostics_from_generated_nodes_are_remapped_to_surface_owners() {
        let surface = NodeID(FileID(0), 7);
        let generated = NodeID(FileID(0), u32::MAX - 2);
        let mut sink = DiagnosticSink::default();
        sink.errors.push((
            TypeError::Unsupported("generated failure".into()),
            generated,
        ));
        let origins = FxHashMap::from_iter([(generated, surface)]);

        let diagnostics = sink.into_diagnostics(&origins);
        let AnyDiagnostic::Types(diagnostic) = &diagnostics[0] else {
            panic!("expected a type diagnostic");
        };
        assert_eq!(diagnostic.id, surface);
    }
}
