use itertools::Itertools;

use super::InferencePass;
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    types::{
        constraints::{constraint::Constraint, projection::Projection, type_member::TypeMember},
        infer_ty::Ty,
        type_error::TypeError,
    },
};

// Transitional phase wrapper: names post-inference finalization before
// finalization state is ready to move out of InferencePass entirely.
pub(super) struct FinalizeTypesPass<'pass, 'ast> {
    pass: &'pass mut InferencePass<'ast>,
}

impl<'pass, 'ast> FinalizeTypesPass<'pass, 'ast> {
    pub(super) fn new(pass: &'pass mut InferencePass<'ast>) -> Self {
        Self { pass }
    }

    pub(super) fn run(&mut self) {
        self.export_child_types();
        self.report_unsolved();
        self.pass.synthesize_auto_derived_bodies();
    }

    fn export_child_types(&mut self) {
        let child_types = self
            .pass
            .session
            .resolved_names
            .child_types
            .iter()
            .map(|(sym, entries)| (*sym, entries.clone()))
            .collect_vec();

        for (sym, entries) in child_types {
            self.pass
                .session
                .type_catalog
                .child_types
                .entry(sym)
                .or_default()
                .extend(entries);
        }
    }

    fn report_unsolved(&mut self) {
        let unresolved = self
            .pass
            .constraints
            .unsolved()
            .into_iter()
            .cloned()
            .collect_vec();

        for constraint in unresolved {
            let constraint = constraint.apply(&mut self.pass.substitutions, self.pass.session);
            match constraint {
                Constraint::Call(..) => (),
                Constraint::DefaultTy(..) => (),
                Constraint::Equals(..) => (),
                Constraint::HasField(..) => (),
                Constraint::Member(..) => (),
                Constraint::RowSubset(..) => (),
                Constraint::Conforms(conforms) => match &conforms.ty {
                    Ty::Nominal { symbol, .. } | Ty::Primitive(symbol) => {
                        self.pass
                            .diagnostics
                            .insert(AnyDiagnostic::Typing(Diagnostic {
                                id: conforms.conformance_node_id,
                                severity: Severity::Error,
                                kind: TypeError::TypeDoesNotConform {
                                    symbol: *symbol,
                                    protocol_id: conforms.protocol_id,
                                },
                            }));
                    }
                    Ty::Constructor { name, .. } => {
                        self.pass
                            .diagnostics
                            .insert(AnyDiagnostic::Typing(Diagnostic {
                                id: conforms.conformance_node_id,
                                severity: Severity::Error,
                                kind: TypeError::TypeDoesNotConform {
                                    symbol: name
                                        .symbol()
                                        .unwrap_or_else(|_| unreachable!("did not resolve name")),
                                    protocol_id: conforms.protocol_id,
                                },
                            }));
                    }
                    Ty::Var { id, .. }
                        if matches!(
                            self.pass.session.lookup_reverse_instantiation(*id),
                            Some(Ty::Param(_, bounds)) if bounds.contains(&conforms.protocol_id)
                        ) => {}
                    ty => {
                        tracing::error!("did not solve {conforms:?}");
                        self.pass
                            .diagnostics
                            .insert(AnyDiagnostic::Typing(Diagnostic {
                                id: conforms.conformance_node_id,
                                severity: Severity::Error,
                                kind: TypeError::TypeCannotConform {
                                    ty: ty.clone(),
                                    protocol_id: conforms.protocol_id,
                                },
                            }));
                    }
                },
                Constraint::TypeMember(type_member) => self.report_type_member(type_member),
                Constraint::Projection(projection) => self.report_projection(projection),
            }
        }
    }

    fn report_projection(&mut self, projection: Projection) {
        if self.pass.session.can_generalize_projection(
            projection.protocol_id,
            &projection.base,
            &projection.label,
            &mut self.pass.substitutions,
        ) {
            return;
        }

        self.pass
            .diagnostics
            .insert(AnyDiagnostic::Typing(Diagnostic {
                id: projection.node_id,
                severity: Severity::Error,
                kind: TypeError::UnknownAssociatedType {
                    base: projection.base,
                    label: projection.label,
                },
            }));
    }

    fn report_type_member(&mut self, type_member: TypeMember) {
        self.pass
            .diagnostics
            .insert(AnyDiagnostic::Typing(Diagnostic {
                id: type_member.node_id,
                severity: Severity::Error,
                kind: TypeError::UnknownTypeMember {
                    base: type_member.base,
                    member: type_member.name,
                },
            }));
    }
}
