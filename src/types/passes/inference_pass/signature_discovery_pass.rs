use indexmap::IndexMap;
use itertools::Itertools;

use super::InferencePass;
use crate::types::constraints::store::GroupId;
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    name::Name,
    name_resolution::symbol::Symbol,
    node::Node,
    node_kinds::decl::{Decl, DeclKind},
    types::{
        infer_row::Row,
        infer_ty::{Level, Ty},
        predicate::Predicate,
        solve_context::{SolveContext, SolveContextKind},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, curry},
    },
};

// Transitional phase wrapper: keeps signature discovery named and isolated
// before it is ready to move out of InferencePass entirely.
pub(super) struct SignatureDiscovery<'pass, 'ast> {
    pass: &'pass mut InferencePass<'ast>,
}

impl<'pass, 'ast> SignatureDiscovery<'pass, 'ast> {
    pub(super) fn new(pass: &'pass mut InferencePass<'ast>) -> Self {
        Self { pass }
    }

    pub(super) fn run(&mut self) {
        // Register extension conformances first, so they're available when processing protocol default methods
        for i in 0..self.pass.asts.len() {
            self.discover_conformances(i);
        }

        for i in 0..self.pass.asts.len() {
            self.discover_protocols(i, Level::default());
            let inherited = self.pass.session.type_catalog.inherit_conformances();
            self.pass.constraints.wake_conformances(&inherited);

            let mut conformance_keys = self
                .pass
                .session
                .type_catalog
                .conformance_claims
                .keys()
                .chain(self.pass.session.type_catalog.conformance_evidence.keys())
                .copied()
                .collect_vec();
            conformance_keys.sort();
            conformance_keys.dedup();

            for conformance in conformance_keys {
                let protocol_symbol = Symbol::Protocol(conformance.protocol_id);
                let protocol_methods = self.pass.session.lookup_instance_methods(&protocol_symbol);
                if !protocol_methods.is_empty() {
                    self.pass
                        .session
                        .type_catalog
                        .instance_methods
                        .entry(conformance.conforming_id)
                        .or_default()
                        .extend(protocol_methods);
                }
            }

            self.pass.session.apply_all(&mut self.pass.substitutions);
        }

        for i in 0..self.pass.asts.len() {
            self.discover_effects(i, Level::default());
            self.pass.session.apply_all(&mut self.pass.substitutions);
        }
    }

    fn discover_conformances(&mut self, idx: usize) {
        let roots = std::mem::take(&mut self.pass.asts[idx].roots);
        for root in roots.iter() {
            let Node::Decl(Decl {
                kind:
                    DeclKind::Extend {
                        name,
                        conformances,
                        body,
                        ..
                    },
                ..
            }) = root
            else {
                continue;
            };

            // Process typealiases first so they're available for claim validation.
            for decl in &body.decls {
                if let DeclKind::TypeAlias(lhs, _, rhs) = &decl.kind {
                    let Ok(lhs_sym) = lhs.symbol() else {
                        continue;
                    };

                    let mut context = SolveContext::new(
                        UnificationSubstitutions::new(self.pass.session.meta_levels.clone()),
                        Level::default(),
                        GroupId(u32::MAX),
                        SolveContextKind::Nominal,
                    );
                    if let Ok(rhs_ty) = self.pass.visit_type_annotation(rhs, &mut context) {
                        self.pass
                            .session
                            .insert(lhs_sym, rhs_ty, &mut self.pass.constraints);
                    }
                }
            }

            for conformance in conformances {
                let Ok(Symbol::Protocol(protocol_id)) = conformance.symbol() else {
                    continue;
                };

                let Some(conforming_id) = name.symbol().ok() else {
                    tracing::error!("did not resolve {name:?}");
                    continue;
                };

                self.pass
                    .session
                    .declare_conformance(InferencePass::conformance_claim_from_body(
                        conforming_id,
                        protocol_id,
                        conformance.id,
                        conformance.span,
                        body,
                    ));

                self.pass
                    .register_conformance(
                        conforming_id,
                        Symbol::Protocol(protocol_id),
                        conformance.id,
                        conformance.span,
                        &mut SolveContext::new(
                            UnificationSubstitutions::new(self.pass.session.meta_levels.clone()),
                            Level::default(),
                            GroupId(u32::MAX),
                            SolveContextKind::Nominal,
                        ),
                    )
                    .ok();
            }
        }
        _ = std::mem::replace(&mut self.pass.asts[idx].roots, roots);
    }

    fn discover_effects(&mut self, idx: usize, level: Level) {
        let mut context = SolveContext::new(
            self.pass.substitutions.clone(),
            level,
            Default::default(),
            SolveContextKind::Normal,
        );
        let roots = std::mem::take(&mut self.pass.asts[idx].roots);
        for root in roots.iter() {
            let Node::Decl(Decl {
                kind:
                    DeclKind::Effect {
                        name: Name::Resolved(symbol, ..),
                        generics,
                        params,
                        ret,
                        ..
                    },
                ..
            }) = &root
            else {
                continue;
            };

            // Register generic type parameters for the effect
            for generic in generics.iter() {
                self.pass.register_generic(generic, &mut context);
            }

            let params = match self.pass.visit_params(params, &mut context) {
                Ok(params) => params,
                Err(e) => {
                    self.pass
                        .diagnostics
                        .insert(AnyDiagnostic::Typing(Diagnostic {
                            id: root.node_id(),
                            severity: Severity::Error,
                            kind: e,
                        }));
                    continue;
                }
            };

            let ret = match self.pass.visit_type_annotation(ret, &mut context) {
                Ok(ret) => ret,
                Err(e) => {
                    self.pass
                        .diagnostics
                        .insert(AnyDiagnostic::Typing(Diagnostic {
                            id: root.node_id(),
                            severity: Severity::Error,
                            kind: e,
                        }));
                    continue;
                }
            };

            let effect_signature =
                curry(params.iter().map(|p| p.ty.clone()), ret, Row::Empty.into());
            self.pass
                .session
                .type_catalog
                .effects
                .insert(*symbol, effect_signature.clone());

            // Also insert into term_env so effect types are available in types_by_symbol for IR lowerer
            self.pass
                .session
                .insert(*symbol, effect_signature, &mut self.pass.constraints);
        }
        _ = std::mem::replace(&mut self.pass.asts[idx].roots, roots);
    }

    fn discover_protocols(&mut self, idx: usize, level: Level) {
        let mut result = vec![];
        let roots = std::mem::take(&mut self.pass.asts[idx].roots);
        for root in roots.iter() {
            let Node::Decl(
                decl @ Decl {
                    kind:
                        DeclKind::Protocol {
                            name: protocol_name @ Name::Resolved(Symbol::Protocol(protocol_id), ..),
                            generics,
                            conformances,
                            body,
                            ..
                        },
                    ..
                },
            ) = root
            else {
                continue;
            };

            let Ok(protocol_sym) = protocol_name.symbol() else {
                self.pass
                    .diagnostics
                    .insert(AnyDiagnostic::Typing(Diagnostic {
                        id: root.node_id(),
                        severity: Severity::Error,
                        kind: TypeError::NameNotResolved(protocol_name.clone()),
                    }));
                continue;
            };

            let protocol_self_id = self.pass.session.new_type_param_id(None);
            self.pass.session.insert(
                protocol_sym,
                Ty::Param(protocol_self_id, vec![*protocol_id]),
                &mut self.pass.constraints,
            );

            let mut context = SolveContext::new(
                self.pass.substitutions.clone(),
                level,
                Default::default(),
                SolveContextKind::Protocol {
                    protocol_id: *protocol_id,
                    protocol_self: protocol_self_id,
                },
            );

            context.givens_mut().insert(Predicate::Conforms {
                param: protocol_self_id,
                protocol_id: *protocol_id,
            });

            let mut binders = IndexMap::<Symbol, Ty>::default();

            match self.pass.visit_protocol(
                decl,
                protocol_name,
                generics,
                conformances,
                body,
                &mut context,
            ) {
                Ok((decl, new_binders)) => {
                    result.push(decl);
                    binders.extend(new_binders)
                }
                Err(e) => {
                    self.pass
                        .diagnostics
                        .insert(AnyDiagnostic::Typing(Diagnostic {
                            id: decl.id,
                            severity: Severity::Error,
                            kind: e,
                        }));
                }
            }

            let (binders, placeholders) = binders.into_iter().unzip();
            self.pass.solve(&mut context, binders, placeholders)
        }
        _ = std::mem::replace(&mut self.pass.asts[idx].roots, roots);

        self.pass.root_decls.extend(result);
    }
}
