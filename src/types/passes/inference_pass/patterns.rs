use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::pattern::{Pattern, PatternKind, RecordFieldPatternKind},
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::Row,
        infer_ty::Ty,
        solve_context::SolveContext,
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::curry,
        typed_ast::{
            TypedPattern, TypedPatternKind, TypedRecordFieldPattern, TypedRecordFieldPatternKind,
        },
    },
};

impl InferencePass<'_> {
    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    fn _promote_pattern_bindings(
        &mut self,
        pattern: &Pattern,
        expected: &Ty,
        context: &mut SolveContext,
    ) -> Ty {
        match &pattern.kind {
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                if let Some(EnvEntry::Mono(existing)) = self.session.lookup(sym) {
                    self.constraints.wants_equals_at_with_cause(
                        pattern.id,
                        expected.clone(),
                        existing.clone(),
                        &context.group_info(),
                        Some(ConstraintCause::Pattern(pattern.id)),
                    );
                };

                self.session
                    .insert(*sym, expected.clone(), &mut self.constraints);
                expected.clone()
            }
            PatternKind::Tuple(items) => {
                let ty = Ty::Tuple(
                    items
                        .iter()
                        .map(|i| {
                            let var = self.session.new_ty_meta_var_id(context.level());

                            self._promote_pattern_bindings(
                                i,
                                &Ty::Var {
                                    id: var,
                                    level: context.level(),
                                },
                                context,
                            )
                        })
                        .collect_vec(),
                );

                self.constraints.wants_equals_at_with_cause(
                    pattern.id,
                    ty.clone(),
                    expected.clone(),
                    &context.group_info(),
                    Some(ConstraintCause::Pattern(pattern.id)),
                );

                ty
            }
            PatternKind::Record { fields } => {
                let mut row = Row::Empty;
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            let Ok(sym) = name.symbol() else {
                                self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                    id: field.id,
                                    severity: Severity::Error,
                                    kind: TypeError::NameNotResolved(name.clone()),
                                }));
                                return Ty::Error(TypeError::NameNotResolved(name.clone()).into());
                            };

                            let var = self.session.new_ty_meta_var_id(context.level());
                            let ty = Ty::Var {
                                id: var,
                                level: context.level(),
                            };

                            self.session.insert(sym, ty.clone(), &mut self.constraints);
                            row = Row::Extend {
                                row: row.into(),
                                label: name.name_str().into(),
                                ty,
                            };
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            let Ok(sym) = name.symbol() else {
                                self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                    id: field.id,
                                    severity: Severity::Error,
                                    kind: TypeError::NameNotResolved(name.clone()),
                                }));
                                return Ty::Error(TypeError::NameNotResolved(name.clone()).into());
                            };

                            let ty = if let Some(existing) = self.session.lookup(&sym) {
                                existing._as_ty()
                            } else {
                                let var = self.session.new_ty_meta_var_id(context.level());

                                Ty::Var {
                                    id: var,
                                    level: context.level(),
                                }
                            };
                            let ty = self._promote_pattern_bindings(value, &ty, context);
                            row = Row::Extend {
                                row: row.into(),
                                label: name.name_str().into(),
                                ty,
                            };
                        }
                        RecordFieldPatternKind::Rest => {}
                    }
                }

                let ty = Ty::Record(None, row.into());
                self.constraints.wants_equals_at_with_cause(
                    pattern.id,
                    ty.clone(),
                    expected.clone(),
                    &context.group_info(),
                    Some(ConstraintCause::Pattern(pattern.id)),
                );

                ty
            }
            // cover any other pattern forms you support
            _ => Ty::Void,
        }
    }

    fn lookup_or_binder(&self, sym: Symbol) -> Option<Ty> {
        for binders in self.or_binders.iter().rev() {
            if let Some(ty) = binders.get(&sym) {
                return Some(ty.clone());
            }
        }
        None
    }

    fn prepare_or_binders(
        &mut self,
        pattern_id: NodeID,
        patterns: &[Pattern],
        context: &mut SolveContext,
    ) -> FxHashMap<Symbol, Ty> {
        let mut sets = vec![];
        for pattern in patterns {
            let mut set = FxHashSet::default();
            for (_, sym) in pattern.collect_binders() {
                set.insert(sym);
            }
            sets.push(set);
        }

        let baseline = sets.first().cloned().unwrap_or_default();
        if sets.iter().skip(1).any(|set| *set != baseline) {
            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                id: pattern_id,
                severity: Severity::Error,
                kind: TypeError::OrPatternBinderMismatch,
            }));
        }

        let mut binders = FxHashMap::default();
        for sym in baseline {
            let canonical = self.session.new_ty_meta_var(context.level());
            if let Some(existing) = self.session.lookup(&sym) {
                self.constraints.wants_equals_at_with_cause(
                    pattern_id,
                    existing._as_ty(),
                    canonical.clone(),
                    &context.group_info(),
                    Some(ConstraintCause::Pattern(pattern_id)),
                );
            }

            self.session
                .insert_mono(sym, canonical.clone(), &mut self.constraints);
            binders.insert(sym, canonical);
        }

        binders
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    pub(super) fn check_pattern(
        &mut self,
        pattern: &Pattern,
        expected: &Ty,
        context: &mut SolveContext,
    ) -> TypedRet<TypedPattern> {
        let Pattern { kind, .. } = &pattern;

        let typed_kind = match kind {
            PatternKind::Or(patterns) => {
                let binders = self.prepare_or_binders(pattern.id, patterns, context);
                self.or_binders.push(binders);
                let typed_patterns = patterns
                    .iter()
                    .map(|pattern| self.check_pattern(pattern, expected, context))
                    .try_collect();
                self.or_binders.pop();
                TypedPatternKind::Or(typed_patterns?)
            }
            PatternKind::Bind(Name::Raw(name)) => {
                self.constraints.wants_equals_at_with_cause(
                    pattern.id,
                    expected.clone(),
                    Ty::Error(TypeError::NameNotResolved(name.clone().into()).into()),
                    &context.group_info(),
                    Some(ConstraintCause::Pattern(pattern.id)),
                );
                TypedPatternKind::Bind(Symbol::Synthesized(
                    self.session
                        .symbols
                        .next_synthesized(self.session.current_module_id),
                ))
            }
            PatternKind::Bind(Name::Resolved(sym, _)) => {
                if let Some(ty) = self.lookup_or_binder(*sym) {
                    self.constraints.wants_equals_at_with_cause(
                        pattern.id,
                        expected.clone(),
                        ty,
                        &context.group_info(),
                        Some(ConstraintCause::Pattern(pattern.id)),
                    );
                } else {
                    self.session
                        .insert_mono(*sym, expected.clone(), &mut self.constraints);
                }
                TypedPatternKind::Bind(*sym)
            }
            PatternKind::Bind(Name::SelfType(..)) => TypedPatternKind::Bind(Symbol::Synthesized(
                self.session
                    .symbols
                    .next_synthesized(self.session.current_module_id),
            )),
            PatternKind::LiteralInt(val) => {
                self.constraints.wants_equals_at_with_cause(
                    pattern.id,
                    expected.clone(),
                    Ty::Int,
                    &context.group_info(),
                    Some(ConstraintCause::Literal(pattern.id)),
                );

                TypedPatternKind::LiteralInt(val.clone())
            }
            PatternKind::LiteralFloat(val) => {
                self.constraints.wants_equals_at_with_cause(
                    pattern.id,
                    expected.clone(),
                    Ty::Float,
                    &context.group_info(),
                    Some(ConstraintCause::Literal(pattern.id)),
                );

                TypedPatternKind::LiteralFloat(val.clone())
            }
            PatternKind::LiteralFalse => {
                self.constraints.wants_equals_at_with_cause(
                    pattern.id,
                    expected.clone(),
                    Ty::Bool,
                    &context.group_info(),
                    Some(ConstraintCause::Literal(pattern.id)),
                );

                TypedPatternKind::LiteralFalse
            }
            PatternKind::LiteralTrue => {
                self.constraints.wants_equals_at_with_cause(
                    pattern.id,
                    expected.clone(),
                    Ty::Bool,
                    &context.group_info(),
                    Some(ConstraintCause::Literal(pattern.id)),
                );

                TypedPatternKind::LiteralTrue
            }
            PatternKind::Tuple(patterns) => {
                let metas: Vec<Ty> = (0..patterns.len())
                    .map(|_| self.session.new_ty_meta_var(context.level()))
                    .collect();

                self.constraints.wants_equals_at_with_cause(
                    pattern.id,
                    expected.clone(),
                    Ty::Tuple(metas.clone()),
                    &context.group_info(),
                    Some(ConstraintCause::Pattern(pattern.id)),
                );

                TypedPatternKind::Tuple(
                    patterns
                        .iter()
                        .zip(metas)
                        .map(|(pi, bi)| self.check_pattern(pi, &bi, context))
                        .try_collect()?,
                )
            }
            PatternKind::Record { fields } => {
                let expected_row = self.ensure_row_record(expected, pattern.id, context);
                let mut typed_fields = vec![];
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            let Ok(sym) = name.symbol() else {
                                self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                                    id: field.id,
                                    severity: Severity::Error,
                                    kind: TypeError::NameNotResolved(name.clone()),
                                }));
                                continue;
                            };

                            // fresh meta for the field type
                            let field_ty = self.session.new_ty_meta_var(context.level());

                            // bind the pattern name
                            self.session
                                .insert_mono(sym, field_ty.clone(), &mut self.constraints);

                            // ONE RowHas per field, all referring to the same row
                            self.constraints._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty,
                                Some(field.id),
                                &context.group_info(),
                            );

                            typed_fields.push(TypedRecordFieldPattern {
                                id: field.id,
                                kind: TypedRecordFieldPatternKind::Bind(sym),
                            });
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            // optional: pattern field = subpattern; same RowHas then recurse on value
                            let field_ty = self.session.new_ty_meta_var(context.level());
                            self.constraints._has_field(
                                expected_row.clone(),
                                name.name_str().into(),
                                field_ty.clone(),
                                Some(field.id),
                                &context.group_info(),
                            );

                            typed_fields.push(TypedRecordFieldPattern {
                                id: field.id,
                                kind: TypedRecordFieldPatternKind::Equals {
                                    name: name
                                        .symbol()
                                        .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                                    value: self.check_pattern(value, &field_ty, context)?,
                                },
                            });
                        }
                        RecordFieldPatternKind::Rest => {
                            typed_fields.push(TypedRecordFieldPattern {
                                id: field.id,
                                kind: TypedRecordFieldPatternKind::Rest,
                            })
                        }
                    }
                }

                TypedPatternKind::Record {
                    fields: typed_fields,
                }
            }
            PatternKind::Variant {
                enum_name,
                variant_name,
                variant_name_span,
                fields,
            } => {
                let field_metas: Vec<Ty> = fields
                    .iter()
                    .map(|_| {
                        let var_id = self.session.new_ty_meta_var_id(context.level());
                        Ty::Var {
                            id: var_id,
                            level: context.level(),
                        }
                    })
                    .collect();
                let payload = if fields.is_empty() {
                    expected.clone()
                } else if fields.len() == 1 {
                    Ty::Func(
                        field_metas[0].clone().into(),
                        expected.clone().into(),
                        Row::Empty.into(),
                    )
                } else {
                    curry(field_metas.clone(), expected.clone(), Row::Empty.into())
                };

                self.constraints.wants_member(
                    pattern.id,
                    expected.clone(),
                    variant_name.into(),
                    payload,
                    &context.group_info(),
                );

                // Recursively check each field pattern
                TypedPatternKind::Variant {
                    enum_name: enum_name
                        .clone()
                        .map(|s| {
                            s.symbol()
                                .map_err(|_| TypeError::NameNotResolved(s.clone()))
                        })
                        .transpose()?,
                    variant_name: variant_name.clone(),
                    variant_name_span: *variant_name_span,
                    fields: fields
                        .iter()
                        .zip(field_metas)
                        .map(|(field_pattern, field_ty)| {
                            self.check_pattern(field_pattern, &field_ty, context)
                        })
                        .try_collect()?,
                }
            }
            PatternKind::Wildcard => TypedPatternKind::Wildcard,
            #[allow(clippy::todo)]
            PatternKind::Struct { .. } => todo!(),
        };

        // Store pattern type for symbol index resolution (variant patterns, etc.)
        self.session
            .types_by_node
            .insert(pattern.id, expected.clone());

        Ok(TypedPattern {
            id: pattern.id,
            ty: expected.clone(),
            kind: typed_kind,
        })
    }

    fn ensure_row_record(
        &mut self,
        expected: &Ty,
        node_id: NodeID,
        context: &mut SolveContext,
    ) -> Row {
        match expected {
            Ty::Record(_, box row) => (*row).clone(),
            _ => {
                let row = self.session.new_row_meta_var(context.level());
                self.constraints.wants_equals_at_with_cause(
                    node_id,
                    expected.clone(),
                    Ty::Record(None, Box::new(row.clone())),
                    &context.group_info(),
                    Some(ConstraintCause::Pattern(node_id)),
                );
                row
            }
        }
    }
}
