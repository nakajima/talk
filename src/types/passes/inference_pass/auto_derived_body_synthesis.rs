use indexmap::IndexMap;

use super::{InferencePass, TypedRet};
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        call_arg::CallArg,
        expr::{Expr, ExprKind},
        func::{EffectSet, Func},
        match_arm::MatchArm,
        parameter::Parameter,
        pattern::{Pattern, PatternKind},
    },
    span::Span,
    types::{
        conformance::{ConformanceEvidence, ConformanceKey},
        infer_ty::Ty,
        solve_context::SolveContext,
        type_catalog::Nominal,
        type_session::ShowDerivation,
        typed_ast::{TypedDecl, TypedDeclKind, TypedFunc},
    },
};

impl InferencePass<'_> {
    pub(super) fn synthesize_show_derived_bodies(
        &mut self,
        derivations: Vec<ShowDerivation>,
        context: &mut SolveContext,
    ) {
        for derivation in derivations {
            let nominal_sym = derivation.nominal;
            let Some(nominal) = self.session.lookup_nominal(&nominal_sym) else {
                continue;
            };

            let type_name = self.type_name(nominal_sym);
            let nominal_ty = self
                .session
                .lookup(&derivation.self_param)
                .map(|entry| entry._as_ty())
                .unwrap_or_else(|| Ty::Nominal {
                    symbol: nominal_sym,
                    type_args: nominal.type_params.clone(),
                });
            let show_label = Label::Named("show".into());
            let func = self.synth_show_func(
                &nominal,
                &type_name,
                nominal_sym,
                show_label.clone(),
                derivation.method,
                derivation.self_param,
            );

            let mut instance_methods = IndexMap::<Label, TypedFunc>::new();
            match self.visit_auto_derived_method(nominal_sym, nominal_ty.clone(), &func, context) {
                Ok(typed_func) => {
                    instance_methods.insert(show_label, typed_func);
                }
                Err(kind) => {
                    self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                        id: func.id,
                        severity: Severity::Error,
                        kind,
                    }));
                    continue;
                }
            }

            self.root_decls.push(TypedDecl {
                id: NodeID(FileID::SYNTHESIZED, 0),
                ty: nominal_ty,
                kind: TypedDeclKind::Extend {
                    symbol: nominal_sym,
                    instance_methods,
                    typealiases: Default::default(),
                },
            });

            let key = ConformanceKey {
                conforming_id: nominal_sym,
                protocol_id: derivation.protocol_id,
            };
            self.session.record_evidence(
                key,
                ConformanceEvidence::synthetic(
                    nominal_sym,
                    derivation.protocol_id,
                    derivation.witnesses,
                ),
            );
            self.constraints.wake_symbols(&[nominal_sym]);
            self.constraints.wake_conformances(&[key]);
        }
    }

    fn visit_auto_derived_method(
        &mut self,
        nominal_sym: Symbol,
        nominal_ty: Ty,
        func: &Func,
        context: &mut SolveContext,
    ) -> TypedRet<TypedFunc> {
        let mut method_context = context.next();
        for predicate in nominal_ty.collect_param_predicates() {
            method_context.givens_mut().insert(predicate);
        }

        let previous_self = self.current_self_ty.replace(nominal_ty);
        let result = self.visit_method(nominal_sym, func, false, &mut method_context);
        self.current_self_ty = previous_self;
        result
    }

    fn synth_show_func(
        &mut self,
        nominal: &Nominal,
        type_name: &str,
        nominal_sym: Symbol,
        label: Label,
        method_sym: Symbol,
        self_param_sym: Symbol,
    ) -> Func {
        let body_expr = if nominal.variants.is_empty() {
            self.synthesize_struct_show_expr(nominal, type_name, self_param_sym)
        } else {
            self.synthesize_enum_show_expr(nominal, type_name, self_param_sym, nominal_sym)
        };

        Func {
            id: self.next_synth_node(),
            name: Name::Resolved(method_sym, label.to_string()),
            name_span: Span::SYNTHESIZED,
            effects: EffectSet::default(),
            generics: vec![],
            params: vec![Parameter {
                id: self.next_synth_node(),
                name: Name::Resolved(self_param_sym, "self".into()),
                name_span: Span::SYNTHESIZED,
                type_annotation: None,
                span: Span::SYNTHESIZED,
            }],
            body: Block {
                id: self.next_synth_node(),
                args: vec![],
                body: vec![Node::Expr(body_expr)],
                span: Span::SYNTHESIZED,
            },
            ret: None,
            attributes: vec![],
        }
    }

    fn synthesize_struct_show_expr(
        &mut self,
        nominal: &Nominal,
        type_name: &str,
        self_param_sym: Symbol,
    ) -> Expr {
        if nominal.properties.is_empty() {
            return self.synth_string_literal(&format!("{type_name} {{}}"));
        }

        let mut parts = vec![];
        for (index, (label, _)) in nominal.properties.iter().enumerate() {
            let prefix = if index == 0 {
                format!("{type_name}({label}: ")
            } else {
                format!(", {label}: ")
            };
            parts.push(self.synth_string_literal(&prefix));

            let self_var = self.synth_variable(self_param_sym, "self");
            let field_access = self.synth_member(self_var, label.clone());
            parts.push(self.synth_show_call(field_access));
        }
        parts.push(self.synth_string_literal(")"));

        self.synth_string_concat(parts)
    }

    fn synthesize_enum_show_expr(
        &mut self,
        nominal: &Nominal,
        type_name: &str,
        self_param_sym: Symbol,
        nominal_sym: Symbol,
    ) -> Expr {
        let scrutinee = self.synth_variable(self_param_sym, "self");
        let mut arms = vec![];

        for (variant_label, payload_tys) in &nominal.variants {
            let mut fields = vec![];
            let mut bindings = vec![];
            for index in 0..payload_tys.len() {
                let name = format!("v{index}");
                let bind_sym = Symbol::PatternBindLocal(self.session.symbols.next_pattern_bind());
                self.session
                    .resolved_names
                    .symbol_names
                    .insert(bind_sym, name.clone());
                bindings.push((bind_sym, name));
                fields.push(Pattern {
                    id: self.next_synth_node(),
                    kind: PatternKind::Bind(Name::Resolved(bind_sym, format!("v{index}"))),
                    span: Span::SYNTHESIZED,
                });
            }

            let pattern = Pattern {
                id: self.next_synth_node(),
                kind: PatternKind::Variant {
                    enum_name: Some(Name::Resolved(nominal_sym, type_name.into())),
                    variant_name: variant_label.to_string(),
                    variant_name_span: Span::SYNTHESIZED,
                    fields,
                },
                span: Span::SYNTHESIZED,
            };

            let body_expr = if payload_tys.is_empty() {
                self.synth_string_literal(&format!("{type_name}.{variant_label}"))
            } else {
                let mut parts =
                    vec![self.synth_string_literal(&format!("{type_name}.{variant_label}("))];
                for (index, (bind_sym, bind_name)) in bindings.iter().enumerate() {
                    if index > 0 {
                        parts.push(self.synth_string_literal(", "));
                    }
                    let var = self.synth_variable(*bind_sym, bind_name);
                    parts.push(self.synth_show_call(var));
                }
                parts.push(self.synth_string_literal(")"));
                self.synth_string_concat(parts)
            };

            arms.push(MatchArm {
                id: self.next_synth_node(),
                pattern,
                body: Block {
                    id: self.next_synth_node(),
                    args: vec![],
                    body: vec![Node::Expr(body_expr)],
                    span: Span::SYNTHESIZED,
                },
                span: Span::SYNTHESIZED,
            });
        }

        Expr {
            id: self.next_synth_node(),
            kind: ExprKind::Match(scrutinee.into(), arms),
            span: Span::SYNTHESIZED,
        }
    }

    fn synth_string_concat(&mut self, parts: Vec<Expr>) -> Expr {
        let mut iter = parts.into_iter();
        let mut acc = iter.next().unwrap_or_else(|| self.synth_string_literal(""));
        for part in iter {
            let add_member = self.synth_member(acc, "add".into());
            acc = self.synth_call(add_member, vec![part]);
        }
        acc
    }

    fn synth_show_call(&mut self, receiver: Expr) -> Expr {
        let show_member = self.synth_member(receiver, "show".into());
        self.synth_call(show_member, vec![])
    }

    fn synth_call(&mut self, callee: Expr, args: Vec<Expr>) -> Expr {
        Expr {
            id: self.next_synth_node(),
            kind: ExprKind::Call {
                callee: callee.into(),
                type_args: vec![],
                args: args
                    .into_iter()
                    .enumerate()
                    .map(|(index, value)| CallArg {
                        id: self.next_synth_node(),
                        label: Label::Positional(index),
                        label_span: Span::SYNTHESIZED,
                        value,
                        span: Span::SYNTHESIZED,
                    })
                    .collect(),
                trailing_block: None,
            },
            span: Span::SYNTHESIZED,
        }
    }

    fn synth_member(&mut self, receiver: Expr, label: Label) -> Expr {
        Expr {
            id: self.next_synth_node(),
            kind: ExprKind::Member(Some(receiver.into()), label, Span::SYNTHESIZED),
            span: Span::SYNTHESIZED,
        }
    }

    fn synth_variable(&mut self, symbol: Symbol, name: &str) -> Expr {
        Expr {
            id: self.next_synth_node(),
            kind: ExprKind::Variable(Name::Resolved(symbol, name.into())),
            span: Span::SYNTHESIZED,
        }
    }

    fn synth_string_literal(&mut self, value: &str) -> Expr {
        Expr {
            id: self.next_synth_node(),
            kind: ExprKind::LiteralString(value.into()),
            span: Span::SYNTHESIZED,
        }
    }

    fn type_name(&self, nominal_sym: Symbol) -> String {
        self.session
            .resolved_names
            .symbol_names
            .get(&nominal_sym)
            .cloned()
            .or_else(|| {
                self.session
                    .modules
                    .imported_symbol_names()
                    .get(&nominal_sym)
                    .cloned()
            })
            .unwrap_or_else(|| format!("{nominal_sym:?}"))
    }
}
