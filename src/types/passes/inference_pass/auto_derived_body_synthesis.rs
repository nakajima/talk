use indexmap::IndexMap;

use super::InferencePass;
use crate::{
    label::Label,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_id::NodeID,
    span::Span,
    types::{
        infer_row::Row,
        infer_ty::Ty,
        type_catalog::Nominal,
        typed_ast::{
            TypedBlock, TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedFunc,
            TypedMatchArm, TypedNode, TypedParameter, TypedPattern, TypedPatternKind,
        },
    },
};

impl InferencePass<'_> {
    /// Build synthesized TypedFunc bodies for auto-derived protocol methods.
    pub(super) fn synthesize_auto_derived_bodies(&mut self) {
        let derivations: Vec<_> = self
            .session
            .auto_derived
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect();

        // Look up the String.add witness (for string concatenation)
        let add_label: Label = "add".into();
        let string_add_witness = self.session.find_protocol_id("Add").and_then(|add_id| {
            self.session
                .find_witness(Symbol::String, add_id, &add_label)
        });

        // Look up the Showable protocol ID for finding show witnesses
        let showable_id = self.session.find_protocol_id("Showable");

        for ((nominal_sym, _protocol_id), methods) in derivations {
            let Some(nominal) = self.session.lookup_nominal(&nominal_sym) else {
                continue;
            };

            let type_name = self
                .session
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
                .unwrap_or_else(|| format!("{nominal_sym:?}"));

            let nominal_ty = Ty::Nominal {
                symbol: nominal_sym,
                type_args: nominal.type_params.clone(),
            };

            let mut instance_methods = IndexMap::new();

            for (label, method_sym, self_param_sym) in methods {
                let body_expr = if !nominal.variants.is_empty() {
                    self.synthesize_enum_show_body(
                        &nominal,
                        &type_name,
                        self_param_sym,
                        nominal_sym,
                        &nominal_ty,
                        string_add_witness,
                        showable_id,
                    )
                } else {
                    self.synthesize_struct_show_body(
                        &nominal,
                        &type_name,
                        self_param_sym,
                        &nominal_ty,
                        string_add_witness,
                        showable_id,
                    )
                };

                let typed_func = TypedFunc {
                    name: method_sym,
                    foralls: Default::default(),
                    params: vec![TypedParameter {
                        name: self_param_sym,
                        ty: nominal_ty.clone(),
                    }],
                    effects: vec![],
                    effects_row: Row::Empty,
                    body: TypedBlock {
                        id: NodeID::SYNTHESIZED,
                        body: vec![TypedNode::Expr(body_expr)],
                        ret: Ty::String(),
                    },
                    ret: Ty::String(),
                };

                instance_methods.insert(label, typed_func);
            }

            // Use a low node ID so auto-derived extends sort before user code
            // in TypedAST::roots(). Otherwise they'd be the last node in the
            // synthesized main function body and override the return value.
            self.root_decls.push(TypedDecl {
                id: NodeID(crate::node_id::FileID::SYNTHESIZED, 0),
                ty: nominal_ty,
                kind: TypedDeclKind::Extend {
                    symbol: nominal_sym,
                    instance_methods,
                    typealiases: Default::default(),
                },
            });
        }
    }

    fn synthesize_struct_show_body(
        &mut self,
        nominal: &Nominal,
        type_name: &str,
        self_param_sym: Symbol,
        nominal_ty: &Ty,
        string_add_witness: Option<Symbol>,
        showable_id: Option<ProtocolId>,
    ) -> TypedExpr {
        if nominal.properties.is_empty() {
            // Empty struct: "TypeName {}"
            return self.synth_string_literal(&format!("{type_name} {{}}"));
        }

        // Build: "TypeName(field1: " + self.field1.show() + ", field2: " + self.field2.show() + ")"
        let fields: Vec<_> = nominal.properties.iter().collect();
        let mut parts: Vec<TypedExpr> = vec![];

        for (i, (label, field_ty)) in fields.iter().enumerate() {
            let prefix = if i == 0 {
                format!("{type_name}({label}: ")
            } else {
                format!(", {label}: ")
            };
            parts.push(self.synth_string_literal(&prefix));

            // self.field.show()
            let self_var = TypedExpr {
                id: NodeID::SYNTHESIZED,
                ty: nominal_ty.clone(),
                kind: TypedExprKind::Variable(self_param_sym),
            };
            let field_access = TypedExpr {
                id: NodeID::SYNTHESIZED,
                ty: (*field_ty).clone(),
                kind: TypedExprKind::Member {
                    receiver: self_var.into(),
                    label: (*label).clone(),
                    label_span: Span::SYNTHESIZED,
                },
            };

            if matches!(**field_ty, Ty::Func(..)) {
                parts.push(self.synth_func_type_literal(field_ty));
            } else {
                let show_witness = self.find_show_witness_for_ty(field_ty, showable_id);
                parts.push(self.synth_show_call(field_access, show_witness, showable_id));
            }
        }
        parts.push(self.synth_string_literal(")"));

        self.synth_string_concat(parts, string_add_witness)
    }

    fn synthesize_enum_show_body(
        &mut self,
        nominal: &Nominal,
        type_name: &str,
        self_param_sym: Symbol,
        nominal_sym: Symbol,
        nominal_ty: &Ty,
        string_add_witness: Option<Symbol>,
        showable_id: Option<ProtocolId>,
    ) -> TypedExpr {
        let self_var = TypedExpr {
            id: NodeID::SYNTHESIZED,
            ty: nominal_ty.clone(),
            kind: TypedExprKind::Variable(self_param_sym),
        };

        let mut arms = vec![];

        for (variant_label, payload_tys) in &nominal.variants {
            if payload_tys.is_empty() {
                // No payload: "TypeName.variant"
                let pattern = TypedPattern {
                    id: NodeID::SYNTHESIZED,
                    ty: nominal_ty.clone(),
                    kind: TypedPatternKind::Variant {
                        enum_name: Some(nominal_sym),
                        variant_name: variant_label.to_string(),
                        variant_name_span: Span::SYNTHESIZED,
                        fields: vec![],
                    },
                };
                let body_expr = self.synth_string_literal(&format!("{type_name}.{variant_label}"));
                arms.push(TypedMatchArm {
                    pattern,
                    body: TypedBlock {
                        id: NodeID::SYNTHESIZED,
                        body: vec![TypedNode::Expr(body_expr)],
                        ret: Ty::String(),
                    },
                });
            } else {
                // With payload: bind values and show them
                let mut bind_syms = vec![];
                let mut bind_patterns = vec![];
                for (j, payload_ty) in payload_tys.iter().enumerate() {
                    let bind_sym =
                        Symbol::PatternBindLocal(self.session.symbols.next_pattern_bind());
                    self.session
                        .resolved_names
                        .symbol_names
                        .insert(bind_sym, format!("v{j}"));
                    self.session.register_mono(bind_sym, payload_ty.clone());
                    bind_syms.push((bind_sym, payload_ty.clone()));
                    bind_patterns.push(TypedPattern {
                        id: NodeID::SYNTHESIZED,
                        ty: payload_ty.clone(),
                        kind: TypedPatternKind::Bind(bind_sym),
                    });
                }

                let pattern = TypedPattern {
                    id: NodeID::SYNTHESIZED,
                    ty: nominal_ty.clone(),
                    kind: TypedPatternKind::Variant {
                        enum_name: Some(nominal_sym),
                        variant_name: variant_label.to_string(),
                        variant_name_span: Span::SYNTHESIZED,
                        fields: bind_patterns,
                    },
                };

                // Build "TypeName.variant(" + v0.show() + ", " + v1.show() + ... + ")"
                let mut parts: Vec<TypedExpr> = vec![];
                parts.push(self.synth_string_literal(&format!("{type_name}.{variant_label}(")));

                for (j, (bind_sym, payload_ty)) in bind_syms.iter().enumerate() {
                    if j > 0 {
                        parts.push(self.synth_string_literal(", "));
                    }
                    let var = TypedExpr {
                        id: NodeID::SYNTHESIZED,
                        ty: payload_ty.clone(),
                        kind: TypedExprKind::Variable(*bind_sym),
                    };

                    if matches!(payload_ty, Ty::Func(..)) {
                        parts.push(self.synth_func_type_literal(payload_ty));
                    } else {
                        let show_witness = self.find_show_witness_for_ty(payload_ty, showable_id);
                        parts.push(self.synth_show_call(var, show_witness, showable_id));
                    }
                }
                parts.push(self.synth_string_literal(")"));

                let body_expr = self.synth_string_concat(parts, string_add_witness);
                arms.push(TypedMatchArm {
                    pattern,
                    body: TypedBlock {
                        id: NodeID::SYNTHESIZED,
                        body: vec![TypedNode::Expr(body_expr)],
                        ret: Ty::String(),
                    },
                });
            }
        }

        TypedExpr {
            id: NodeID::SYNTHESIZED,
            ty: Ty::String(),
            kind: TypedExprKind::Match(self_var.into(), arms),
        }
    }

    fn synth_string_literal(&self, s: &str) -> TypedExpr {
        TypedExpr {
            id: NodeID::SYNTHESIZED,
            ty: Ty::String(),
            kind: TypedExprKind::LiteralString(s.into()),
        }
    }

    fn synth_func_type_literal(&self, ty: &Ty) -> TypedExpr {
        use crate::types::format::{SymbolNames, TypeFormatter};
        let imported = self.session.modules.imported_symbol_names();
        let formatter = TypeFormatter::new(SymbolNames::new(
            Some(&self.session.resolved_names.symbol_names),
            Some(&imported),
        ));
        self.synth_string_literal(&formatter.format_ty_for_show(ty))
    }

    /// Generate a `.show()` call on `receiver`, using the resolved witness symbol if available.
    fn synth_show_call(
        &self,
        mut receiver: TypedExpr,
        show_witness: Option<Symbol>,
        showable_id: Option<ProtocolId>,
    ) -> TypedExpr {
        match show_witness {
            Some(witness_sym) => {
                // Pre-resolved: emit Call { callee: Variable(witness), args: [receiver] }
                // Full method type: Func(Self, Func(Void, String, Empty), Empty)
                let method_ty = Ty::Func(
                    receiver.ty.clone().into(),
                    Ty::Func(Ty::Void.into(), Ty::String().into(), Row::Empty.into()).into(),
                    Row::Empty.into(),
                );
                let callee = TypedExpr {
                    id: NodeID::SYNTHESIZED,
                    ty: method_ty.clone(),
                    kind: TypedExprKind::Variable(witness_sym),
                };
                TypedExpr {
                    id: NodeID::SYNTHESIZED,
                    ty: Ty::String(),
                    kind: TypedExprKind::Call {
                        callee: callee.into(),
                        callee_ty: method_ty,
                        type_args: vec![],
                        args: vec![receiver],
                        callee_sym: Some(witness_sym),
                    },
                }
            }
            None => {
                // For type parameters, add Showable bound so the lowerer emits a
                // MethodRequirement that the monomorphizer resolves at instantiation time.
                if let Ty::Param(_, ref mut bounds) = receiver.ty
                    && let Some(sid) = showable_id
                        && !bounds.contains(&sid) {
                            bounds.push(sid);
                        }

                // Fallback: emit Member + Call (for types we can't resolve yet)
                let show_method = TypedExpr {
                    id: NodeID::SYNTHESIZED,
                    ty: Ty::Func(Ty::Void.into(), Ty::String().into(), Row::Empty.into()),
                    kind: TypedExprKind::Member {
                        receiver: receiver.into(),
                        label: "show".into(),
                        label_span: Span::SYNTHESIZED,
                    },
                };
                TypedExpr {
                    id: NodeID::SYNTHESIZED,
                    ty: Ty::String(),
                    kind: TypedExprKind::Call {
                        callee: show_method.into(),
                        callee_ty: Ty::Func(
                            Ty::Void.into(),
                            Ty::String().into(),
                            Row::Empty.into(),
                        ),
                        type_args: vec![],
                        args: vec![],
                        callee_sym: None,
                    },
                }
            }
        }
    }

    /// Find the Showable.show witness symbol for a given type.
    fn find_show_witness_for_ty(
        &mut self,
        ty: &Ty,
        showable_id: Option<ProtocolId>,
    ) -> Option<Symbol> {
        let showable_id = showable_id?;
        let show_label: Label = "show".into();
        let conforming_sym = match ty {
            Ty::Primitive(sym) => *sym,
            Ty::Nominal { symbol, .. } => *symbol,
            _ => return None,
        };
        self.session
            .find_witness(conforming_sym, showable_id, &show_label)
    }

    fn synth_string_concat(&self, parts: Vec<TypedExpr>, add_witness: Option<Symbol>) -> TypedExpr {
        let mut result = parts.into_iter();
        let mut acc = result
            .next()
            .unwrap_or_else(|| self.synth_string_literal(""));
        for part in result {
            match add_witness {
                Some(witness_sym) => {
                    // Pre-resolved: emit Call { callee: Variable(witness), args: [acc, part] }
                    // Full method type: Func(Self=String, Func(RHS=String, Ret=String, Empty), Empty)
                    let method_ty = Ty::Func(
                        Ty::String().into(),
                        Ty::Func(Ty::String().into(), Ty::String().into(), Row::Empty.into())
                            .into(),
                        Row::Empty.into(),
                    );
                    let callee = TypedExpr {
                        id: NodeID::SYNTHESIZED,
                        ty: method_ty.clone(),
                        kind: TypedExprKind::Variable(witness_sym),
                    };
                    acc = TypedExpr {
                        id: NodeID::SYNTHESIZED,
                        ty: Ty::String(),
                        kind: TypedExprKind::Call {
                            callee: callee.into(),
                            callee_ty: method_ty,
                            type_args: vec![],
                            args: vec![acc, part],
                            callee_sym: Some(witness_sym),
                        },
                    };
                }
                None => {
                    // Fallback
                    let add_method = TypedExpr {
                        id: NodeID::SYNTHESIZED,
                        ty: Ty::Func(Ty::String().into(), Ty::String().into(), Row::Empty.into()),
                        kind: TypedExprKind::Member {
                            receiver: acc.into(),
                            label: "add".into(),
                            label_span: Span::SYNTHESIZED,
                        },
                    };
                    acc = TypedExpr {
                        id: NodeID::SYNTHESIZED,
                        ty: Ty::String(),
                        kind: TypedExprKind::Call {
                            callee: add_method.into(),
                            callee_ty: Ty::Func(
                                Ty::String().into(),
                                Ty::String().into(),
                                Row::Empty.into(),
                            ),
                            type_args: vec![],
                            args: vec![part],
                            callee_sym: None,
                        },
                    };
                }
            }
        }
        acc
    }
}
