use derive_visitor::{DriveMut, VisitorMut};
use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::{name_resolver::ResolvedNames, symbol::{ProtocolId, Symbol}},
    node_id::NodeID,
    types::{
        conformance::ConformanceKey,
        ty::Ty,
        type_error::TypeError,
        typed_ast::{TypedAST, TypedExpr, TypedExprKind},
        types::Types,
        variational::{AlternativeIndex, ChoiceAlternative, DimensionId},
    },
};

type TypedExprTy = TypedExpr<Ty>;

#[derive(VisitorMut)]
#[visitor(TypedExprTy(enter, exit))]
pub struct WitnessResolutionPass {
    ast: TypedAST<Ty>,
    types: Types,
    resolved_names: ResolvedNames,
    protocol_members: FxHashMap<NodeID, Symbol>,
}

impl WitnessResolutionPass {
    pub fn new(
        ast: TypedAST<Ty>,
        types: Types,
        resolved_names: ResolvedNames,
        protocol_members: FxHashMap<NodeID, Symbol>,
    ) -> Self {
        Self {
            ast,
            types,
            resolved_names,
            protocol_members,
        }
    }

    /// Register variational choices for protocol method resolution.
    /// For each conformance to the protocol, register the witness as an alternative.
    fn register_protocol_method_choices(
        &mut self,
        callee_id: NodeID,
        protocol_id: ProtocolId,
        method_req: Symbol,
        label: &Label,
    ) {
        let dimension = DimensionId(callee_id);

        // Find all conformances to this protocol and register each as an alternative
        let conformances: Vec<_> = self
            .types
            .catalog
            .conformances
            .iter()
            .filter(|(key, _)| key.protocol_id == protocol_id)
            .map(|(key, conf)| (key.conforming_id, conf.witnesses.clone()))
            .collect();

        for (i, (conforming_id, witnesses)) in conformances.iter().enumerate() {
            // Get the witness method - first try by label, then by method requirement
            let witness_sym = witnesses
                .methods
                .get(label)
                .copied()
                .or_else(|| witnesses.requirements.get(&method_req).copied());

            if let Some(witness) = witness_sym {
                let alternative = ChoiceAlternative {
                    conforming_type: *conforming_id,
                    witness_sym: witness,
                    protocol_id,
                };

                self.types.choices.register_alternative(
                    dimension,
                    AlternativeIndex(i),
                    alternative,
                );
            }
        }
    }

    pub fn drive(mut self) -> Result<(TypedAST<Ty>, Types, ResolvedNames), TypeError> {
        let mut stmts = std::mem::take(&mut self.ast.stmts);
        let mut decls = std::mem::take(&mut self.ast.decls);

        for stmt in stmts.iter_mut() {
            stmt.drive_mut(&mut self);
        }

        for decl in decls.iter_mut() {
            decl.drive_mut(&mut self);
        }

        Ok((TypedAST { stmts, decls }, self.types, self.resolved_names))
    }

    fn enter_typed_expr_ty(&mut self, expr: &mut TypedExpr<Ty>) {
        if let TypedExprKind::Call { callee, args, .. } = &mut expr.kind {
            let (receiver, label) = match &callee.kind {
                TypedExprKind::Member { receiver, label } => (receiver.clone(), label.clone()),
                _ => return,
            };

            let receiver_expr = (*receiver).clone();
            let should_insert_receiver =
                !matches!(receiver_expr.kind, TypedExprKind::Constructor(..));

            if let Some(req_sym) = self.protocol_members.get(&callee.id).copied() {
                // Insert receiver as first arg if needed (it becomes the self parameter)
                if should_insert_receiver {
                    args.insert(0, receiver_expr.clone());
                }

                // Get the conforming type from the first argument (self)
                let Some(self_arg) = args.first() else {
                    callee.kind = TypedExprKind::Variable(req_sym);
                    return;
                };

                // Find the protocol for this method requirement
                let Some(protocol_sym) =
                    self.types.catalog.protocol_for_method_requirement(&req_sym)
                else {
                    callee.kind = TypedExprKind::Variable(req_sym);
                    return;
                };

                let Symbol::Protocol(protocol_id) = protocol_sym else {
                    callee.kind = TypedExprKind::Variable(req_sym);
                    return;
                };

                let Ok(conforming_sym) = self.symbol_from_ty(&self_arg.ty) else {
                    // Can't determine conforming type (e.g., type param)
                    // Register choices for variational resolution
                    self.register_protocol_method_choices(callee.id, protocol_id, req_sym, &label);
                    callee.kind = TypedExprKind::Variable(req_sym);
                    return;
                };

                // Look up the witness from the conformance
                let key = ConformanceKey {
                    protocol_id,
                    conforming_id: conforming_sym,
                };

                if let Some(conformance) = self.types.catalog.conformances.get(&key) {
                    // Try both methods (by label) and requirements (by symbol)
                    let witness = conformance
                        .witnesses
                        .methods
                        .get(&label)
                        .copied()
                        .or_else(|| conformance.witnesses.requirements.get(&req_sym).copied());

                    if let Some(witness) = witness {
                        callee.kind = TypedExprKind::Variable(witness);
                    } else {
                        // Fall back to method requirement if witness not found
                        callee.kind = TypedExprKind::Variable(req_sym);
                    }
                } else {
                    // Fall back to method requirement if conformance not found
                    callee.kind = TypedExprKind::Variable(req_sym);
                }
                return;
            }

            let TypedExprKind::Constructor(protocol_sym @ Symbol::Protocol(_), _) =
                &receiver_expr.kind
            else {
                return;
            };

            let Some(member_sym) = self
                .types
                .catalog
                .lookup_member(protocol_sym, &label)
                .map(|s| s.0)
            else {
                return;
            };

            if matches!(member_sym, Symbol::InstanceMethod(_)) {
                return;
            }

            let Some(self_arg) = args.first() else {
                return;
            };

            let Ok(conforming_sym) = self.symbol_from_ty(&self_arg.ty) else {
                tracing::error!("no conforming sym found: {self_arg:?}");
                return;
            };

            let Symbol::Protocol(protocol_id) = protocol_sym else {
                return Default::default();
            };

            let key = ConformanceKey {
                protocol_id: *protocol_id,
                conforming_id: conforming_sym,
            };
            let Some(reqs) = self
                .types
                .catalog
                .conformances
                .get(&key)
                .map(|c| &c.witnesses.requirements)
            else {
                return;
            };

            if let Some(witness) = reqs.get(&member_sym) {
                callee.kind = TypedExprKind::Variable(*witness);
                if should_insert_receiver {
                    args.insert(0, receiver_expr);
                }
            }
        }
    }

    fn exit_typed_expr_ty(&mut self, _expr: &mut TypedExpr<Ty>) {
        // println!("{expr:?}");
    }

    fn symbol_from_ty(&self, ty: &Ty) -> Result<Symbol, TypeError> {
        match ty {
            Ty::Primitive(sym) => Ok(*sym),
            Ty::Nominal { symbol, .. } => Ok(*symbol),
            Ty::Constructor { name, .. } => Ok(name.symbol().unwrap_or_else(|_| unreachable!())),
            _ => Err(TypeError::TypeNotFound(format!(
                "could not determine receiver: {ty:?}",
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        assert_eq_diff,
        name::Name,
        name_resolution::symbol::{InitializerId, StructId, Symbol, SynthesizedId},
        node_id::NodeID,
        types::{
            row::Row,
            ty::Ty,
            typed_ast::{TypedExpr, TypedExprKind, TypedStmtKind},
            types_tests::tests::typecheck,
        },
    };

    #[test]
    fn rewrites_callers_of_witnesses() {
        let (ast, _types) = typecheck(
            "
      protocol A {
        func fizz() -> Int
      }

      struct B {}
      extend B: A {
        init() { }

        func fizz() { 123 }
      }

      func callIt<T: A>(t: T) {
        t.fizz()
      }

      callIt(B())
    ",
        );

        assert_eq_diff!(
            ast.stmts[0].kind,
            TypedStmtKind::Expr(TypedExpr {
                id: NodeID::ANY,
                ty: Ty::Int,
                kind: TypedExprKind::Call {
                    callee: TypedExpr {
                        id: NodeID::ANY,
                        ty: Ty::Func(
                            Ty::Nominal {
                                symbol: StructId::from(1).into(),
                                type_args: vec![]
                            }
                            .into(),
                            Ty::Int.into(),
                            Row::Param(3.into()).into()
                        ),
                        kind: TypedExprKind::Variable(Symbol::Synthesized(SynthesizedId::from(2)))
                    }
                    .into(),
                    callee_ty: Ty::Func(
                        Ty::Param(2.into(), vec![]).into(),
                        Ty::Int.into(),
                        Row::Param(3.into()).into()
                    ),
                    type_args: vec![Ty::Nominal {
                        symbol: StructId::from(1).into(),
                        type_args: vec![]
                    }],
                    args: vec![TypedExpr {
                        id: NodeID::ANY,
                        ty: Ty::Nominal {
                            symbol: StructId::from(1).into(),
                            type_args: vec![]
                        },
                        kind: TypedExprKind::Call {
                            callee: TypedExpr {
                                id: NodeID::ANY,
                                ty: Ty::Constructor {
                                    name: Name::Resolved(StructId::from(1).into(), "B".into()),
                                    params: vec![],
                                    ret: Ty::Nominal {
                                        symbol: StructId::from(1).into(),
                                        type_args: vec![]
                                    }
                                    .into()
                                },
                                kind: TypedExprKind::Constructor(
                                    StructId::from(1).into(),
                                    Default::default()
                                )
                            }
                            .into(),
                            callee_ty: Ty::Func(
                                Ty::Nominal {
                                    symbol: StructId::from(1).into(),
                                    type_args: vec![]
                                }
                                .into(),
                                Ty::Nominal {
                                    symbol: StructId::from(1).into(),
                                    type_args: vec![]
                                }
                                .into(),
                                Row::Empty.into()
                            ),
                            type_args: vec![],
                            args: vec![],
                            callee_sym: Some(InitializerId::from(1).into())
                        }
                    }],
                    callee_sym: Some(Symbol::Synthesized(SynthesizedId::from(3)))
                }
            })
        );
    }
}
