//! Synthesized value glue: shared drop/retain functions, `'heap`
//! finalizers, checker-derived `Showable`/`Equatable` bodies, and
//! protocol requirement thunks.

use super::*;

impl<'a> ProgramBuilder<'a> {
    /// A one-parameter chunk that drops (or retains) a value of the given
    /// concrete type: an existential's fixed-slot witnesses.
    /// The finalizer chunk for a `'heap` struct, or None when it needs
    /// none: the user's Deinit hook runs first, then buffer-owning
    /// fields free (the region walk frees the object slots themselves;
    /// handle-carrying fields belong to their own objects' finalizers).
    pub(super) fn heap_teardown(&mut self, ty: &Ty) -> Result<Option<FuncId>, BackendError> {
        let Ty::Nominal(symbol, args) = ty else {
            return Ok(None);
        };
        let deinit = self.deinit_witness(*symbol, args);
        let fields = self.field_types(*symbol, args).unwrap_or_default();
        let droppable: Vec<(usize, Ty)> = fields
            .iter()
            .enumerate()
            .filter(|(_, field)| {
                !matches!(field, Ty::Borrow(_, _))
                    && contains_buffer(self, field)
                    && !contains_object(self, field)
            })
            .map(|(index, field)| (index, field.clone()))
            .collect();
        if deinit.is_none() && droppable.is_empty() {
            return Ok(None);
        }
        if let Some(id) = self.glue.get(&(ty.clone(), Glue::HeapTeardown)) {
            return Ok(Some(*id));
        }
        let id = self.reserve("heap_teardown");
        self.glue.insert((ty.clone(), Glue::HeapTeardown), id);
        let mut fx = FunctionBuilder::new(self, 0, 0);
        fx.next_local = 1;
        if let Some((witness, subst)) = deinit {
            let func = fx
                .program_builder
                .demand(witness, subst, Span::SYNTHESIZED)?;
            let dest = fx.fresh_local();
            fx.push(Inst::Call {
                dest,
                func,
                args: vec![Operand::Local(0)],
                unwind: None,
            });
        }
        for (index, field_ty) in droppable {
            let field = fx.fresh_local();
            fx.push(Inst::ObjectGet {
                dest: field,
                src: Operand::Local(0),
                index: u16::try_from(index).unwrap_or_default(),
            });
            fx.drop_value(Operand::Local(field), &field_ty);
        }
        let (n_locals, blocks) = fx.finish(Operand::Const(Constant::Unit))?;
        self.functions[id] = Function {
            name: "heap_teardown".into(),
            arity: 1,
            n_locals,
            blocks,
        };
        Ok(Some(id))
    }

    pub(super) fn value_glue(&mut self, ty: &Ty, glue: Glue) -> Result<FuncId, BackendError> {
        if let Some(id) = self.glue.get(&(ty.clone(), glue)) {
            return Ok(*id);
        }
        let id = self.reserve(match glue {
            Glue::Drop => "shared_drop",
            Glue::Retain => "existential_retain",
            Glue::HeapTeardown => unreachable!("heap teardown has its own builder"),
        });
        self.glue.insert((ty.clone(), glue), id);
        let mut fx = FunctionBuilder::new(self, 0, 0);
        fx.next_local = 1;
        // Glue over a type that mentions rigid effect-generics reads their
        // witnesses from its closure environment, in the order
        // `glue_witness_params` reports (the MakeClosure site captures the
        // same list).
        for (index, param_symbol) in glue_witness_params(ty).iter().enumerate() {
            let drop_local = fx.fresh_local();
            fx.push(Inst::EnvGet {
                dest: drop_local,
                index: u16::try_from(2 * index).unwrap_or_default(),
            });
            let retain_local = fx.fresh_local();
            fx.push(Inst::EnvGet {
                dest: retain_local,
                index: u16::try_from(2 * index + 1).unwrap_or_default(),
            });
            fx.param_witnesses
                .insert(*param_symbol, (drop_local, retain_local));
        }
        match glue {
            Glue::HeapTeardown => unreachable!("heap teardown has its own builder"),
            Glue::Drop => {
                fx.drop_glue_root = Some(ty.clone());
                fx.drop_value(Operand::Local(0), ty);
            }
            Glue::Retain => {
                let mut retained = ty.clone();
                while let Ty::Borrow(_, inner) = retained {
                    retained = *inner;
                }
                fx.retain_value(Operand::Local(0), &retained, Span::SYNTHESIZED)?;
            }
        }
        let (n_locals, blocks) = fx.finish(Operand::Const(Constant::Unit))?;
        self.functions[id] = Function {
            name: match glue {
                Glue::HeapTeardown => unreachable!("heap teardown has its own builder"),
                Glue::Drop => "shared_drop".into(),
                Glue::Retain => "existential_retain".into(),
            },
            arity: 1,
            n_locals,
            blocks,
        };
        Ok(id)
    }
}

impl<'p, 'a> FunctionBuilder<'p, 'a> {
    /// The derived rendering: enums as `Name.variant(payloads…)`, structs
    /// as `Name(field: value…)` (`Name {}` when fieldless) — the archived
    /// synthesis format.
    pub(super) fn emit_show(
        &mut self,
        value: Operand,
        ty: &Ty,
        protocol: &crate::types::ty::ProtocolRef,
        span: Span,
    ) -> Result<Operand, BackendError> {
        let Ty::Nominal(symbol, args) = ty else {
            return Err(BackendError::unsupported(
                "derived show on this type is not supported yet".into(),
                span,
            ));
        };
        let type_name = self.program_builder.display_name(*symbol);
        if let (Some(payloads), Some(names)) = (
            self.program_builder.variant_payloads(*symbol, args),
            self.program_builder.variant_names(*symbol),
        ) {
            let out = self.fresh_local();
            let done = self.new_block();
            let tag = self.fresh_local();
            self.push(Inst::GetTag {
                dest: tag,
                src: value,
            });
            let last = payloads.len().saturating_sub(1);
            for (variant_tag, (payload_tys, name)) in payloads.iter().zip(&names).enumerate() {
                let arm = self.new_block();
                let next = self.new_block();
                if variant_tag == last {
                    self.terminate(Term::Goto(arm, Vec::new()));
                } else {
                    self.branch_if_equal(
                        ScalarOp::IntCmp(CmpKind::Eq),
                        Operand::Local(tag),
                        Operand::Const(Constant::Int(
                            i64::try_from(variant_tag).unwrap_or_default(),
                        )),
                        arm,
                        next,
                    );
                }
                self.switch_to(arm);
                let mut acc = if payload_tys.is_empty() {
                    self.emit_string_lit(&format!("{type_name}.{name}"))
                } else {
                    self.emit_string_lit(&format!("{type_name}.{name}("))
                };
                for (index, payload_ty) in payload_tys.iter().enumerate() {
                    if index > 0 {
                        let comma = self.emit_string_lit(", ");
                        acc = self.emit_string_concat(acc, comma, span)?;
                    }
                    let payload = self.fresh_local();
                    self.push(Inst::GetPayload {
                        dest: payload,
                        src: value,
                        index: u16::try_from(index).unwrap_or_default(),
                    });
                    let rendered =
                        self.emit_sub_show(Operand::Local(payload), payload_ty, protocol, span)?;
                    acc = self.emit_string_concat(acc, rendered, span)?;
                }
                if !payload_tys.is_empty() {
                    let close = self.emit_string_lit(")");
                    acc = self.emit_string_concat(acc, close, span)?;
                }
                self.push(Inst::Copy {
                    dest: out,
                    src: acc,
                });
                self.terminate(Term::Goto(done, Vec::new()));
                self.switch_to(next);
            }
            // The chain's trailing block is unreachable (the last variant
            // falls through to its arm above).
            self.terminate(Term::Goto(done, Vec::new()));
            self.switch_to(done);
            return Ok(Operand::Local(out));
        }
        if let (Some(field_tys), Some(names)) = (
            self.program_builder.field_types(*symbol, args),
            self.program_builder.field_names(*symbol),
        ) {
            if field_tys.is_empty() {
                return Ok(self.emit_string_lit(&format!("{type_name} {{}}")));
            }
            let mut acc = self.emit_string_lit("");
            for (index, (field_ty, name)) in field_tys.iter().zip(&names).enumerate() {
                let prefix = if index == 0 {
                    self.emit_string_lit(&format!("{type_name}({name}: "))
                } else {
                    self.emit_string_lit(&format!(", {name}: "))
                };
                acc = self.emit_string_concat(acc, prefix, span)?;
                let field = self.fresh_local();
                self.push(Inst::GetField {
                    dest: field,
                    src: value,
                    index: u16::try_from(index).unwrap_or_default(),
                });
                let rendered =
                    self.emit_sub_show(Operand::Local(field), field_ty, protocol, span)?;
                acc = self.emit_string_concat(acc, rendered, span)?;
            }
            let close = self.emit_string_lit(")");
            let result = self.emit_string_concat(acc, close, span)?;
            return Ok(result);
        }
        Err(BackendError::unsupported(
            "derived show on this type is not supported yet".into(),
            span,
        ))
    }

    /// Tags equal, then payload-wise equality in the matching variant's
    /// arm.
    pub(super) fn emit_enum_equality(
        &mut self,
        a: Operand,
        b: Operand,
        payloads: Vec<Vec<Ty>>,
        protocol: &crate::types::ty::ProtocolRef,
        span: Span,
    ) -> Result<Operand, BackendError> {
        let result = self.fresh_local();
        let fail = self.new_block();
        let done = self.new_block();
        let tag_a = self.fresh_local();
        self.push(Inst::GetTag {
            dest: tag_a,
            src: a,
        });
        let tag_b = self.fresh_local();
        self.push(Inst::GetTag {
            dest: tag_b,
            src: b,
        });
        let tags_equal = self.fresh_local();
        self.push(Inst::Scalar {
            dest: tags_equal,
            op: ScalarOp::IntCmp(CmpKind::Eq),
            a: Operand::Local(tag_a),
            b: Some(Operand::Local(tag_b)),
        });
        let tags_ok = self.new_block();
        self.terminate(Term::Branch {
            cond: Operand::Local(tags_equal),
            then_block: tags_ok,
            else_block: fail,
        });
        self.switch_to(tags_ok);
        // Dispatch payload comparison per variant that carries any.
        for (variant_tag, payload_tys) in payloads.iter().enumerate() {
            if payload_tys.is_empty() {
                continue;
            }
            let arm = self.new_block();
            let next = self.new_block();
            self.branch_if_equal(
                ScalarOp::IntCmp(CmpKind::Eq),
                Operand::Local(tag_a),
                Operand::Const(Constant::Int(
                    i64::try_from(variant_tag).unwrap_or_default(),
                )),
                arm,
                next,
            );
            self.switch_to(arm);
            for (index, payload_ty) in payload_tys.iter().enumerate() {
                let pa = self.fresh_local();
                self.push(Inst::GetPayload {
                    dest: pa,
                    src: a,
                    index: u16::try_from(index).unwrap_or_default(),
                });
                let pb = self.fresh_local();
                self.push(Inst::GetPayload {
                    dest: pb,
                    src: b,
                    index: u16::try_from(index).unwrap_or_default(),
                });
                let equal = self.emit_equality(
                    Operand::Local(pa),
                    Operand::Local(pb),
                    payload_ty,
                    protocol,
                    span,
                )?;
                let payload_next = self.new_block();
                self.terminate(Term::Branch {
                    cond: equal,
                    then_block: payload_next,
                    else_block: fail,
                });
                self.switch_to(payload_next);
            }
            self.push(Inst::Copy {
                dest: result,
                src: Operand::Const(Constant::Bool(true)),
            });
            self.terminate(Term::Goto(done, Vec::new()));
            self.switch_to(next);
        }
        self.push(Inst::Copy {
            dest: result,
            src: Operand::Const(Constant::Bool(true)),
        });
        self.terminate(Term::Goto(done, Vec::new()));
        self.switch_to(fail);
        self.push(Inst::Copy {
            dest: result,
            src: Operand::Const(Constant::Bool(false)),
        });
        self.terminate(Term::Goto(done, Vec::new()));
        self.switch_to(done);
        Ok(Operand::Local(result))
    }

    /// One requirement's implementation closure for a concrete payload
    /// type — conformance row first, protocol default second (the same
    /// selection existential packs use).
    pub(super) fn requirement_closure(
        &mut self,
        payload_ty: &Ty,
        protocol: &crate::types::ty::ProtocolRef,
        name: &str,
        span: Span,
    ) -> Result<Operand, BackendError> {
        let label = crate::label::Label::Named(name.to_string());
        let (implementation, mut subst) = match self
            .program_builder
            .generated_conformance_witness(payload_ty, protocol, &label)
        {
            Some(found) => found,
            None if (name == "equals" || name == "show")
                && self
                    .program_builder
                    .requirement_symbol(protocol.protocol, name)
                    .is_some_and(|requirement| {
                        !self.program_builder.callables.contains_key(&requirement)
                    }) =>
            {
                // Derived structural conformance: synthesize the chunk
                // and wrap it directly.
                let glue = if name == "show" {
                    self.program_builder
                        .derived_show(payload_ty, protocol, span)?
                } else {
                    self.program_builder
                        .derived_equality(payload_ty, protocol, span)?
                };
                let closure = self.fresh_local();
                self.push(Inst::MakeClosure {
                    dest: closure,
                    func: glue,
                    env: Vec::new(),
                });
                return Ok(Operand::Local(closure));
            }
            None => {
                let mut subst = vec![(protocol.protocol, payload_ty.clone())];
                if let Some(params) = self.program_builder.protocol_params(protocol.protocol) {
                    for (param, arg) in params.iter().zip(&protocol.args) {
                        subst.push((*param, arg.clone()));
                    }
                }
                subst.extend(self.program_builder.conformance_assoc(payload_ty, protocol));
                let requirement = self
                    .program_builder
                    .requirement_symbol(protocol.protocol, name)
                    .ok_or_else(|| {
                        BackendError::unsupported(
                            "existential requirement without an implementation is not supported yet"
                                .into(),
                            span,
                        )
                    })?;
                (requirement, subst)
            }
        };
        subst.push((protocol.protocol, payload_ty.clone()));
        // The closure calls its chunk directly: an instance with hidden
        // parameters of its own would break that arity contract.
        if !witness_params(&subst).is_empty() {
            return Err(BackendError::unsupported(
                "conformance evidence for compound rigid payloads is not supported yet".into(),
                span,
            ));
        }
        let func = self.program_builder.demand(implementation, subst, span)?;
        // The declared requirement fixes the writeback shape every
        // implementation must follow.
        let declared: usize = self
            .program_builder
            .programs
            .iter()
            .find_map(|input| {
                input
                    .program
                    .types()
                    .schemes
                    .iter()
                    .find_map(|(symbol, scheme)| {
                        (canonical(*symbol, input.module)
                            == self
                                .program_builder
                                .requirement_symbol(protocol.protocol, name)
                                .unwrap_or(*symbol))
                        .then(|| match &scheme.ty {
                            Ty::Func(params, _, _) => params
                                .iter()
                                .filter(|param| matches!(param, Ty::Borrow(Perm::Exclusive, _)))
                                .count(),
                            _ => 0,
                        })
                    })
            })
            .unwrap_or(0);
        self.program_builder
            .writeback_expectations
            .push((func, declared, span));
        let closure = self.fresh_local();
        self.push(Inst::MakeClosure {
            dest: closure,
            func,
            env: Vec::new(),
        });
        Ok(Operand::Local(closure))
    }

    /// A `[drop]`/`[retain]` glue closure for a value type, capturing the
    /// witnesses for any rigid effect-generics the type mentions from this
    /// frame's environment.
    pub(super) fn glue_closure(
        &mut self,
        ty: &Ty,
        glue: Glue,
        span: Span,
    ) -> Result<Operand, BackendError> {
        let func = self.program_builder.value_glue(ty, glue)?;
        let mut env = Vec::new();
        for param in glue_witness_params(ty) {
            let Some((drop_witness, retain_witness)) = self.param_witnesses.get(&param).copied()
            else {
                return Err(BackendError::unsupported(
                    "a generic value cannot cross this boundary without its ownership witnesses (not supported yet)"
                        .into(),
                    span,
                ));
            };
            env.push(Operand::Local(drop_witness));
            env.push(Operand::Local(retain_witness));
        }
        let dest = self.fresh_local();
        self.push(Inst::MakeClosure { dest, func, env });
        Ok(Operand::Local(dest))
    }
}
