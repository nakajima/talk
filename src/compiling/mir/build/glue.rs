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
        fx.frame.resize(1, Default::default());
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
        let (n_locals, blocks, _return_repr) = fx.finish(Operand::Const(Constant::Unit))?;
        self.functions[id] = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "heap_teardown".into(),
            arity: 1,
            locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
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
        fx.frame.resize(1, Default::default());
        // Glue over a type that mentions rigid effect-generics reads their
        // full witness blocks from its closure environment — the
        // `[drop, retain]` pair plus each bound protocol's requirement
        // dictionaries, in the order `glue_witness_params` reports (the
        // MakeClosure sites capture the same blocks via
        // `push_witness_block`). The dictionaries let the glue body call
        // instances whose hidden arguments include them (a compound rigid
        // payload's deinit, for example).
        let mut env_index: u16 = 0;
        for param_symbol in glue_witness_params(ty) {
            let drop_local = fx.fresh_local();
            fx.push(Inst::EnvGet {
                dest: drop_local,
                index: env_index,
            });
            let retain_local = fx.fresh_local();
            fx.push(Inst::EnvGet {
                dest: retain_local,
                index: env_index + 1,
            });
            env_index += 2;
            fx.param_witnesses
                .insert(param_symbol, (drop_local, retain_local));
            for protocol in fx.program_builder.rigid_constraints(param_symbol) {
                let count = fx
                    .program_builder
                    .protocol_requirements(protocol.protocol)
                    .map(|requirements| requirements.len())
                    .unwrap_or(0);
                let mut locals = Vec::new();
                for _ in 0..count {
                    let local = fx.fresh_local();
                    fx.push(Inst::EnvGet {
                        dest: local,
                        index: env_index,
                    });
                    env_index += 1;
                    locals.push(local);
                }
                fx.param_requirements
                    .insert((param_symbol, protocol.protocol), locals);
            }
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
        let (n_locals, blocks, _return_repr) = fx.finish(Operand::Const(Constant::Unit))?;
        // The glue's one parameter is the value itself, at its published
        // layout: scope-exit drops of native locals then pass the struct
        // straight in instead of boxing at every death.
        let layout = self.layouts.borrow_mut().id_of(ty);
        self.functions[id] = Function {
            frame_sites: Default::default(),
            param_reprs: vec![layout::ParamRepr::Value(layout)],
            return_repr: None,
            name: match glue {
                Glue::HeapTeardown => unreachable!("heap teardown has its own builder"),
                Glue::Drop => "shared_drop".into(),
                Glue::Retain => "existential_retain".into(),
            },
            arity: 1,
            locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
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
        let container = self.container_layout(ty);
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
                    self.push_field(payload, value, container, u16::try_from(index).unwrap_or_default(), Some(u16::try_from(variant_tag).unwrap_or_default()));
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
                self.push_field(field, value, container, u16::try_from(index).unwrap_or_default(), None);
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
        ty: &Ty,
        payloads: Vec<Vec<Ty>>,
        protocol: &crate::types::ty::ProtocolRef,
        span: Span,
    ) -> Result<Operand, BackendError> {
        let container = self.container_layout(ty);
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
                self.push_field(pa, a, container, u16::try_from(index).unwrap_or_default(), Some(u16::try_from(variant_tag).unwrap_or_default()));
                let pb = self.fresh_local();
                self.push_field(pb, b, container, u16::try_from(index).unwrap_or_default(), Some(u16::try_from(variant_tag).unwrap_or_default()));
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

    /// One committed dictionary entry's implementation closure for a
    /// concrete payload type (ADR 0038): demand the committed callable,
    /// or synthesize the derived structural glue. Selection happened at
    /// typing — nothing here searches rows or guesses by name.
    pub(super) fn requirement_closure(
        &mut self,
        payload_ty: &Ty,
        protocol: &crate::types::ty::ProtocolRef,
        entry: &crate::types::catalog::DictionaryEntry,
        subst: &[(Symbol, Ty)],
        span: Span,
    ) -> Result<Operand, BackendError> {
        use crate::types::catalog::{DerivedRecipe, DictionaryEntry};
        let (func, env) = match entry {
            DictionaryEntry::Derived(DerivedRecipe::Show) => (
                self.program_builder
                    .derived_show(payload_ty, protocol, span)?,
                Vec::new(),
            ),
            DictionaryEntry::Derived(DerivedRecipe::Equality) => (
                self.program_builder
                    .derived_equality(payload_ty, protocol, span)?,
                Vec::new(),
            ),
            DictionaryEntry::Implementation {
                symbol,
                writeback_width,
            } => {
                let mut subst = subst.to_vec();
                subst.push((protocol.protocol, payload_ty.clone()));
                let func = self.program_builder.demand(*symbol, subst, span)?;
                self.program_builder
                    .writeback_expectations
                    .push((func, *writeback_width, span));
                // A compound rigid payload's instance takes hidden
                // witness arguments. The dictionary's arity contract
                // stays at the requirement's visible arity: a forwarding
                // chunk passes the parameters through and appends the
                // evidence from its environment, which captures this
                // frame's witness blocks (the same layout `glue_closure`
                // uses).
                let hidden = self
                    .program_builder
                    .instance_witnesses
                    .get(&func)
                    .cloned()
                    .unwrap_or_default();
                if hidden.is_empty() {
                    (func, Vec::new())
                } else {
                    let visible = self
                        .program_builder
                        .callables
                        .get(symbol)
                        .map(|callable| match callable.body {
                            crate::compiling::mir::build::CallableBody::Func(func) => func.params.len(),
                            crate::compiling::mir::build::CallableBody::Init { params, .. } => params.len(),
                        })
                        .unwrap_or(0);
                    let visible = u16::try_from(visible).unwrap_or_default();
                    let forwarder = self.requirement_forwarder(func, visible, &hidden);
                    let mut env = Vec::new();
                    for param in &hidden {
                        self.push_witness_block(*param, &mut env, span)?;
                    }
                    (forwarder, env)
                }
            }
        };
        let closure = self.fresh_local();
        self.push(Inst::MakeClosure {
            dest: closure,
            func,
            env,
        });
        Ok(Operand::Local(closure))
    }

    /// A forwarding chunk for a requirement implementation with hidden
    /// witness arguments: visible parameters pass straight through, the
    /// evidence blocks ride in the closure environment in
    /// `instance_witnesses` order.
    fn requirement_forwarder(
        &mut self,
        instance: FuncId,
        visible: u16,
        hidden: &[Symbol],
    ) -> FuncId {
        let id = self.program_builder.reserve("requirement_forwarder");
        let mut insts = Vec::new();
        let mut args: Vec<Operand> = (0..visible).map(Operand::Local).collect();
        let mut next = visible;
        let mut env_index: u16 = 0;
        for param in hidden {
            let mut slots = 2;
            for protocol in self.program_builder.rigid_constraints(*param) {
                slots += self
                    .program_builder
                    .protocol_requirements(protocol.protocol)
                    .map(|requirements| requirements.len())
                    .unwrap_or(0);
            }
            for _ in 0..slots {
                insts.push(Inst::EnvGet {
                    dest: next,
                    index: env_index,
                });
                args.push(Operand::Local(next));
                next += 1;
                env_index += 1;
            }
        }
        let result = next;
        insts.push(Inst::Call {
            dest: result,
            func: instance,
            args,
            unwind: None,
        });
        let block = BlockData {
            params: Vec::new(),
            insts,
            term: Some(Term::Return(Operand::Local(result))),
        };
        self.program_builder.functions[id] = Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "requirement_forwarder".into(),
            arity: visible,
            locals: crate::compiling::mir::build::LocalInfo::uniform(result + 1),
            blocks: vec![block],
        };
        id
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
            // The full block — pair plus dictionaries — matching the
            // layout the glue chunk binds from its environment.
            self.push_witness_block(param, &mut env, span)?;
        }
        let dest = self.fresh_local();
        self.push(Inst::MakeClosure { dest, func, env });
        Ok(Operand::Local(dest))
    }
}
