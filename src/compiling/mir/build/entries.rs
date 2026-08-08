//! Program entry construction: the script body (every file's
//! top-level statements in initialization order, LINK-02), named
//! entries, and the guarded global teardown wrapper (ADR 0033).

use super::*;

impl<'a> ProgramBuilder<'a> {
    /// Find the requested `--entry` function among the root program's
    /// top-level functions. An explicit request crosses the package
    /// boundary, so it must name a public function; the implicit
    /// `main` fallback for statement-free scripts stays a file-local
    /// convention and passes `require_public: false`.
    pub(super) fn named_entry(
        &self,
        name: &str,
        require_public: bool,
    ) -> Result<Symbol, BackendError> {
        for file in self.programs[0].program.files().values() {
            for node in &file.roots {
                // The contract is a zero-parameter function. Top-level
                // functions lower to lets, so the let-bound arm carries
                // the declaration's source visibility.
                let (visibility, bound, func) = match node {
                    Node::Decl(
                        decl @ Decl {
                            kind: DeclKind::Func(func),
                            ..
                        },
                    ) => (decl.visibility, &func.name, func),
                    Node::Decl(decl) => match bound_func(decl) {
                        Some((bound, func)) => (decl.visibility, bound, func),
                        None => continue,
                    },
                    _ => continue,
                };
                if bound.name_str() == name
                    && let Name::Resolved(symbol, _) = bound
                {
                    if require_public
                        && visibility != crate::parsing::node_kinds::decl::Visibility::Public
                    {
                        return Err(BackendError::new(
                            format!("entry `{name}` must be a public function"),
                            func.body.span,
                        ));
                    }
                    if !func.params.is_empty() {
                        return Err(BackendError::new(
                            format!("entry `{name}` must take no parameters"),
                            func.body.span,
                        ));
                    }
                    return Ok(*symbol);
                }
            }
        }
        Err(BackendError::new(
            format!("no function named `{name}` to use as the entry"),
            Span::SYNTHESIZED,
        ))
    }

    /// A script executes its top-level statements in order; the final
    /// top-level expression is the program result. A file with no top-level
    /// statements falls back to a zero-parameter `main`.
    pub(super) fn build_script_entry(&mut self) -> Result<FuncId, BackendError> {
        // A script is every file's top-level statements in order (a
        // multi-file program — a test harness, a package binary — is one
        // reachable unit). Top-level bindings are program globals with
        // static slots, initialized in statement order (LINK-02), so
        // handler clauses and closures share them without captures.
        // `files()` comes published in initialization order (LINK-02).
        let program = self.programs[0].program;
        let script: Vec<&Node> = program
            .files()
            .values()
            .flat_map(|file| file.roots.iter())
            .filter(|node| match node {
                Node::Decl(decl) => {
                    matches!(decl.kind, DeclKind::Let { .. }) && bound_func(decl).is_none()
                }
                // Named `func` declarations surface as expression nodes in
                // scripts; they declare callables rather than execute.
                Node::Expr(Expr {
                    kind: ExprKind::Func(_),
                    ..
                })
                | Node::Stmt(Stmt {
                    kind:
                        StmtKind::Expr(Expr {
                            kind: ExprKind::Func(_),
                            ..
                        }),
                    ..
                }) => false,
                _ => true,
            })
            .collect();

        if script.is_empty() {
            let main = self.named_entry("main", false).map_err(|_| {
                BackendError::new(
                    "nothing to run: the file has no top-level statements and no `main`".into(),
                    Span::SYNTHESIZED,
                )
            })?;
            let entry = self.demand(main, Vec::new(), Span::SYNTHESIZED)?;
            return self.wrap_with_teardown(entry, None);
        }

        // Register the global slots first: later statements (and clause
        // bodies) resolve reads against them. A function quantifying
        // static value parameters gets NO slot (ADR 0035): it has no
        // single generic clause, so every use — call or first-class —
        // resolves through the callables registry and specializes.
        for node in &script {
            if let Node::Decl(decl) = node
                && let DeclKind::Let {
                    lhs:
                        Pattern {
                            kind: PatternKind::Bind(Name::Resolved(symbol, _)),
                            ..
                        },
                    rhs: Some(rhs),
                    ..
                } = &decl.kind
            {
                if let Some((_, func)) = bound_func(decl)
                    && func
                        .scheme
                        .params
                        .iter()
                        .any(|param| matches!(param.kind, ParamKind::Static(_)))
                {
                    continue;
                }
                let ty = rhs.ty.clone();
                // The stored type specializes like the initializer
                // compile below: the binding's own generalized
                // parameters pin to the one concrete argument every
                // use agrees on. Best-effort here — a genuine
                // disagreement is reported by the initializer compile.
                let ty = self.specialized_global_ty(*symbol, &ty);
                // The global twin of the borrowed-global rule: a linear
                // value's exactly-once consumption cannot be proven
                // across program-lifetime storage (OWN-03).
                if is_linear(self, &ty) {
                    return Err(BackendError::new(
                        "a linear value cannot be stored in a global binding; consume linear values within function scopes".into(),
                        decl.span,
                    ));
                }
                let slot = u32::try_from(self.global_slots.len()).unwrap_or_default();
                self.global_slots.insert(*symbol, slot);
                self.global_tys.insert(slot, ty);
            }
        }

        let id = self.reserve("script");
        let mut fx = FunctionBuilder::new(self, 0, 0);
        let mut value = Operand::Const(Constant::Unit);
        let last = script.len().saturating_sub(1);
        let mut returned_global: Option<u32> = None;
        for (ix, node) in script.iter().enumerate() {
            match node {
                Node::Decl(decl)
                    if let DeclKind::Let {
                        lhs:
                            Pattern {
                                kind: PatternKind::Bind(Name::Resolved(symbol, _)),
                                ..
                            },
                        rhs: Some(rhs),
                        ..
                    } = &decl.kind =>
                {
                    fx.current_span = decl.span;
                    // ADR 0035: a static-value-generic function has no
                    // slot (see registration above) and no generic clause
                    // to compile - skip its initializer entirely.
                    if let Some((_, func)) = bound_func(decl)
                        && func
                            .scheme
                            .params
                            .iter()
                            .any(|param| matches!(param.kind, ParamKind::Static(_)))
                    {
                        fx.flush_stmt_temps(None);
                        value = Operand::Const(Constant::Unit);
                        continue;
                    }
                    let specialization = fx.value_specialization(*symbol, &rhs.ty, rhs.span)?;
                    let (initializer, initializer_ty) =
                        fx.compile_with_specialization(&specialization, |fx| {
                            let initializer = fx.compile_expr(rhs)?;
                            let initializer_ty = fx.resolved(&rhs.ty);
                            Ok::<_, BackendError>((initializer, initializer_ty))
                        })?;
                    // A view rooted in a temporary cannot be stored: the
                    // owner dies with this statement (a view of another
                    // global is fine — the global outlives everything).
                    let initializer_is_view =
                        { contains_borrow_classified(fx.program_builder, &initializer_ty) };
                    if initializer_is_view
                        && let Operand::Local(view) = initializer
                        && fx.borrow_roots.contains_key(&view)
                    {
                        let root = fx.borrow_root(view);
                        if !fx.global_loads.contains_key(&root) && fx.owns(root) {
                            return Err(BackendError::new(
                                "a borrowed value cannot be stored in a global binding".into(),
                                rhs.span,
                            ));
                        }
                    }
                    // The slot is an owned sink: a place read the frame
                    // does not own (another global) donates a reference.
                    fx.consume_binding(initializer, &initializer_ty, rhs.span)?;
                    let slot = fx.program_builder.global_slots[symbol];
                    fx.push(Inst::GlobalStore {
                        global: slot,
                        src: initializer,
                    });
                    fx.flush_stmt_temps(None);
                    value = Operand::Const(Constant::Unit);
                }
                _ => {
                    value = fx.compile_node(node)?;
                    if ix != last {
                        fx.flush_stmt_temps(None);
                        value = Operand::Const(Constant::Unit);
                    } else {
                        fx.flush_stmt_temps(Some(value));
                        if let Node::Expr(Expr {
                            kind: ExprKind::Variable(Name::Resolved(symbol, _)),
                            ..
                        }) = node
                        {
                            returned_global = fx.program_builder.global_slots.get(symbol).copied();
                        }
                    }
                }
            }
        }

        let (n_locals, blocks, _return_repr, debug_names) = fx.finish(value)?;
        self.functions[id] = Function {
            debug_names,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "script".into(),
            arity: 0,
            locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
            blocks,
        };

        self.wrap_with_teardown(id, returned_global)
    }

    /// Guarded global teardown (ADR 0033) lives in an OUTER frame: a
    /// handler clause's Discontinue aborts to the frame that installed it
    /// (the inner script), so teardown still runs on every exit. The
    /// teardown skips a global the script returns (its buffers are the
    /// program's result).
    pub(super) fn wrap_with_teardown(
        &mut self,
        id: FuncId,
        returned_global: Option<u32>,
    ) -> Result<FuncId, BackendError> {
        // The program runs inside core's `_with_host` (ADR 0039), which
        // installs the host fallbacks around it as ordinary handlers —
        // the compiler knows the wrapper, not any effect. Its callback
        // returns unit, so a synthesized body stashes the program value
        // in a hidden global slot for this wrapper to return after
        // teardown. Programs without core have no wrapper (and no
        // ambient effects to supply) and run directly.
        let hosted = if self.callables.contains_key(&Symbol::WithHost) {
            let host = self.demand(Symbol::WithHost, Vec::new(), Span::SYNTHESIZED)?;
            let slot = u32::try_from(self.global_slots.len()).unwrap_or_default();
            self.result_slot = Some(slot);
            let body_id = self.reserve("entry_body");
            let mut fx = FunctionBuilder::new(self, 0, 0);
            let result = fx.fresh_local();
            fx.push(Inst::Call {
                dest: result,
                func: id,
                args: Vec::new(),
                unwind: None,
            });
            fx.push(Inst::GlobalStore {
                global: slot,
                src: Operand::Local(result),
            });
            let (n_locals, blocks, _return_repr, debug_names) =
                fx.finish(Operand::Const(Constant::Unit))?;
            self.functions[body_id] = Function {
                debug_names,
                frame_sites: Default::default(),
                param_reprs: Vec::new(),
                return_repr: None,
                name: "entry_body".into(),
                arity: 0,
                locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
                blocks,
            };
            Some((host, body_id, slot))
        } else {
            None
        };

        let outer = self.reserve("script_main");
        let mut wrapper = FunctionBuilder::new(self, 0, 0);
        let result = wrapper.fresh_local();
        match hosted {
            Some((host, body_id, slot)) => {
                let closure = wrapper.fresh_local();
                wrapper.push(Inst::MakeClosure {
                    dest: closure,
                    func: body_id,
                    env: Vec::new(),
                });
                let unit_result = wrapper.fresh_local();
                wrapper.push(Inst::Call {
                    dest: unit_result,
                    func: host,
                    args: vec![Operand::Local(closure)],
                    unwind: None,
                });
                wrapper.push(Inst::GlobalLoad {
                    dest: result,
                    global: slot,
                });
            }
            None => {
                wrapper.push(Inst::Call {
                    dest: result,
                    func: id,
                    args: Vec::new(),
                    unwind: None,
                });
            }
        }
        let mut slots: Vec<(u32, Ty)> = wrapper
            .program_builder
            .global_tys
            .iter()
            .map(|(slot, ty)| (*slot, ty.clone()))
            .collect();
        slots.sort_unstable_by_key(|(slot, _)| std::cmp::Reverse(*slot));
        for (slot, ty) in slots {
            if Some(slot) == returned_global {
                continue;
            }
            if wrapper.needs_release(&ty) {
                let loaded = wrapper.fresh_local();
                wrapper.push(Inst::GlobalLoad {
                    dest: loaded,
                    global: slot,
                });
                wrapper.drop_value(Operand::Local(loaded), &ty);
            }
        }
        let (n_locals, blocks, _return_repr, debug_names) =
            wrapper.finish(Operand::Local(result))?;
        self.functions[outer] = Function {
            debug_names,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "script_main".into(),
            arity: 0,
            locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
            blocks,
        };
        Ok(outer)
    }

    /// A named entry always runs inside the host and teardown wrapper.
    /// Its top-level bindings, when present, initialize first in declaration
    /// order - the same LINK-02 discipline scripts get.
    pub(super) fn build_named_entry(&mut self, name: &str) -> Result<FuncId, BackendError> {
        let symbol = self.named_entry(name, true)?;
        let entry = self.demand(symbol, Vec::new(), Span::SYNTHESIZED)?;
        let Some(globals_init) = self.build_globals_init()? else {
            return self.wrap_with_teardown(entry, None);
        };
        let id = self.reserve("entry_init");
        let mut fx = FunctionBuilder::new(self, 0, 0);
        let unit = fx.fresh_local();
        fx.push(Inst::Call {
            dest: unit,
            func: globals_init,
            args: Vec::new(),
            unwind: None,
        });
        let result = fx.fresh_local();
        fx.push(Inst::Call {
            dest: result,
            func: entry,
            args: Vec::new(),
            unwind: None,
        });
        let (n_locals, blocks, _return_repr, debug_names) = fx.finish(Operand::Local(result))?;
        self.functions[id] = Function {
            debug_names,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "entry_init".into(),
            arity: 0,
            locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
            blocks,
        };
        self.wrap_with_teardown(id, None)
    }

    /// Register the root program's top-level `let` bindings as globals and
    /// compile their initializers into one shared arity-0 function, or
    /// `None` when there are no top-level bindings.
    fn build_globals_init(&mut self) -> Result<Option<FuncId>, BackendError> {
        let program = self.programs[0].program;
        let lets: Vec<&Decl> = program
            .files()
            .values()
            .flat_map(|file| file.roots.iter())
            .filter_map(|node| match node {
                Node::Decl(decl)
                    if matches!(decl.kind, DeclKind::Let { .. }) && bound_func(decl).is_none() =>
                {
                    Some(decl)
                }
                _ => None,
            })
            .collect();
        if lets.is_empty() {
            return Ok(None);
        }
        for decl in &lets {
            if let DeclKind::Let {
                lhs, rhs: Some(_), ..
            } = &decl.kind
            {
                for (symbol, ty) in pattern_bindings_with_tys(lhs) {
                    if is_linear(self, &ty) {
                        return Err(BackendError::new(
                            "a linear value cannot be stored in a global binding; consume linear values within function scopes".into(),
                            decl.span,
                        ));
                    }
                    let slot = u32::try_from(self.global_slots.len()).unwrap_or_default();
                    self.global_slots.insert(symbol, slot);
                    self.global_tys.insert(slot, ty);
                }
            }
        }
        let id = self.reserve("globals_init");
        let mut fx = FunctionBuilder::new(self, 0, 0);
        for decl in &lets {
            let DeclKind::Let {
                lhs:
                    Pattern {
                        kind: PatternKind::Bind(Name::Resolved(symbol, _)),
                        ..
                    },
                rhs: Some(rhs),
                ..
            } = &decl.kind
            else {
                // Destructure into frame locals, then transfer each
                // component into its slot.
                let DeclKind::Let {
                    lhs, rhs: Some(_), ..
                } = &decl.kind
                else {
                    return Err(BackendError::unsupported(
                        "`let` without an initializer is not supported yet".into(),
                        decl.span,
                    ));
                };
                fx.compile_decl(decl)?;
                for (symbol, _) in pattern_bindings_with_tys(lhs) {
                    let Some(local) = fx.locals.get(&symbol).copied() else {
                        continue;
                    };
                    let slot = fx.program_builder.global_slots[&symbol];
                    fx.consume_operand(Operand::Local(local));
                    fx.push(Inst::GlobalStore {
                        global: slot,
                        src: Operand::Local(local),
                    });
                }
                fx.flush_stmt_temps(None);
                continue;
            };
            let initializer = fx.compile_expr(rhs)?;
            fx.consume_binding(initializer, &rhs.ty, rhs.span)?;
            let slot = fx.program_builder.global_slots[symbol];
            fx.push(Inst::GlobalStore {
                global: slot,
                src: initializer,
            });
            fx.flush_stmt_temps(None);
        }
        let (n_locals, blocks, _return_repr, debug_names) =
            fx.finish(Operand::Const(Constant::Unit))?;
        self.functions[id] = Function {
            debug_names,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "globals_init".into(),
            arity: 0,
            locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
            blocks,
        };
        Ok(Some(id))
    }

    /// A symbol's display name, from whichever program declared it.
    fn symbol_name(&self, symbol: Symbol) -> Option<String> {
        self.programs.iter().find_map(|input| {
            input
                .program
                .resolved_names()
                .symbol_names
                .get(&symbol)
                .cloned()
        })
    }

    /// Resolve one exported service function (ADR 0043 call ABI): public,
    /// top-level, non-generic, free of `mut` parameters (the
    /// writeback-tuple return convention would corrupt the host-visible
    /// result value), and performing only allowed effects.
    fn export_entry(
        &self,
        name: &str,
        allowed_effects: &[String],
    ) -> Result<(Symbol, u16), BackendError> {
        for file in self.programs[0].program.files().values() {
            for node in &file.roots {
                let (visibility, bound, func) = match node {
                    Node::Decl(
                        decl @ Decl {
                            kind: DeclKind::Func(func),
                            ..
                        },
                    ) => (decl.visibility, &func.name, func),
                    Node::Decl(decl) => match bound_func(decl) {
                        Some((bound, func)) => (decl.visibility, bound, func),
                        None => continue,
                    },
                    _ => continue,
                };
                if bound.name_str() == name
                    && let Name::Resolved(symbol, _) = bound
                {
                    if visibility != crate::parsing::node_kinds::decl::Visibility::Public {
                        return Err(BackendError::new(
                            format!("exported function `{name}` must be public"),
                            func.body.span,
                        ));
                    }
                    if !func.scheme.params.is_empty() {
                        return Err(BackendError::new(
                            format!("exported function `{name}` may not be generic"),
                            func.body.span,
                        ));
                    }
                    // The same exclusive-borrow classification that
                    // populates `writeback_params` in `compile_func`;
                    // exports are non-generic, so the raw type suffices.
                    if func.params.iter().any(|param| {
                        param
                            .ty
                            .as_ref()
                            .is_some_and(|ty| matches!(ty, Ty::Borrow(Perm::Exclusive, _)))
                    }) {
                        return Err(BackendError::new(
                            format!("exported function `{name}` may not take `mut` parameters"),
                            func.body.span,
                        ));
                    }
                    // The capability gate: the export's latent row must
                    // stay within the service's allowed effects. Typing
                    // guarantees the body cannot perform outside its row
                    // (a local `#handle`'s clauses are row-checked too),
                    // so this subset check is the whole denial.
                    // The AST node's scheme is the declared one; the
                    // inferred row lives in typing's published scheme
                    // (ADR 0015: typing publishes, the backend reads).
                    let Some(scheme) = self.programs[0].program.types().schemes.get(symbol) else {
                        return Err(BackendError::new(
                            format!("exported function `{name}` has no published scheme"),
                            func.body.span,
                        ));
                    };
                    let Ty::Func(_, _, row) = &scheme.ty else {
                        return Err(BackendError::new(
                            format!("exported function `{name}` has a non-function scheme"),
                            func.body.span,
                        ));
                    };
                    // A generalized row tail (`'[ | ρ]`) is subsumption
                    // slack, not a capability: the body can only perform
                    // the row's concrete labels. A label that is not a
                    // declared effect is a caller-chosen effect parameter
                    // — rejected, since the host instantiates nothing.
                    for entry in &row.effects {
                        if !matches!(entry.effect, Symbol::Effect(_)) {
                            return Err(BackendError::new(
                                format!(
                                    "exported function `{name}` may not take effect parameters"
                                ),
                                func.body.span,
                            ));
                        }
                        let effect = self.symbol_name(entry.effect);
                        let allowed = effect
                            .as_ref()
                            .is_some_and(|effect| allowed_effects.iter().any(|a| a == effect));
                        if !allowed {
                            return Err(BackendError::new(
                                format!(
                                    "exported function `{name}` performs '{}, which this service does not allow",
                                    effect.as_deref().unwrap_or("<unknown>")
                                ),
                                func.body.span,
                            ));
                        }
                    }
                    let arity = u16::try_from(func.params.len()).unwrap_or_default();
                    return Ok((*symbol, arity));
                }
            }
        }
        Err(BackendError::new(
            format!("no function named `{name}` to export"),
            Span::SYNTHESIZED,
        ))
    }

    /// Compile a service module (ADR 0043): one host-callable wrapper per
    /// export. The returned entry chunk is inert — a service module is
    /// dispatched through its export table, not run.
    pub(super) fn build_export_entries(
        &mut self,
        names: &[String],
        allowed_effects: &[String],
    ) -> Result<FuncId, BackendError> {
        if let Some(duplicate) = names
            .iter()
            .enumerate()
            .find(|(ix, name)| names[..*ix].contains(name))
        {
            return Err(BackendError::new(
                format!("duplicate export `{}`", duplicate.1),
                Span::SYNTHESIZED,
            ));
        }
        let globals_init = self.build_globals_init()?;
        for name in names {
            let (symbol, arity) = self.export_entry(name, allowed_effects)?;
            let target = self.demand(symbol, Vec::new(), Span::SYNTHESIZED)?;
            let wrapper = self.wrap_export(name, target, arity, globals_init)?;
            self.exports.push((name.clone(), wrapper));
        }
        let id = self.reserve("empty_entry");
        let fx = FunctionBuilder::new(self, 0, 0);
        let (n_locals, blocks, _return_repr, debug_names) =
            fx.finish(Operand::Const(Constant::Unit))?;
        self.functions[id] = Function {
            debug_names,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "empty_entry".into(),
            arity: 0,
            locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
            blocks,
        };
        Ok(id)
    }

    /// One host-callable wrapper per export, mirroring the script entry
    /// (ADR 0039/0033): the wrapper's arguments ride into `_with_host`'s
    /// nullary callback through its closure environment, the callback
    /// stashes the result in the hidden slot, and the wrapper reloads it
    /// and tears globals down in the outer frame. Every call runs on a
    /// fresh machine, so each wrapper owns the full init/teardown cycle.
    /// The host's argument values are scalars or static-backed strings,
    /// so the wrapper frame drops none of them.
    fn wrap_export(
        &mut self,
        name: &str,
        target: FuncId,
        arity: u16,
        globals_init: Option<FuncId>,
    ) -> Result<FuncId, BackendError> {
        let outer = self.reserve(&format!("export:{name}"));
        if !self.callables.contains_key(&Symbol::WithHost) {
            // No core, no ambient effects to install: call directly.
            let mut fx = FunctionBuilder::new(self, arity, 0);
            let args: Vec<Operand> = (0..arity).map(Operand::Local).collect();
            let result = fx.fresh_local();
            fx.push(Inst::Call {
                dest: result,
                func: target,
                args,
                unwind: None,
            });
            let (n_locals, blocks, _return_repr, debug_names) =
                fx.finish(Operand::Local(result))?;
            self.functions[outer] = Function {
                debug_names,
                frame_sites: Default::default(),
                param_reprs: Vec::new(),
                return_repr: None,
                name: format!("export:{name}"),
                arity,
                locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
                blocks,
            };
            return Ok(outer);
        }

        let host = self.demand(Symbol::WithHost, Vec::new(), Span::SYNTHESIZED)?;
        let slot = u32::try_from(self.global_slots.len()).unwrap_or_default();
        self.result_slot = Some(slot);

        let body_id = self.reserve("export_body");
        let mut fx = FunctionBuilder::new(self, 0, 0);
        if let Some(init) = globals_init {
            let unit = fx.fresh_local();
            fx.push(Inst::Call {
                dest: unit,
                func: init,
                args: Vec::new(),
                unwind: None,
            });
        }
        let mut args = Vec::new();
        for index in 0..arity {
            let local = fx.fresh_local();
            fx.push(Inst::EnvGet { dest: local, index });
            args.push(Operand::Local(local));
        }
        let result = fx.fresh_local();
        fx.push(Inst::Call {
            dest: result,
            func: target,
            args,
            unwind: None,
        });
        fx.push(Inst::GlobalStore {
            global: slot,
            src: Operand::Local(result),
        });
        let (n_locals, blocks, _return_repr, debug_names) =
            fx.finish(Operand::Const(Constant::Unit))?;
        self.functions[body_id] = Function {
            debug_names,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "export_body".into(),
            arity: 0,
            locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
            blocks,
        };

        let mut wrapper = FunctionBuilder::new(self, arity, 0);
        let closure = wrapper.fresh_local();
        let env: Vec<Operand> = (0..arity).map(Operand::Local).collect();
        wrapper.push(Inst::MakeClosure {
            dest: closure,
            func: body_id,
            env,
        });
        let unit_result = wrapper.fresh_local();
        wrapper.push(Inst::Call {
            dest: unit_result,
            func: host,
            args: vec![Operand::Local(closure)],
            unwind: None,
        });
        let result = wrapper.fresh_local();
        wrapper.push(Inst::GlobalLoad {
            dest: result,
            global: slot,
        });
        let mut slots: Vec<(u32, Ty)> = wrapper
            .program_builder
            .global_tys
            .iter()
            .map(|(slot, ty)| (*slot, ty.clone()))
            .collect();
        slots.sort_unstable_by_key(|(slot, _)| std::cmp::Reverse(*slot));
        for (slot, ty) in slots {
            if wrapper.needs_release(&ty) {
                let loaded = wrapper.fresh_local();
                wrapper.push(Inst::GlobalLoad {
                    dest: loaded,
                    global: slot,
                });
                wrapper.drop_value(Operand::Local(loaded), &ty);
            }
        }
        let (n_locals, blocks, _return_repr, debug_names) =
            wrapper.finish(Operand::Local(result))?;
        self.functions[outer] = Function {
            debug_names,
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: format!("export:{name}"),
            arity,
            locals: crate::compiling::mir::build::LocalInfo::uniform(n_locals),
            blocks,
        };
        Ok(outer)
    }
}
