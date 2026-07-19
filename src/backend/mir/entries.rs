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
                    Node::Decl(decl) => match let_bound_func(decl) {
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
                    return Ok(canonical(*symbol, self.programs[0].module));
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
        let program = self.programs[0].program;
        let script: Vec<&Node> = files_in_initialization_order(program)
            .into_iter()
            .flat_map(|file| file.roots.iter())
            .filter(|node| match node {
                Node::Decl(decl) => {
                    matches!(decl.kind, DeclKind::Let { .. }) && let_bound_func(decl).is_none()
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
            return self.demand(main, Vec::new(), Span::SYNTHESIZED);
        }

        // Register the global slots first: later statements (and clause
        // bodies) resolve reads against them.
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
                let ty = canonical_ty(&rhs.ty, self.programs[0].module);
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
                    let initializer = fx.compile_expr(rhs)?;
                    // A view rooted in a temporary cannot be stored: the
                    // owner dies with this statement (a view of another
                    // global is fine — the global outlives everything).
                    let initializer_is_view = {
                        let ty = fx.resolved(&rhs.ty);
                        contains_borrow_classified(fx.program_builder, &ty)
                    };
                    if initializer_is_view
                        && let Operand::Local(view) = initializer
                        && fx.borrow_roots.contains_key(&view)
                    {
                        let root = fx.borrow_root(view);
                        if !fx.global_loads.contains_key(&root) && fx.owned_tys.contains_key(&root)
                        {
                            return Err(BackendError::new(
                                "a borrowed value cannot be stored in a global binding".into(),
                                rhs.span,
                            ));
                        }
                    }
                    // The slot is an owned sink: a place read the frame
                    // does not own (another global) donates a reference.
                    let initializer_ty = fx.resolved(&rhs.ty);
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

        let (n_locals, blocks) = fx.finish(value)?;
        self.functions[id] = Function {
            name: "script".into(),
            arity: 0,
            n_locals,
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
        let outer = self.reserve("script_main");
        let mut wrapper = FunctionBuilder::new(self, 0, 0);
        let result = wrapper.fresh_local();
        wrapper.push(Inst::Call {
            dest: result,
            func: id,
            args: Vec::new(),
            unwind: None,
        });
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
            // A linear global would need an exactly-once consumption proof
            // across every function that can reach the slot plus this
            // teardown; keep linear values in function scopes (OWN-03).
            if is_linear(wrapper.program_builder, &ty) {
                return Err(BackendError::unsupported(
                    "linear global values are not supported yet (consume linear values within function scopes)".into(),
                    Span::SYNTHESIZED,
                ));
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
        let (n_locals, blocks) = wrapper.finish(Operand::Local(result))?;
        self.functions[outer] = Function {
            name: "script_main".into(),
            arity: 0,
            n_locals,
            blocks,
        };
        Ok(outer)
    }

    /// A named entry still initializes the program's top-level bindings
    /// (in declaration order) into their slots and tears them down around
    /// the call — the same LINK-02 discipline scripts get.
    pub(super) fn build_named_entry(&mut self, name: &str) -> Result<FuncId, BackendError> {
        let symbol = self.named_entry(name, true)?;
        let program = self.programs[0].program;
        let lets: Vec<&Decl> = files_in_initialization_order(program)
            .into_iter()
            .flat_map(|file| file.roots.iter())
            .filter_map(|node| match node {
                Node::Decl(decl)
                    if matches!(decl.kind, DeclKind::Let { .. })
                        && let_bound_func(decl).is_none() =>
                {
                    Some(decl)
                }
                _ => None,
            })
            .collect();
        let entry = self.demand(symbol, Vec::new(), Span::SYNTHESIZED)?;
        if lets.is_empty() {
            return Ok(entry);
        }
        for decl in &lets {
            if let DeclKind::Let {
                lhs,
                rhs: Some(rhs),
                ..
            } = &decl.kind
            {
                for (symbol, ty) in pattern_bindings_with_tys(lhs, &rhs.ty) {
                    let slot = u32::try_from(self.global_slots.len()).unwrap_or_default();
                    self.global_slots.insert(symbol, slot);
                    self.global_tys
                        .insert(slot, canonical_ty(&ty, self.programs[0].module));
                }
            }
        }
        let id = self.reserve("entry_init");
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
                    lhs,
                    rhs: Some(rhs),
                    ..
                } = &decl.kind
                else {
                    return Err(BackendError::unsupported(
                        "`let` without an initializer is not supported yet".into(),
                        decl.span,
                    ));
                };
                fx.compile_decl(decl)?;
                for (symbol, _) in pattern_bindings_with_tys(lhs, &rhs.ty) {
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
        let result = fx.fresh_local();
        let unwind = None;
        fx.push(Inst::Call {
            dest: result,
            func: entry,
            args: Vec::new(),
            unwind,
        });
        let (n_locals, blocks) = fx.finish(Operand::Local(result))?;
        self.functions[id] = Function {
            name: "entry_init".into(),
            arity: 0,
            n_locals,
            blocks,
        };
        self.wrap_with_teardown(id, None)
    }
}
