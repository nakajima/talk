use derive_visitor::VisitorMut;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    id_generator::IDGenerator,
    name::Name,
    name_resolution::{
        name_resolver::{NameResolver, NameResolverError, Scope},
        symbol::{StructId, Symbol},
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        body::Body,
        decl::{Decl, DeclKind, Visibility},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        match_arm::MatchArm,
        parameter::Parameter,
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    on,
    span::Span,
};

// Dummy values for symbol type discrimination - actual values created by declare()
#[macro_export]
macro_rules! some {
    (Struct) => {
        $crate::name_resolution::symbol::Symbol::Struct(
            $crate::name_resolution::symbol::StructId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Effect) => {
        $crate::name_resolution::symbol::Symbol::Effect(
            $crate::name_resolution::symbol::EffectId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Enum) => {
        $crate::name_resolution::symbol::Symbol::Enum($crate::name_resolution::symbol::EnumId::new(
            $crate::compiling::module::ModuleId::Current,
            0,
        ))
    };
    (TypeAlias) => {
        $crate::name_resolution::symbol::Symbol::TypeAlias(
            $crate::name_resolution::symbol::TypeAliasId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Global) => {
        $crate::name_resolution::symbol::Symbol::Global(
            $crate::name_resolution::symbol::GlobalId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Protocol) => {
        $crate::name_resolution::symbol::Symbol::Protocol(
            $crate::name_resolution::symbol::ProtocolId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Variant) => {
        $crate::name_resolution::symbol::Symbol::Variant(
            $crate::name_resolution::symbol::VariantId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Property) => {
        $crate::name_resolution::symbol::Symbol::Property(
            $crate::name_resolution::symbol::PropertyId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (InstanceMethod) => {
        $crate::name_resolution::symbol::Symbol::InstanceMethod(
            $crate::name_resolution::symbol::InstanceMethodId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Initializer) => {
        $crate::name_resolution::symbol::Symbol::Initializer(
            $crate::name_resolution::symbol::InitializerId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (MethodRequirement) => {
        $crate::name_resolution::symbol::Symbol::MethodRequirement(
            $crate::name_resolution::symbol::MethodRequirementId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (StaticMethod) => {
        $crate::name_resolution::symbol::Symbol::StaticMethod(
            $crate::name_resolution::symbol::StaticMethodId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (AssociatedType) => {
        $crate::name_resolution::symbol::Symbol::AssociatedType(
            $crate::name_resolution::symbol::AssociatedTypeId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Builtin) => {
        $crate::name_resolution::symbol::Symbol::Builtin(
            $crate::name_resolution::symbol::BuiltinId::new(
                $crate::compiling::module::ModuleId::Builtin,
                0,
            ),
        )
    };
    // Module-scoped type parameters
    (TypeParameter) => {
        $crate::name_resolution::symbol::Symbol::TypeParameter(
            $crate::name_resolution::symbol::TypeParameterId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (DeclaredLocal) => {
        $crate::name_resolution::symbol::Symbol::DeclaredLocal(
            $crate::name_resolution::symbol::DeclaredLocalId(0),
        )
    };
    (ParamLocal) => {
        $crate::name_resolution::symbol::Symbol::ParamLocal(
            $crate::name_resolution::symbol::ParamLocalId(0),
        )
    };
    (PatternBindLocal) => {
        $crate::name_resolution::symbol::Symbol::PatternBindLocal(
            $crate::name_resolution::symbol::PatternBindLocalId(0),
        )
    };
    (Synthesized) => {
        $crate::name_resolution::symbol::Symbol::Synthesized(
            $crate::name_resolution::symbol::SynthesizedId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
}

#[derive(VisitorMut)]
#[visitor(
    Stmt(enter, exit),
    FuncSignature,
    MatchArm(enter, exit),
    Func,
    Decl(enter, exit),
    Block(enter)
)]
pub struct DeclDeclarer<'a> {
    pub(super) resolver: &'a mut NameResolver,
    // For determining whether we need to synth an init
    type_members: FxHashMap<NodeID, TypeMembers>,
    // For synthesizing
    node_ids: &'a mut IDGenerator,
}

#[derive(Default)]
struct TypeMembers {
    initializers: Vec<DeclKind>,
    properties: Vec<DeclKind>,
}

#[allow(clippy::expect_used)]
impl<'a> DeclDeclarer<'a> {
    pub fn new(resolver: &'a mut NameResolver, node_ids: &'a mut IDGenerator) -> Self {
        Self {
            resolver,
            type_members: Default::default(),
            node_ids,
        }
    }

    pub fn at_module_scope(&self) -> bool {
        matches!(self.resolver.current_scope_id, Some(NodeID(_, 0)))
    }

    #[instrument(skip(self), fields(level = ?self.resolver.current_level))]
    pub fn start_scope(&mut self, binder: Option<Symbol>, id: NodeID, bump_level: bool) {
        let parent_id = self.resolver.current_scope_id;
        let scope = Scope::new(
            binder,
            if bump_level {
                self.resolver.current_level.next()
            } else {
                self.resolver.current_level
            },
            id,
            parent_id,
            self.resolver
                .current_scope()
                .map(|s| s.depth + 1)
                .unwrap_or(1),
        );
        tracing::trace!("start_scope: {:?}", scope);
        self.resolver.scopes.insert(id, scope);
        self.resolver.current_scope_id = Some(id);
    }

    pub fn end_scope(&mut self) {
        let current_id = self.resolver.current_scope_id.expect("no scope to end");
        let current = self
            .resolver
            .scopes
            .get(&current_id)
            .expect("did not find current scope");

        self.resolver.current_scope_id = current.parent_id;
    }

    /// Declares generics as TypeParameter symbols in the current scope.
    fn declare_generics(&mut self, generics: &mut [GenericDecl]) {
        for generic in generics {
            generic.name = self
                .resolver
                .declare(&generic.name, some!(TypeParameter), generic.id, generic.name_span);
        }
    }

    pub(super) fn predeclare_nominals(&mut self, decls: &[&Decl]) {
        for decl in decls.iter() {
            // Note: Effects are NOT predeclared here to maintain ID stability for Core types
            // (Array, String, etc. have hardcoded IDs). Effects get their IDs during
            // the full declaration phase.
            match &decl.kind {
                DeclKind::Struct { name, name_span, .. }
                | DeclKind::Enum { name, name_span, .. }
                | DeclKind::Protocol { name, name_span, .. } => {
                    let kind = match &decl.kind {
                        DeclKind::Struct { .. } => some!(Struct),
                        DeclKind::Enum { .. } => some!(Enum),
                        DeclKind::Protocol { .. } => some!(Protocol),
                        _ => unreachable!(),
                    };

                    let resolved = self.resolver.declare(name, kind, decl.id, *name_span);

                    // Mark as public if visibility is Public (needed for import resolution)
                    if decl.visibility == Visibility::Public {
                        if let Ok(sym) = resolved.symbol() {
                            self.resolver.mark_public(sym);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Predeclare public top-level Let bindings as Globals so they're available during import resolution.
    /// Only handles simple Bind patterns (not destructuring).
    /// Only public bindings are predeclared since they're the only ones that can be imported.
    pub(super) fn predeclare_values(&mut self, decls: &[&Decl]) {
        let mut exported_names: FxHashMap<String, NodeID> = FxHashMap::default();

        for decl in decls.iter() {
            // Only predeclare public Let bindings
            if decl.visibility != Visibility::Public {
                continue;
            }
            if let DeclKind::Let { lhs, .. } = &decl.kind {
                // For simple bind patterns, predeclare as Global
                // Use lhs.id (pattern id) to match what declare_pattern uses
                if let PatternKind::Bind(name) = &lhs.kind {
                    let name_str = name.name_str();
                    if exported_names.contains_key(&name_str) {
                        self.resolver
                            .diagnostic(lhs.id, NameResolverError::DuplicateExport(name_str));
                        continue;
                    }
                    exported_names.insert(name_str, lhs.id);

                    // Pattern span is used for the binding since Bind pattern doesn't have name_span
                    let resolved = self.resolver.declare(name, some!(Global), lhs.id, lhs.span);
                    if let Ok(sym) = resolved.symbol() {
                        self.resolver.mark_public(sym);
                    }
                }
            }
        }
    }


    ///////////////////////////////////////////////////////////////////////////
    // Local decls
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn declare_pattern(&mut self, pattern: &mut Pattern, bind_type: Symbol) {
        let Pattern { kind, span, .. } = pattern;
        let span = *span;

        match kind {
            PatternKind::Bind(name @ Name::Raw(_)) => {
                *name = if self.at_module_scope() {
                    self.resolver.declare(name, some!(Global), pattern.id, span)
                } else {
                    self.resolver.declare(name, bind_type, pattern.id, span)
                }
            }
            PatternKind::Or(patterns) => {
                // Declare the binds in the first pattern, the following patterns will get resolved from those
                self.declare_pattern(&mut patterns[0], bind_type);
            }
            PatternKind::Bind(..) => {}
            PatternKind::Variant { fields, .. } => {
                for field in fields.iter_mut() {
                    self.declare_pattern(field, some!(PatternBindLocal));
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    match &mut field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            *name =
                                self.resolver
                                    .declare(name, some!(PatternBindLocal), pattern.id, field.span);
                        }
                        RecordFieldPatternKind::Equals { name, name_span, value } => {
                            *name =
                                self.resolver
                                    .declare(name, some!(PatternBindLocal), pattern.id, *name_span);
                            self.declare_pattern(value, some!(PatternBindLocal));
                        }
                        RecordFieldPatternKind::Rest => (),
                    }
                }
            }
            #[allow(clippy::todo)]
            PatternKind::Struct { .. } => {
                todo!()
            }
            PatternKind::Tuple(values) => {
                for value in values {
                    self.declare_pattern(value, bind_type);
                }
            }
            PatternKind::Wildcard => (),
            PatternKind::LiteralFalse
            | PatternKind::LiteralTrue
            | PatternKind::LiteralInt(..)
            | PatternKind::LiteralFloat(..) => (),
        }
    }

    fn enter_nominal(
        &mut self,
        id: NodeID,
        name: &mut Name,
        generics: &mut [GenericDecl],
        decls: &[Decl],
    ) {
        // Should be set by predeclare_nominals for Struct/Enum/Protocol, but `extend` can target
        // a nominal declared in another file. If we still can't resolve it, keep the resolver
        // state consistent so we don't crash while walking the body.
        // Note: name_span is not available in this function signature, so we pass None.
        // The spans are already recorded by predeclare_nominals for Struct/Enum/Protocol.
        *name = self.resolver.lookup(name, Some(id), None).unwrap_or(name.clone());

        let sym = match name.symbol() {
            Ok(sym) => sym,
            Err(_) => {
                self.resolver
                    .diagnostic(id, NameResolverError::Unresolved(name.clone()));
                Symbol::Synthesized(
                    self.resolver
                        .symbols
                        .next_synthesized(self.resolver.current_module_id),
                )
            }
        };

        if let Some(parent) = self.resolver.nominal_stack.last() {
            self.resolver
                .phase
                .child_types
                .entry(parent.0)
                .or_default()
                .insert(name.name_str().into(), sym);
        }

        self.resolver.nominal_stack.push((sym, id));
        self.type_members.insert(id, TypeMembers::default());

        self.start_scope(Some(sym), id, false);
        self.resolver
            .current_scope_mut()
            .expect("didn't get current scope")
            .types
            .insert("Self".into(), sym);

        self.declare_generics(generics);

        self.predeclare_nominals(decls.iter().collect_vec().as_slice());
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block expr decls
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self, stmt))]
    fn enter_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(block),
            ..
        }) = &mut stmt.kind
        {
            self.start_scope(None, block.id, false);
        }
    }

    fn exit_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(..),
            ..
        }) = &mut stmt.kind
        {
            self.end_scope();
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block scoping
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self, arm))]
    fn enter_match_arm(&mut self, arm: &mut MatchArm) {
        self.start_scope(None, arm.id, false);
        self.declare_pattern(&mut arm.pattern, some!(PatternBindLocal));
    }

    fn exit_match_arm(&mut self, _arm: &mut MatchArm) {
        self.end_scope();
    }

    fn enter_block(&mut self, block: &mut Block) {
        for arg in &mut block.args {
            arg.name = self.resolver.declare(&arg.name, some!(ParamLocal), arg.id, arg.name_span);
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Funcs
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self, func), fields(func.name = ?func.name))]
    fn enter_func(&mut self, func: &mut Func) {
        let func_id = func.id;
        let func_name_span = func.name_span;
        on!(
            func,
            Func {
                id,
                name,
                generics,
                params,
                body: _,
                ret: _,
                attributes: _,
                ..
            },
            {
                let is_synth = matches!(name, Name::Raw(raw) if raw.starts_with("#fn_"))
                    || matches!(name, Name::Resolved(_, raw) if raw.starts_with("#fn_"));
                let fallback = if is_synth {
                    some!(Synthesized)
                } else {
                    some!(Global)
                };
                *name = self
                    .resolver
                    .lookup(name, Some(*id), Some(func_name_span))
                    .unwrap_or_else(|| self.resolver.declare(name, fallback, func_id, func_name_span));

                let func_sym = name
                    .symbol()
                    .unwrap_or_else(|_| unreachable!("did not resolve func name"));
                let binder = match self.resolver.current_scope().and_then(|scope| scope.binder) {
                    Some(parent) if parent == func_sym => None,
                    _ => Some(func_sym),
                };
                self.start_scope(binder, *id, false);

                self.declare_generics(generics);

                for param in params {
                    param.name = self
                        .resolver
                        .declare(&param.name, some!(ParamLocal), param.id, param.name_span);
                }
            }
        )
    }

    fn exit_func(&mut self, _func: &mut Func) {
        self.end_scope();
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, func))]
    fn enter_func_signature(&mut self, func: &mut FuncSignature) {
        let func_span = func.span;
        on!(
            func,
            FuncSignature {
                name,
                params,
                generics,
                ..
            },
            {
                // FuncSignature doesn't have a name_span, use its span
                *name = self
                    .resolver
                    .declare(name, some!(MethodRequirement), func.id, func_span);

                self.start_scope(
                    Some(name.symbol().unwrap_or_else(|_| unreachable!())),
                    func.id,
                    false,
                );

                self.declare_generics(generics);

                for param in params {
                    param.name = self
                        .resolver
                        .declare(&param.name, some!(ParamLocal), param.id, param.name_span);
                }
            }
        )
    }

    fn exit_func_signature(&mut self, _func: &mut FuncSignature) {
        self.end_scope();
    }

    ///////////////////////////////////////////////////////////////////////////
    // Struct decls
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self, decl))]
    fn enter_decl(&mut self, decl: &mut Decl) {
        on!(
            &mut decl.kind,
            DeclKind::Struct {
                name,
                generics,
                body,
                ..
            },
            {
                self.enter_nominal(decl.id, name, generics, &body.decls);
            }
        );

        on!(
            &mut decl.kind,
            DeclKind::Enum {
                name,
                generics,
                body,
                ..
            },
            {
                self.enter_nominal(decl.id, name, generics, &body.decls);
            }
        );

        on!(
            &mut decl.kind,
            DeclKind::Protocol {
                name,
                generics,
                body,
                ..
            },
            {
                self.enter_nominal(decl.id, name, generics, &body.decls);
            }
        );

        on!(
            &mut decl.kind,
            DeclKind::Extend {
                name,
                generics,
                body,
                ..
            },
            {
                self.enter_nominal(decl.id, name, generics, &body.decls);
            }
        );

        on!(&mut decl.kind, DeclKind::TypeAlias(lhs_name, name_span, ..), {
            *lhs_name = self.resolver.declare(lhs_name, some!(TypeAlias), decl.id, *name_span);

            if let Some(parent) = self.resolver.nominal_stack.last() {
                self.resolver
                    .phase
                    .child_types
                    .entry(parent.0)
                    .or_default()
                    .insert(
                        lhs_name.name_str().into(),
                        lhs_name.symbol().unwrap_or_else(|_| unreachable!()),
                    );
            }
        });

        on!(&mut decl.kind, DeclKind::EnumVariant(name, name_span, ..), {
            *name = self.resolver.declare(name, some!(Variant), decl.id, *name_span);
        });

        on!(
            &mut decl.kind,
            DeclKind::Method {
                func: box Func { id, name, name_span, generics, .. },
                is_static
            },
            {
                *name = if *is_static {
                    self.resolver.declare(name, some!(StaticMethod), decl.id, *name_span)
                } else {
                    self.resolver.declare(name, some!(InstanceMethod), decl.id, *name_span)
                };

                if let Some((nominal_sym, nominal_id)) = self.resolver.nominal_stack.last().cloned()
                {
                    let method_sym = name.symbol().unwrap_or_else(|_| unreachable!());
                    self.resolver
                        .track_dependency_from_to(method_sym, *id, nominal_sym, nominal_id);
                    self.resolver
                        .track_dependency_from_to(nominal_sym, nominal_id, method_sym, *id);
                }

                // self.start_scope(name.symbol().ok(), *id, true);
                self.declare_generics(generics);
            }
        );

        on!(&mut decl.kind, DeclKind::Associated { generic }, {
            generic.name = self
                .resolver
                .declare(&generic.name, some!(AssociatedType), decl.id, generic.name_span);
            let parent = self
                .resolver
                .nominal_stack
                .last()
                .expect("did not get parent protocol for associated type");
            self.resolver
                .phase
                .child_types
                .entry(parent.0)
                .or_default()
                .insert(
                    generic.name.name_str().into(),
                    generic.name.symbol().unwrap_or_else(|_| unreachable!()),
                );
        });

        on!(
            &mut decl.kind,
            DeclKind::FuncSignature(FuncSignature {
                id,
                name,
                span,
                generics,
                ..
            }),
            {
                // FuncSignature doesn't have name_span, use its span
                *name = self.resolver.declare(name, some!(Global), decl.id, *span);

                let (nominal_sym, nominal_id) = self
                    .resolver
                    .nominal_stack
                    .last()
                    .cloned()
                    .unwrap_or_else(|| unreachable!());
                let method_sym = name.symbol().unwrap_or_else(|_| unreachable!());
                self.resolver
                    .track_dependency_from_to(method_sym, *id, nominal_sym, nominal_id);
                self.resolver
                    .track_dependency_from_to(nominal_sym, nominal_id, method_sym, *id);

                self.declare_generics(generics);
            }
        );

        let decl_kind = decl.kind.clone();

        on!(&mut decl.kind, DeclKind::Property { name, name_span, .. }, {
            *name = self.resolver.declare(name, some!(Property), decl.id, *name_span);
            let id = self
                .resolver
                .current_scope_id
                .expect("didn't get current scope id");
            self.type_members
                .entry(id)
                .or_default()
                .properties
                .push(decl_kind.clone());
        });

        on!(&mut decl.kind, DeclKind::Init { name, .. }, {
            let id = self
                .resolver
                .current_scope_id
                .expect("didn't get current scope id");
            self.type_members
                .entry(id)
                .or_default()
                .initializers
                .push(decl_kind);

            // Init declarations use decl.span since there's no dedicated name_span
            *name = self.resolver.declare(name, some!(Initializer), decl.id, decl.span);

            self.start_scope(None, decl.id, false);
        });

        on!(&mut decl.kind, DeclKind::Let { lhs, .. }, {
            self.declare_pattern(lhs, some!(DeclaredLocal));
            for (id, binder) in lhs.collect_binders() {
                self.start_scope(Some(binder), id, true);
            }
        });

        on!(
            &mut decl.kind,
            DeclKind::Effect {
                name,
                name_span,
                generics,
                params,
                ..
            },
            {
                *name = self.resolver.declare(name, some!(Effect), decl.id, *name_span);

                // Start a scope for the effect's generics and params
                self.start_scope(None, decl.id, false);

                self.declare_generics(generics);

                for param in params {
                    param.name = self
                        .resolver
                        .declare(&param.name, some!(ParamLocal), param.id, param.name_span);
                }
            }
        );
    }

    fn exit_decl(&mut self, decl: &mut Decl) {
        on!(
            &mut decl.kind,
            DeclKind::Struct {
                name: Name::Resolved(Symbol::Struct(type_id), _),
                body,
                ..
            },
            {
                let type_members = self
                    .type_members
                    .remove(&decl.id)
                    .expect("didn't get type members");

                if type_members.initializers.is_empty() {
                    self.synthesize_init(body, &type_members, *type_id);
                }

                self.end_scope();
            }
        );

        on!(&mut decl.kind, DeclKind::Struct { name, .. }, {
            // If this struct failed to resolve (e.g. due to earlier errors), still unwind scopes so
            // we don't poison the resolver state.
            if !matches!(name, Name::Resolved(Symbol::Struct(..), _)) {
                self.type_members.remove(&decl.id);
                self.end_scope();
            }
        });

        on!(
            &mut decl.kind,
            DeclKind::Protocol { .. }
                | DeclKind::Enum { .. }
                | DeclKind::Extend { .. }
                | DeclKind::Init { .. }
                | DeclKind::Effect { .. },
            {
                self.end_scope();
            }
        );

        on!(&mut decl.kind, DeclKind::Let { lhs, .. }, {
            for _ in lhs.collect_binders() {
                self.end_scope();
            }
        });

        // on!(&mut decl.kind, DeclKind::Method { .. }, {
        //     self.end_scope();
        // });

        on!(
            &mut decl.kind,
            DeclKind::Protocol { .. }
                | DeclKind::Enum { .. }
                | DeclKind::Extend { .. }
                | DeclKind::Struct { .. },
            {
                self.resolver.nominal_stack.pop();
            }
        );

        // Mark public declarations
        if decl.visibility == Visibility::Public {
            match &decl.kind {
                DeclKind::Let { lhs, .. } => {
                    // For let bindings, mark all bound symbols as public
                    for (_, sym) in lhs.collect_binders() {
                        self.resolver.mark_public(sym);
                    }
                }
                DeclKind::Struct { name, body, .. }
                | DeclKind::Enum { name, body, .. }
                | DeclKind::Protocol { name, body, .. } => {
                    if let Ok(sym) = name.symbol() {
                        self.resolver.mark_public(sym);
                    }
                    // Also mark members (init, methods, nested extends) as public
                    for member in &body.decls {
                        match &member.kind {
                            DeclKind::Init { name, .. } => {
                                if let Ok(sym) = name.symbol() {
                                    self.resolver.mark_public(sym);
                                }
                            }
                            DeclKind::Method { func, .. } => {
                                if let Ok(sym) = func.name.symbol() {
                                    self.resolver.mark_public(sym);
                                }
                            }
                            DeclKind::EnumVariant(name, ..) => {
                                if let Ok(sym) = name.symbol() {
                                    self.resolver.mark_public(sym);
                                }
                            }
                            DeclKind::Property { name, .. } => {
                                if let Ok(sym) = name.symbol() {
                                    self.resolver.mark_public(sym);
                                }
                            }
                            // Handle nested extends (like extend Self: Protocol inside a struct)
                            DeclKind::Extend {
                                body: nested_body, ..
                            } => {
                                for nested_member in &nested_body.decls {
                                    if let DeclKind::Method { func, .. } = &nested_member.kind {
                                        if let Ok(sym) = func.name.symbol() {
                                            self.resolver.mark_public(sym);
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                DeclKind::Effect { name, .. } => {
                    if let Ok(sym) = name.symbol() {
                        self.resolver.mark_public(sym);
                    }
                }
                DeclKind::TypeAlias(name, ..) => {
                    if let Ok(sym) = name.symbol() {
                        self.resolver.mark_public(sym);
                    }
                }
                _ => {}
            }
        }

        // For Extend blocks, mark methods as public if the extended type is public
        // This happens regardless of the extend's own visibility
        if let DeclKind::Extend { name, body, .. } = &decl.kind {
            // Check if the extended type is public
            let extended_type_is_public = name
                .symbol()
                .map(|sym| self.resolver.phase.public_symbols.contains(&sym))
                .unwrap_or(false);

            if extended_type_is_public {
                // Mark all methods in this extend as public
                for member in &body.decls {
                    match &member.kind {
                        DeclKind::Method { func, .. } => {
                            if let Ok(sym) = func.name.symbol() {
                                self.resolver.mark_public(sym);
                            }
                        }
                        // Handle nested extends (like extend Self: Protocol inside a struct)
                        DeclKind::Extend { body: nested_body, .. } => {
                            for nested_member in &nested_body.decls {
                                if let DeclKind::Method { func, .. } = &nested_member.kind {
                                    if let Ok(sym) = func.name.symbol() {
                                        self.resolver.mark_public(sym);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    fn synthesize_init(&mut self, body: &mut Body, type_members: &TypeMembers, type_id: StructId) {
        let init_id = NodeID(FileID::SYNTHESIZED, self.node_ids.next_id());
        tracing::debug!("synthesizing init for type {type_id:?} as: {init_id:?}");

        let init_name = self
            .resolver
            .declare(&"init".into(), some!(Synthesized), init_id, Span::SYNTHESIZED);

        self.start_scope(None, init_id, false);

        // Need to synthesize an init
        let self_param_name = self.resolver.declare(
            &Name::Raw("self".into()),
            some!(ParamLocal),
            NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
            Span::SYNTHESIZED,
        );
        let mut params: Vec<Parameter> = vec![Parameter {
            id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
            span: Span::SYNTHESIZED,
            name: self_param_name.clone(),
            name_span: Span::SYNTHESIZED,
            type_annotation: Some(TypeAnnotation {
                id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                span: Span::SYNTHESIZED,
                kind: TypeAnnotationKind::SelfType(Name::SelfType(type_id.into())),
            }),
        }];

        let mut assignments: Vec<Node> = vec![];
        for property in type_members.properties.iter() {
            let DeclKind::Property {
                name,
                is_static,
                type_annotation,
                ..
            } = &property
            else {
                continue;
            };

            if *is_static {
                continue;
            }

            let name = self.resolver.declare(
                &Name::Raw(name.name_str()),
                some!(ParamLocal),
                NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                Span::SYNTHESIZED,
            );
            params.push(Parameter {
                id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                name: name.clone(),
                name_span: Span::SYNTHESIZED,
                type_annotation: type_annotation.clone(),
                span: Span::SYNTHESIZED,
            });

            let assignment = Node::Stmt(Stmt {
                id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                span: Span::SYNTHESIZED,
                kind: StmtKind::Assignment(
                    Expr {
                        id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                        kind: ExprKind::Member(
                            Some(
                                Expr {
                                    id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                                    span: Span::SYNTHESIZED,
                                    kind: ExprKind::Variable(self_param_name.clone()),
                                }
                                .into(),
                            ),
                            name.name_str().into(),
                            Span::SYNTHESIZED,
                        ),
                        span: Span::SYNTHESIZED,
                    }
                    .into(),
                    Expr {
                        id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                        kind: ExprKind::Variable(name),
                        span: Span::SYNTHESIZED,
                    }
                    .into(),
                ),
            });

            assignments.push(assignment);
        }

        assignments.push(Node::Stmt(Stmt {
            id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
            span: Span::SYNTHESIZED,
            kind: StmtKind::Expr(Expr {
                id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                span: Span::SYNTHESIZED,
                kind: ExprKind::Variable(self_param_name),
            }),
        }));

        let init = Decl {
            id: init_id,
            span: Span::SYNTHESIZED,
            visibility: Visibility::default(),
            kind: DeclKind::Init {
                name: init_name,
                params,
                body: Block {
                    id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                    span: Span::SYNTHESIZED,
                    args: vec![],
                    body: assignments,
                },
            },
        };

        self.end_scope();

        body.decls.insert(0, init);
    }
}
