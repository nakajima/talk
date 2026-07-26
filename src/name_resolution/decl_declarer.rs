use derive_visitor::VisitorMut;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    id_generator::IDGenerator,
    name::Name,
    name_resolution::{
        name_resolver::{NameResolver, NameResolverError, Scope},
        symbol::{StructId, Symbol, SymbolKind},
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        body::Body,
        decl::{Decl, DeclKind, Visibility},
        expr::{Expr, ExprKind},
        func::{Func, FuncOrigin},
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        parameter::{ParamMode, Parameter},
        pattern::PatternKind,
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
        type_application::TypeApplication,
    },
    on,
    span::Span,
};

#[derive(VisitorMut)]
#[visitor(FuncSignature, Decl(enter, exit), Block(enter, exit))]
pub struct DeclDeclarer<'a> {
    pub(super) resolver: &'a mut NameResolver,
    // For determining whether we need to synth an init
    type_members: FxHashMap<NodeID, TypeMembers>,
    // For synthesizing
    node_ids: &'a mut IDGenerator,
    // How many blocks deep the walk is: anything inside a block is local
    // territory, declared in resolution order by the resolver pass, not
    // here.
    block_depth: u32,
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
            block_depth: 0,
        }
    }

    #[instrument(skip(self))]
    pub fn start_scope(&mut self, id: NodeID) {
        let parent_id = self.resolver.current_scope_id;
        let depth = self
            .resolver
            .current_scope()
            .map(|s| s.depth + 1)
            .unwrap_or(1);
        let scope = Scope::new(id, parent_id, depth);
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
    /// For extend blocks, generics that already resolve to a concrete (non-TypeParameter) symbol
    /// (e.g. `Void`) are kept as-is rather than being redeclared as fresh type parameters.
    fn declare_generics(&mut self, generics: &mut [GenericDecl], is_extend: bool) {
        for generic in generics {
            if is_extend
                && let Some(resolved) = self.resolver.lookup(&generic.name)
                && let Ok(sym) = resolved.symbol()
                && !matches!(sym, Symbol::TypeParameter(..))
            {
                generic.name = resolved;
                continue;
            }
            generic.name = self.resolver.declare(
                &generic.name,
                SymbolKind::TypeParameter,
                generic.id,
                generic.name_span,
            );
        }
    }

    pub(super) fn predeclare_nominals(&mut self, decls: &[&Decl]) {
        // Two same-named nominals in one scope would silently collapse
        // onto one symbol (same kind) or overwrite each other's entry
        // (different kinds); ADR 0042 diagnoses instead.
        let mut seen: rustc_hash::FxHashSet<String> = Default::default();
        for decl in decls.iter() {
            match &decl.kind {
                DeclKind::Struct {
                    name, name_span, ..
                }
                | DeclKind::Enum {
                    name, name_span, ..
                }
                | DeclKind::Protocol {
                    name, name_span, ..
                } => {
                    if !seen.insert(name.name_str()) {
                        self.resolver.diagnostic(
                            decl.id,
                            NameResolverError::DuplicateDeclaration(name.name_str()),
                        );
                    }
                    let kind = match &decl.kind {
                        DeclKind::Struct { .. } => SymbolKind::Struct,
                        DeclKind::Enum { .. } => SymbolKind::Enum,
                        DeclKind::Protocol { .. } => SymbolKind::Protocol,
                        _ => unreachable!(),
                    };

                    let resolved = self.resolver.declare(name, kind, decl.id, *name_span);

                    // Mark as public if visibility is Public (needed for import resolution)
                    if decl.visibility == Visibility::Public
                        && let Ok(sym) = resolved.symbol()
                    {
                        self.resolver.mark_public(sym);
                    }
                }
                _ => {}
            }
        }
    }

    /// Predeclare effects across all ASTs so they're available for import resolution
    /// and cross-file effect references in function signatures.
    /// Called after `predeclare_nominals` so effect names are available across files
    /// without changing nominal predeclaration behavior.
    pub(super) fn predeclare_effects(&mut self, decls: &[&Decl]) {
        for decl in decls.iter() {
            if let DeclKind::Effect {
                name, name_span, ..
            } = &decl.kind
            {
                let resolved = self
                    .resolver
                    .declare(name, SymbolKind::Effect, decl.id, *name_span);

                if decl.visibility == Visibility::Public
                    && let Ok(sym) = resolved.symbol()
                {
                    self.resolver.mark_public(sym);
                }
            }
        }
    }

    /// Predeclare module-scope type aliases so imports can resolve public aliases
    /// before the full declaration walk resolves alias RHS annotations.
    pub(super) fn predeclare_type_aliases(&mut self, decls: &[&Decl]) {
        for decl in decls.iter() {
            if let DeclKind::TypeAlias(name, name_span, ..) = &decl.kind {
                let resolved =
                    self.resolver
                        .declare(name, SymbolKind::TypeAlias, decl.id, *name_span);
                if decl.visibility == Visibility::Public
                    && let Ok(sym) = resolved.symbol()
                {
                    self.resolver.mark_public(sym);
                }
            }
        }
    }

    /// Predeclare public top-level Let bindings as Globals so they're available during import resolution.
    /// Only handles simple Bind patterns (not destructuring).
    /// Only public bindings are predeclared since they're the only ones that can be imported.
    pub(super) fn predeclare_values(&mut self, decls: &[&Decl]) {
        use crate::types::callables::ArgumentLabel;
        // Public overloads coexist when their full callable names differ
        // (ADR 0041); non-callables (labels `None`) still collide by name.
        type ExportedLabels = Option<Vec<ArgumentLabel>>;
        let mut exported_names: FxHashMap<String, Vec<ExportedLabels>> = FxHashMap::default();

        for decl in decls.iter() {
            // Only predeclare public Let bindings
            if decl.visibility != Visibility::Public {
                continue;
            }
            if let DeclKind::Let { lhs, rhs, .. } = &decl.kind {
                // For simple bind patterns, predeclare as Global
                // Use lhs.id (pattern id) to match what declare_pattern uses
                if let PatternKind::Bind(name) = &lhs.kind {
                    let name_str = name.name_str();
                    let labels: ExportedLabels = match rhs {
                        Some(Expr {
                            kind: ExprKind::Func(func),
                            ..
                        }) if func.origin == FuncOrigin::Decl => Some(
                            crate::types::callables::CallableName::from_params(
                                name_str.clone(),
                                &func.params,
                                false,
                            )
                            .labels,
                        ),
                        _ => None,
                    };
                    let overloading = match exported_names.get(&name_str) {
                        None => false,
                        Some(entries) => {
                            if entries.iter().any(|entry| *entry == labels) || labels.is_none() {
                                self.resolver.diagnostic(
                                    lhs.id,
                                    NameResolverError::DuplicateExport(name_str),
                                );
                                continue;
                            }
                            true
                        }
                    };
                    exported_names
                        .entry(name_str.clone())
                        .or_default()
                        .push(labels);

                    // Pattern span is used for the binding since Bind pattern doesn't have name_span
                    // An overload sibling must never reuse the earlier
                    // public Global by name: it mints fresh.
                    let resolved = if overloading {
                        let minted =
                            self.resolver
                                .mint(name, SymbolKind::Global, lhs.id, lhs.span);
                        if let Ok(sym) = minted.symbol() {
                            self.resolver.bind_value(&name_str, sym);
                        }
                        minted
                    } else {
                        self.resolver
                            .declare(name, SymbolKind::Global, lhs.id, lhs.span)
                    };
                    if let Ok(sym) = resolved.symbol() {
                        self.resolver.mark_public(sym);
                        self.resolver.predeclared.insert(lhs.id, sym);
                    }
                } else {
                    // ADR 0042: every binder of a public destructuring
                    // pattern predeclares, so local-source imports and
                    // compiled modules observe the same export set.
                    let mut binders = Vec::new();
                    Self::collect_raw_binders(lhs, &mut binders);
                    for (name, id, span) in binders {
                        let name_str = name.name_str();
                        if exported_names.contains_key(&name_str) {
                            self.resolver
                                .diagnostic(id, NameResolverError::DuplicateExport(name_str));
                            continue;
                        }
                        exported_names.insert(name_str, vec![None]);
                        let resolved =
                            self.resolver
                                .declare(&name, SymbolKind::Global, id, span);
                        if let Ok(sym) = resolved.symbol() {
                            self.resolver.mark_public(sym);
                            self.resolver.predeclared.insert(id, sym);
                        }
                    }
                }
            }
        }
    }

    /// Binders a module-scope pattern will declare as Globals, mirroring
    /// `declare_pattern`'s traversal (record fields bind locals and are
    /// excluded).
    fn collect_raw_binders(
        pattern: &crate::node_kinds::pattern::Pattern,
        out: &mut Vec<(Name, NodeID, Span)>,
    ) {
        match &pattern.kind {
            PatternKind::Bind(name) => out.push((name.clone(), pattern.id, pattern.span)),
            PatternKind::Tuple(patterns) => {
                for pattern in patterns {
                    Self::collect_raw_binders(pattern, out);
                }
            }
            // Only the first alternative declares; later ones re-resolve.
            PatternKind::Or(patterns) => {
                if let Some(first) = patterns.first() {
                    Self::collect_raw_binders(first, out);
                }
            }
            PatternKind::Variant { fields, .. } => {
                for field in fields {
                    Self::collect_raw_binders(field, out);
                }
            }
            _ => {}
        }
    }

    fn enter_nominal(
        &mut self,
        id: NodeID,
        name: &mut Name,
        row_generics: Option<&mut [GenericDecl]>,
        generics: &mut [GenericDecl],
        decls: &[Decl],
        is_extend: bool,
    ) {
        // Should be set by predeclare_nominals for Struct/Enum/Protocol, but `extend` can target
        // a nominal declared in another file. If we still can't resolve it, keep the resolver
        // state consistent so we don't crash while walking the body.
        // Note: name_span is not available in this function signature, so we pass None.
        // The spans are already recorded by predeclare_nominals for Struct/Enum/Protocol.
        *name = self.resolver.lookup(name).unwrap_or(name.clone());

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
            let parent_symbol = parent.0;
            self.resolver
                .phase
                .child_types
                .entry(parent_symbol)
                .or_default()
                .insert(name.name_str().into(), sym);
            // Nested types display qualified (`Res.A`, composing down
            // chains) — the parent's recorded name is already qualified
            // by the time its children declare.
            if !is_extend
                && matches!(sym, Symbol::Struct(_) | Symbol::Enum(_))
                && let Some(owner_name) = self.resolver.phase.symbol_names.get(&parent_symbol)
            {
                let qualified = format!("{owner_name}.{}", name.name_str());
                self.resolver.phase.symbol_names.insert(sym, qualified);
            }
        }

        self.resolver.nominal_stack.push((sym, id));
        self.type_members.insert(id, TypeMembers::default());

        self.start_scope(id);
        self.resolver
            .current_scope_mut()
            .expect("didn't get current scope")
            .types
            .insert("Self".into(), sym);

        // A protocol extension body sees the protocol's member type names
        // (associated types, typealiases) unqualified, like the protocol
        // body itself.
        if is_extend && matches!(sym, Symbol::Protocol(_)) {
            let children = self.resolver.phase.child_types.get(&sym).cloned();
            if let Some(children) = children {
                let scope = self
                    .resolver
                    .current_scope_mut()
                    .expect("didn't get current scope");
                for (label, child) in children {
                    scope.types.insert(label.to_string(), child);
                }
            }
        }

        if let Some(row_generics) = row_generics {
            self.declare_generics(row_generics, true);
        }
        self.declare_generics(generics, is_extend);
        if !is_extend {
            let children = self.resolver.phase.child_types.entry(sym).or_default();
            for generic in generics {
                if let Ok(param) = generic.name.symbol() {
                    children.insert(generic.name.name_str().into(), param);
                }
            }
        }

        self.predeclare_nominals(decls.iter().collect_vec().as_slice());
    }

    fn enter_extend(
        &mut self,
        id: NodeID,
        head: &mut TypeApplication,
        binders: &mut [GenericDecl],
        decls: &[Decl],
    ) {
        let name = &mut head.name;
        *name = self.resolver.lookup(name).unwrap_or(name.clone());
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

        self.resolver.nominal_stack.push((sym, id));
        self.type_members.insert(id, TypeMembers::default());
        self.start_scope(id);
        self.resolver
            .current_scope_mut()
            .expect("didn't get current scope")
            .types
            .insert("Self".into(), sym);

        if matches!(sym, Symbol::Protocol(_))
            && let Some(children) = self.resolver.phase.child_types.get(&sym).cloned()
        {
            let scope = self
                .resolver
                .current_scope_mut()
                .expect("didn't get current scope");
            for (label, child) in children {
                scope.types.insert(label.to_string(), child);
            }
        }

        self.declare_generics(binders, false);
        self.predeclare_nominals(decls.iter().collect_vec().as_slice());
    }

    ///////////////////////////////////////////////////////////////////////////
    // Blocks
    ///////////////////////////////////////////////////////////////////////////
    // Blocks (function bodies included) are local territory: their
    // scopes, binders, and nested funcs are declared in resolution order
    // by the resolver pass. This pass only tracks how deep it is, so
    // module-scope handling doesn't fire inside them.
    fn enter_block(&mut self, _block: &mut Block) {
        self.block_depth += 1;
    }

    fn exit_block(&mut self, _block: &mut Block) {
        self.block_depth -= 1;
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
                *name =
                    self.resolver
                        .declare(name, SymbolKind::MethodRequirement, func.id, func_span);

                self.start_scope(func.id);

                self.declare_generics(generics, false);

                for param in params {
                    param.name = self.resolver.declare(
                        &param.name,
                        SymbolKind::ParamLocal,
                        param.id,
                        param.name_span,
                    );
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
                self.enter_nominal(decl.id, name, None, generics, &body.decls, false);
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
                self.enter_nominal(decl.id, name, None, generics, &body.decls, false);
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
                self.enter_nominal(decl.id, name, None, generics, &body.decls, false);
            }
        );

        on!(
            &mut decl.kind,
            DeclKind::Extend {
                binders,
                head,
                body,
                ..
            },
            {
                self.enter_extend(decl.id, head, binders, &body.decls);
            }
        );

        on!(
            &mut decl.kind,
            DeclKind::TypeAlias(lhs_name, name_span, ..),
            {
                *lhs_name =
                    self.resolver
                        .declare(lhs_name, SymbolKind::TypeAlias, decl.id, *name_span);

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
            }
        );

        on!(
            &mut decl.kind,
            DeclKind::EnumVariant {
                name,
                name_span,
                generics,
                ..
            },
            {
                *name = self
                    .resolver
                    .declare(name, SymbolKind::Variant, decl.id, *name_span);
                self.start_scope(decl.id);
                self.declare_generics(generics, false);
            }
        );

        on!(
            &mut decl.kind,
            DeclKind::Method {
                func: box Func { name, name_span, generics, .. },
                is_static,
                ..
            },
            {
                *name = if *is_static {
                    self.resolver.declare(name, SymbolKind::StaticMethod, decl.id, *name_span)
                } else {
                    self.resolver.declare(name, SymbolKind::InstanceMethod, decl.id, *name_span)
                };

                // self.start_scope(name.symbol().ok(), *id, true);
                self.declare_generics(generics, false);
            }
        );

        on!(&mut decl.kind, DeclKind::Associated { generic, .. }, {
            generic.name = self.resolver.declare(
                &generic.name,
                SymbolKind::AssociatedType,
                decl.id,
                generic.name_span,
            );
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
                name,
                span,
                generics,
                ..
            }),
            {
                // FuncSignature doesn't have name_span, use its span
                *name = self
                    .resolver
                    .declare(name, SymbolKind::Global, decl.id, *span);

                self.declare_generics(generics, false);
            }
        );

        let decl_kind = decl.kind.clone();

        on!(
            &mut decl.kind,
            DeclKind::Property {
                name,
                name_span,
                ..
            },
            {
                *name = self
                    .resolver
                    .declare(name, SymbolKind::Property, decl.id, *name_span);
                let id = self
                    .resolver
                    .current_scope_id
                    .expect("didn't get current scope id");
                self.type_members
                    .entry(id)
                    .or_default()
                    .properties
                    .push(decl_kind.clone());
            }
        );

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
            *name = self
                .resolver
                .declare(name, SymbolKind::Initializer, decl.id, decl.span);

            self.start_scope(decl.id);
        });

        on!(&mut decl.kind, DeclKind::Let { lhs, rhs, .. }, {
            // Module-scope lets only: they predeclare (order-independent,
            // rule 4). Locals declare at their point in the resolver pass.
            if self.block_depth == 0 {
                // A public binding predeclared for import resolution keeps
                // its exact symbol — reuse-by-name would collapse overload
                // siblings onto one declaration (ADR 0041).
                if let Some(&predeclared) = self.resolver.predeclared.get(&lhs.id)
                    && let PatternKind::Bind(name) = &mut lhs.kind
                {
                    *name = Name::Resolved(predeclared, name.name_str());
                } else {
                    self.resolver.declare_pattern(lhs, SymbolKind::Global);
                }
                // A lowered `func` declaration joins its scope's overload
                // set (ADR 0041).
                if let PatternKind::Bind(name) = &lhs.kind
                    && let Ok(symbol) = name.symbol()
                    && let Some(Expr {
                        kind: ExprKind::Func(func),
                        ..
                    }) = rhs
                    && func.origin == FuncOrigin::Decl
                {
                    self.resolver.register_callable(
                        symbol,
                        &name.name_str(),
                        &func.params,
                        decl.id,
                    );
                }
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
                *name = self
                    .resolver
                    .declare(name, SymbolKind::Effect, decl.id, *name_span);

                // Start a scope for the effect's generics and params
                self.start_scope(decl.id);

                self.declare_generics(generics, false);

                for param in params {
                    param.name = self.resolver.declare(
                        &param.name,
                        SymbolKind::ParamLocal,
                        param.id,
                        param.name_span,
                    );
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
                    self.synthesize_init(body, &type_members, *type_id, decl.id.0);
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
                | DeclKind::Effect { .. }
                | DeclKind::EnumVariant { .. },
            {
                self.end_scope();
            }
        );

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

        // ADR 0042: record the authored visibility on each declared
        // symbol's record; an authored `pub` concludes public on its
        // own declaration (members included — owners no longer smear
        // visibility over their members).
        match &decl.kind {
            DeclKind::Let { lhs, .. } if self.block_depth == 0 => {
                for (_, sym) in lhs.collect_binders() {
                    self.resolver
                        .record_declared_visibility(sym, decl.visibility);
                }
            }
            _ => {
                if let Some(sym) = Self::declared_symbol(&decl.kind) {
                    self.resolver
                        .record_declared_visibility(sym, decl.visibility);
                    if decl.visibility == Visibility::Public {
                        self.resolver.mark_public(sym);
                    }
                }
            }
        }

        // ADR 0042: a public member requires a publicly accessible
        // owner. Public nominals concluded their visibility during
        // predeclaration, so a private conclusion here is final.
        let private_owner = match &decl.kind {
            DeclKind::Struct { name, body, .. }
            | DeclKind::Enum { name, body, .. }
            | DeclKind::Protocol { name, body, .. }
                if decl.visibility == Visibility::Private =>
            {
                Some((name.name_str(), body))
            }
            DeclKind::Extend { head, body, .. } => {
                let extended_is_public = head.symbol().map_or(true, |sym| {
                    // A head without a local record is an imported
                    // type, which is public by construction.
                    !self.resolver.phase.declarations.contains_key(&sym)
                        || self.resolver.phase.is_public(&sym)
                });
                if extended_is_public {
                    None
                } else {
                    Some((head.name.name_str(), body))
                }
            }
            _ => None,
        };
        if let Some((owner_name, body)) = private_owner {
            for member in &body.decls {
                if member.visibility == Visibility::Public {
                    let member_name = Self::declared_symbol(&member.kind)
                        .and_then(|sym| self.resolver.phase.symbol_names.get(&sym).cloned())
                        .unwrap_or_else(|| "member".into());
                    self.resolver.diagnostic(
                        member.id,
                        NameResolverError::PublicMemberPrivateOwner {
                            member: member_name,
                            owner: owner_name.clone(),
                        },
                    );
                }
            }
        }

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
                    // Only inherited-visibility members conclude public
                    // from their owner (ADR 0042): the synthesized
                    // memberwise initializer, enum cases, and protocol
                    // requirements. Every other member needs its own
                    // `pub`, handled by the authored-visibility arm
                    // above.
                    for member in &body.decls {
                        match &member.kind {
                            DeclKind::Init { name, .. } => {
                                // Explicit initializers need their own
                                // `pub`; only the resolver-synthesized
                                // memberwise init inherits.
                                if let Ok(sym) = name.symbol()
                                    && matches!(sym, Symbol::Synthesized(_))
                                {
                                    self.resolver.mark_public(sym);
                                }
                            }
                            DeclKind::EnumVariant { name, .. } => {
                                if let Ok(sym) = name.symbol() {
                                    self.resolver.mark_public(sym);
                                }
                            }
                            DeclKind::MethodRequirement { signature, .. }
                            | DeclKind::InitRequirement { signature } => {
                                if let Ok(sym) = signature.name.symbol() {
                                    self.resolver.mark_public(sym);
                                }
                            }
                            DeclKind::Associated { generic, .. } => {
                                if let Ok(sym) = generic.name.symbol() {
                                    self.resolver.mark_public(sym);
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

    }

    /// The symbol a declaration introduced, for single-symbol kinds.
    /// `Let` binds through its pattern and is handled separately.
    fn declared_symbol(kind: &DeclKind) -> Option<Symbol> {
        match kind {
            DeclKind::Struct { name, .. }
            | DeclKind::Enum { name, .. }
            | DeclKind::Protocol { name, .. }
            | DeclKind::Effect { name, .. }
            | DeclKind::EnumVariant { name, .. }
            | DeclKind::Property { name, .. }
            | DeclKind::Init { name, .. }
            | DeclKind::TypeAlias(name, ..) => name.symbol().ok(),
            DeclKind::Method { func, .. } => func.name.symbol().ok(),
            DeclKind::FuncSignature(signature) => signature.name.symbol().ok(),
            DeclKind::Func(func) => func.name.symbol().ok(),
            DeclKind::Associated { generic, .. } => generic.name.symbol().ok(),
            DeclKind::MethodRequirement { signature, .. }
            | DeclKind::InitRequirement { signature } => signature.name.symbol().ok(),
            DeclKind::Import(_) | DeclKind::Macro { .. } | DeclKind::Extend { .. }
            | DeclKind::Let { .. } => None,
        }
    }

    fn synthesize_init(
        &mut self,
        body: &mut Body,
        type_members: &TypeMembers,
        type_id: StructId,
        file_id: FileID,
    ) {
        let init_id = NodeID(file_id, self.node_ids.next_id());
        tracing::debug!("synthesizing init for type {type_id:?} as: {init_id:?}");

        let init_name = self.resolver.declare(
            &"init".into(),
            SymbolKind::Synthesized,
            init_id,
            Span::SYNTHESIZED,
        );

        self.start_scope(init_id);

        // Need to synthesize an init
        let self_param_name = self.resolver.declare(
            &Name::Raw("self".into()),
            SymbolKind::ParamLocal,
            NodeID(file_id, self.node_ids.next_id()),
            Span::SYNTHESIZED,
        );
        let mut params: Vec<Parameter> = vec![Parameter {
            label: None,
            label_span: None,
            mode: None,
            mode_span: None,
            id: NodeID(file_id, self.node_ids.next_id()),
            span: Span::SYNTHESIZED,
            name: self_param_name.clone(),
            name_span: Span::SYNTHESIZED,
            type_annotation: Some(TypeAnnotation {
                id: NodeID(file_id, self.node_ids.next_id()),
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
                SymbolKind::ParamLocal,
                NodeID(file_id, self.node_ids.next_id()),
                Span::SYNTHESIZED,
            );
            params.push(Parameter {
                label: None,
                label_span: None,
                // Memberwise init params consume their arguments (ADR 0018),
                // like every other init parameter.
                mode: Some(ParamMode::Consume),
                mode_span: None,
                id: NodeID(file_id, self.node_ids.next_id()),
                name: name.clone(),
                name_span: Span::SYNTHESIZED,
                type_annotation: type_annotation.clone(),
                span: Span::SYNTHESIZED,
            });

            let assignment = Node::Stmt(Stmt {
                id: NodeID(file_id, self.node_ids.next_id()),
                span: Span::SYNTHESIZED,
                kind: StmtKind::Assignment(
                    Expr {
                        id: NodeID(file_id, self.node_ids.next_id()),
                        kind: ExprKind::Member(
                            Some(
                                Expr {
                                    id: NodeID(file_id, self.node_ids.next_id()),
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
                        id: NodeID(file_id, self.node_ids.next_id()),
                        kind: ExprKind::Variable(name),
                        span: Span::SYNTHESIZED,
                    }
                    .into(),
                ),
            });

            assignments.push(assignment);
        }

        assignments.push(Node::Stmt(Stmt {
            id: NodeID(file_id, self.node_ids.next_id()),
            span: Span::SYNTHESIZED,
            kind: StmtKind::Expr(Expr {
                id: NodeID(file_id, self.node_ids.next_id()),
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
                    id: NodeID(file_id, self.node_ids.next_id()),
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
