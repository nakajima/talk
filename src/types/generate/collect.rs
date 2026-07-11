use super::*;

use crate::types::catalog::Grade;

impl<'s, 'a> CatalogBuilder<'s, 'a> {
    // ----- Declaration collection ---------------------------------------

    pub(super) fn collect(
        &mut self,
        asts: &'a IndexMap<Source, AST<NameResolved>>,
    ) -> Collected<'a> {
        self.collect_type_aliases(asts);
        self.level = OUTER_LEVEL;
        let mut decls: IndexMap<Symbol, TopEntry<'a>> = IndexMap::default();
        let mut stmts: Vec<&'a Stmt> = vec![];
        let mut destructuring_lets: Vec<&'a Decl> = vec![];
        let mut extends: Vec<ExtendWork<'a>> = vec![];
        let mut protocol_defaults: Vec<(Symbol, Symbol, &'a Func)> = vec![];

        let mut top_decls: Vec<&'a Decl> = vec![];
        for ast in asts.values() {
            for root in &ast.roots {
                match root {
                    Node::Decl(decl) => top_decls.push(decl),
                    Node::Stmt(stmt) => stmts.push(stmt),
                    _ => {}
                }
            }
        }

        let mut struct_decls: Vec<(Symbol, &'a Decl)> = vec![];
        for decl in &top_decls {
            match &decl.kind {
                DeclKind::Struct { name, .. } => {
                    if let Ok(symbol) = name.symbol() {
                        self.register_struct(symbol, decl);
                        struct_decls.push((symbol, decl));
                        decls.insert(symbol, TopEntry::Struct { decl });
                    }
                }
                DeclKind::Enum { name, .. } => {
                    if let Ok(symbol) = name.symbol() {
                        self.register_enum(symbol, decl);
                        decls.insert(symbol, TopEntry::Enum { decl });
                    }
                }
                DeclKind::Protocol { name, .. } => {
                    if let Ok(symbol) = name.symbol() {
                        self.register_protocol(symbol, decl, &mut protocol_defaults);
                    }
                }
                DeclKind::Effect {
                    name,
                    generics,
                    where_clause,
                    params,
                    ret,
                    ..
                } => {
                    if let Ok(symbol) = name.symbol() {
                        self.register_effect(symbol, generics, where_clause.as_ref(), params, ret);
                    }
                }
                _ => {}
            }
        }

        self.register_catalog_type_aliases();
        self.collect_explicit_conformance_claims(&top_decls, &struct_decls);

        // Default-only protocol extensions register before conforming extends so their
        // requirements are witnessable regardless of declaration order. Protocol-head
        // conformance extends use the normal conformance-row path below.
        for decl in &top_decls {
            if let Some(protocol) = self.protocol_extension_head(decl)
                && matches!(&decl.kind, DeclKind::Extend { conformances, .. } if conformances.is_empty())
            {
                self.register_protocol_extension(protocol, decl, &mut protocol_defaults);
            }
        }

        for decl in &top_decls {
            match &decl.kind {
                DeclKind::Let {
                    lhs:
                        Pattern {
                            kind: PatternKind::Bind(name),
                            ..
                        },
                    type_annotation,
                    rhs,
                } => {
                    if let Ok(symbol) = name.symbol() {
                        if let Some(Expr {
                            kind: ExprKind::Func(func),
                            ..
                        }) = rhs
                        {
                            self.register_func_bounds(func);
                        }
                        decls.insert(
                            symbol,
                            TopEntry::Let {
                                decl,
                                annotation: type_annotation.as_ref(),
                                rhs: rhs.as_ref(),
                            },
                        );
                    }
                }
                DeclKind::Let { .. } => destructuring_lets.push(decl),
                DeclKind::Extend { conformances, .. } => {
                    let protocol_default_extension =
                        self.protocol_extension_head(decl).is_some() && conformances.is_empty();
                    if !protocol_default_extension
                        && let Some(work) = self.register_extend(decl, None)
                    {
                        extends.push(work);
                    }
                }
                DeclKind::Struct { .. }
                | DeclKind::Enum { .. }
                | DeclKind::Protocol { .. }
                | DeclKind::Effect { .. }
                | DeclKind::TypeAlias(..)
                | DeclKind::Import(_) => {}
                other => self.unsupported(decl.id, decl_kind_name(other)),
            }
        }

        for (symbol, decl) in &struct_decls {
            let DeclKind::Struct { body, .. } = &decl.kind else {
                continue;
            };
            for member in &body.decls {
                if matches!(member.kind, DeclKind::Extend { .. })
                    && let Some(work) = self.register_extend(member, Some(*symbol))
                {
                    extends.push(work);
                }
            }
        }

        self.validate_marker_conformances();

        Collected {
            decls,
            stmts,
            destructuring_lets,
            extends,
            protocol_defaults,
        }
    }

    pub(super) fn collect_type_aliases(&mut self, asts: &'a IndexMap<Source, AST<NameResolved>>) {
        use derive_visitor::{Drive, Visitor};

        #[derive(Visitor)]
        #[visitor(Decl(enter))]
        struct AliasCollector {
            aliases: Vec<(Symbol, TypeAnnotation)>,
        }

        impl AliasCollector {
            fn enter_decl(&mut self, decl: &Decl) {
                if let DeclKind::TypeAlias(name, _, rhs) = &decl.kind
                    && let Ok(symbol) = name.symbol()
                {
                    self.aliases.push((symbol, rhs.clone()));
                }
            }
        }

        let mut owners: FxHashMap<Symbol, Symbol> = FxHashMap::default();
        for (owner, children) in &self.resolved.child_types {
            for child in children.values() {
                if matches!(child, Symbol::TypeAlias(_)) {
                    owners.insert(*child, *owner);
                }
            }
        }

        let mut scopes: FxHashMap<Symbol, NodeID> = FxHashMap::default();
        for (scope_id, scope) in &self.resolved.scopes {
            for symbol in scope.types.values() {
                if matches!(symbol, Symbol::TypeAlias(_)) {
                    scopes.insert(*symbol, *scope_id);
                }
            }
        }

        let mut collector = AliasCollector { aliases: vec![] };
        for ast in asts.values() {
            for root in &ast.roots {
                root.drive(&mut collector);
            }
        }

        for (symbol, rhs) in collector.aliases {
            let owner = owners.get(&symbol).copied();
            let exportable = owner.is_some()
                || scopes
                    .get(&symbol)
                    .map(|scope_id| scope_id.1 == 0)
                    .unwrap_or(false);
            self.type_aliases.insert(
                symbol,
                TypeAliasDef {
                    rhs,
                    owner,
                    exportable,
                },
            );
        }
    }

    pub(super) fn register_catalog_type_aliases(&mut self) {
        let aliases: Vec<(Symbol, TypeAliasDef)> = self
            .type_aliases
            .iter()
            .filter_map(|(symbol, alias)| alias.exportable.then_some((*symbol, alias.clone())))
            .collect();

        for (symbol, alias) in aliases {
            let ty = self.lower_type_alias(symbol, alias.rhs.id, None);
            let params = alias
                .owner
                .map(|owner| nominal_params(self.catalog, owner))
                .unwrap_or_default();
            self.catalog.type_aliases.insert(
                symbol,
                TypeAliasInfo {
                    params,
                    ty: ty.sanitize_for_export(symbol),
                },
            );
        }
    }

    pub(super) fn collect_explicit_conformance_claims(
        &mut self,
        top_decls: &[&'a Decl],
        struct_decls: &[(Symbol, &'a Decl)],
    ) {
        for decl in top_decls {
            if let DeclKind::Extend {
                name,
                conformances,
                generics,
                ..
            } = &decl.kind
                && let Ok(head) = name.symbol()
            {
                let self_params: Vec<Symbol> = if generics.is_empty() {
                    self.catalog
                        .structs
                        .get(&head)
                        .map(|info| info.params.clone())
                        .or_else(|| {
                            self.catalog
                                .enums
                                .get(&head)
                                .map(|info| info.params.clone())
                        })
                        .unwrap_or_default()
                } else {
                    generic_symbols(generics)
                };
                let self_ty =
                    Ty::Nominal(head, self_params.iter().copied().map(Ty::Param).collect());
                for conformance in conformances {
                    if let Some((protocol, _)) =
                        self.lower_protocol_ref_with_self(conformance, Some(&self_ty))
                    {
                        self.record_marker_claim(head, protocol.protocol, decl.id);
                        self.explicit_conformances.insert((head, protocol));
                    }
                }
            }
        }

        for (head, decl) in struct_decls {
            let DeclKind::Struct { body, .. } = &decl.kind else {
                continue;
            };
            let self_params = self
                .catalog
                .structs
                .get(head)
                .map(|info| info.params.clone())
                .unwrap_or_default();
            let self_ty = Ty::Nominal(*head, self_params.iter().copied().map(Ty::Param).collect());
            for member in &body.decls {
                if let DeclKind::Extend { conformances, .. } = &member.kind {
                    for conformance in conformances {
                        if let Some((protocol, _)) =
                            self.lower_protocol_ref_with_self(conformance, Some(&self_ty))
                        {
                            self.record_marker_claim(*head, protocol.protocol, member.id);
                            self.explicit_conformances.insert((*head, protocol));
                        }
                    }
                }
            }
        }
    }

    fn record_marker_claim(&mut self, head: Symbol, protocol: Symbol, node: NodeID) {
        if matches!(protocol, Symbol::Copy | Symbol::CheapClone | Symbol::Deinit) {
            self.marker_claims.push((head, protocol, node));
        }
    }

    /// Validate the substructural marker protocols once the whole catalog is
    /// collected: a `linear` declaration may not claim any of them (Copy
    /// duplicates the value, CheapClone shares it, Deinit silently discards
    /// it), and `Copy`/`CheapClone` require every field to satisfy the
    /// marker.
    fn validate_marker_conformances(&mut self) {
        for (head, protocol, node) in std::mem::take(&mut self.marker_claims) {
            let declared_linear = self
                .catalog
                .structs
                .get(&head)
                .map(|info| info.linear)
                .or_else(|| self.catalog.enums.get(&head).map(|info| info.linear))
                .unwrap_or(false);
            if declared_linear {
                self.diagnostics.errors.push((
                    TypeError::LinearConformance {
                        ty: head.to_string(),
                        protocol: protocol.to_string(),
                    },
                    node,
                ));
                continue;
            }
            // A `'heap` value is a shared reference: copying or cheap-cloning
            // the handle is meaningless as a *value* operation, and Deinit
            // dispatch belongs to the region's teardown walk.
            if self.catalog.is_heap(head) && protocol != Symbol::Deinit {
                self.diagnostics.errors.push((
                    TypeError::HeapConformance {
                        ty: head.to_string(),
                        protocol: protocol.to_string(),
                    },
                    node,
                ));
                continue;
            }
            if protocol == Symbol::Deinit {
                continue;
            }
            for (field, ty) in self.marker_checked_fields(head) {
                if !self.satisfies_marker(&ty, protocol) {
                    self.diagnostics.errors.push((
                        TypeError::NonConformingField {
                            protocol: protocol.to_string(),
                            field,
                            ty: ty.render_mono(),
                        },
                        node,
                    ));
                }
            }
        }
    }

    /// The stored payload types a Copy/CheapClone claim must cover: struct
    /// fields, or every enum variant's constructor parameters.
    fn marker_checked_fields(&self, head: Symbol) -> Vec<(String, Ty)> {
        if let Some(info) = self.catalog.structs.get(&head) {
            return info
                .fields
                .iter()
                .map(|(name, (_, ty))| (name.clone(), ty.clone()))
                .collect();
        }
        if let Some(info) = self.catalog.enums.get(&head) {
            return info
                .variants
                .iter()
                .flat_map(|(name, variant)| match &variant.constructor_scheme.ty {
                    Ty::Func(payloads, ..) => payloads
                        .iter()
                        .map(|ty| (name.clone(), ty.clone()))
                        .collect(),
                    _ => vec![],
                })
                .collect();
        }
        vec![]
    }

    fn satisfies_marker(&self, ty: &Ty, marker: Symbol) -> bool {
        match ty {
            // Error is poison; a variable here means the field type is still
            // being collected — the conformance's own use sites will re-check.
            Ty::Error | Ty::Var(_) => true,
            // A unique value is the sole reference: never Copy/CheapClone.
            Ty::Unique(_) => false,
            Ty::Nominal(symbol, args) => {
                // Storage and Array are refcounted buffers: cloning bumps
                // the buffer without touching elements, so element grade is
                // irrelevant.
                if marker == Symbol::CheapClone
                    && matches!(*symbol, Symbol::Storage | Symbol::Array)
                {
                    return true;
                }
                let head_ok = match marker {
                    Symbol::Copy => self.catalog.grade_of(*symbol) == Grade::Copy,
                    // CheapClone: Copy fields are fine, and CheapClone-
                    // conforming fields are fine.
                    _ => {
                        self.catalog.grade_of(*symbol) == Grade::Copy
                            || self
                                .catalog
                                .has_bare_conformance(*symbol, Symbol::CheapClone)
                    }
                };
                head_ok && args.iter().all(|arg| self.satisfies_marker(arg, marker))
            }
            Ty::Param(symbol) => self
                .catalog
                .param_bounds
                .get(symbol)
                .is_some_and(|bounds| bounds.contains(&ProtocolRef::bare(marker))),
            Ty::Tuple(items) => items.iter().all(|item| self.satisfies_marker(item, marker)),
            Ty::Record(row) => {
                row.tail.is_none()
                    && row
                        .fields
                        .iter()
                        .all(|(_, field)| self.satisfies_marker(field, marker))
            }
            // An effect argument is runtime-inert: it never blocks a
            // marker (Copy/CheapClone judge values, not rows).
            Ty::Eff(_) => true,
            Ty::Borrow(..) | Ty::Func(..) | Ty::Any { .. } | Ty::Proj(..) => false,
        }
    }

    pub(super) fn register_struct(&mut self, symbol: Symbol, decl: &Decl) {
        let DeclKind::Struct {
            generics,
            where_clause,
            body,
            linear,
            heap,
            ..
        } = &decl.kind
        else {
            return;
        };
        self.register_generic_bounds(generics);
        self.register_where_bounds(where_clause.as_ref());
        let params = generic_symbols(generics);
        let self_ty = Ty::Nominal(symbol, params.iter().map(|p| Ty::Param(*p)).collect());
        self.self_types.push(self_ty);
        let predicates = self.declared_predicates(generics, where_clause.as_ref());
        self.self_types.pop();
        let mut info = StructInfo {
            linear: *linear,
            heap: *heap,
            params,
            predicates,
            ..Default::default()
        };
        for member in &body.decls {
            match &member.kind {
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    ..
                } => {
                    if *is_static {
                        self.unsupported(member.id, "static properties");
                        continue;
                    }
                    let Ok(property) = name.symbol() else {
                        continue;
                    };
                    let ty = match type_annotation {
                        Some(annotation) => self.lower_annotation(annotation),
                        None => {
                            // Default-valued properties still need explicit
                            // type annotations so collection can catalog the
                            // struct shape before bodies are checked.
                            self.unsupported(member.id, "properties without type annotations");
                            Ty::Error
                        }
                    };
                    info.fields.insert(name.name_str(), (property, ty));
                }
                DeclKind::Method {
                    func, is_static, ..
                } => {
                    let Ok(method) = func.name.symbol() else {
                        continue;
                    };
                    let table = if *is_static {
                        &mut info.statics
                    } else {
                        &mut info.methods
                    };
                    table.insert(func.name.name_str(), method);
                }
                DeclKind::Init { name, .. } => {
                    if let Ok(init) = name.symbol() {
                        info.inits.push(init);
                    }
                }
                // Nested `extend Self: P` registers in pass B. Type aliases
                // are transparent type declarations, not value members.
                DeclKind::Extend { .. } | DeclKind::TypeAlias(..) => {}
                other => self.unsupported(member.id, decl_kind_name(other)),
            }
        }
        self.mint_field_eff_params(&mut info);
        for label in info.fields.keys().chain(info.methods.keys()) {
            self.catalog.add_owner(label, MemberOwner::Nominal(symbol));
        }
        self.catalog.structs.insert(symbol, info);
    }

    /// Quantify the struct's closure-field effect rows: every free row
    /// tail minted by the field annotations becomes an implicit rigid
    /// effect param (one per distinct variable), instantiated per
    /// construction and carried as a `Ty::Eff` argument on the nominal
    /// head. Without this the module shares ONE row variable per field,
    /// so any effectful construction contaminates every other use.
    fn mint_field_eff_params(&mut self, info: &mut StructInfo) {
        use crate::types::ty::{EffTail, TyFold};

        struct Mint<'a> {
            symbols: &'a mut Symbols,
            module_id: ModuleId,
            minted: FxHashMap<u32, Symbol>,
            order: Vec<Symbol>,
        }
        impl TyFold for Mint<'_> {
            fn fold_eff_tail(&mut self, tail: &Option<EffTail>) -> Option<EffTail> {
                match tail {
                    Some(EffTail::Var(v)) => {
                        let param = *self.minted.entry(v.0).or_insert_with(|| {
                            let param =
                                Symbol::Synthesized(self.symbols.next_synthesized(self.module_id));
                            self.order.push(param);
                            param
                        });
                        Some(EffTail::Param(param))
                    }
                    other => other.clone(),
                }
            }
        }

        let mut mint = Mint {
            symbols: self.symbols,
            module_id: self.module_id,
            minted: FxHashMap::default(),
            order: vec![],
        };
        for (_, ty) in info.fields.values_mut() {
            *ty = mint.fold_ty(ty);
        }
        info.eff_params = mint.order;
    }

    pub(super) fn register_enum(&mut self, symbol: Symbol, decl: &Decl) {
        let DeclKind::Enum {
            generics,
            where_clause,
            body,
            linear,
            ..
        } = &decl.kind
        else {
            return;
        };
        self.register_generic_bounds(generics);
        self.register_where_bounds(where_clause.as_ref());
        let params = generic_symbols(generics);
        let result = Ty::Nominal(symbol, params.iter().map(|p| Ty::Param(*p)).collect());
        self.self_types.push(result.clone());
        let predicates = self.declared_predicates(generics, where_clause.as_ref());
        self.self_types.pop();
        let mut info = Enum {
            linear: *linear,
            params,
            predicates,
            ..Default::default()
        };
        for member in &body.decls {
            match &member.kind {
                DeclKind::EnumVariant {
                    name,
                    generics: case_generics,
                    payloads: payload_annotations,
                    payload_labels: declared_payload_labels,
                    result: case_result,
                    ..
                } => {
                    let Ok(variant) = name.symbol() else { continue };
                    self.register_generic_bounds(case_generics);
                    self.report_variant_generic_shadowing(generics, case_generics);

                    let payloads = payload_annotations
                        .iter()
                        .map(|a| self.lower_annotation(a))
                        .collect();
                    let payload_labels: Vec<Option<String>> = declared_payload_labels
                        .iter()
                        .map(|label| label.as_ref().map(Name::name_str))
                        .collect();
                    let mut seen_labels = FxHashSet::default();
                    for label in payload_labels.iter().flatten() {
                        if !seen_labels.insert(label.clone()) {
                            self.diagnostics.errors.push((
                                TypeError::DuplicateVariantPayloadLabel {
                                    variant: name.name_str(),
                                    label: label.clone(),
                                },
                                member.id,
                            ));
                        }
                    }
                    let case_result_ty = case_result
                        .as_ref()
                        .map(|annotation| self.lower_annotation(annotation))
                        .unwrap_or_else(|| result.clone());
                    if !self.valid_variant_result(symbol, info.params.len(), &case_result_ty) {
                        self.diagnostics.errors.push((
                            TypeError::InvalidVariantResultType {
                                variant: name.name_str(),
                            },
                            case_result
                                .as_ref()
                                .map_or(member.id, |annotation| annotation.id),
                        ));
                    } else if case_result.is_some() && case_result_ty == result {
                        self.diagnostics.warnings.push((
                            TypeError::RedundantVariantResultType {
                                variant: name.name_str(),
                            },
                            case_result
                                .as_ref()
                                .map_or(member.id, |annotation| annotation.id),
                        ));
                    }

                    let predicates = self.declared_predicates(case_generics, None);
                    let all_params: Vec<Symbol> = info
                        .params
                        .iter()
                        .copied()
                        .chain(
                            case_generics
                                .iter()
                                .filter_map(|generic| generic.name.symbol().ok()),
                        )
                        .collect();
                    let universe: FxHashSet<Symbol> = all_params.iter().copied().collect();
                    let mut mentioned = FxHashSet::default();
                    for payload in &payloads {
                        collect_ty_params(payload, Some(&universe), &mut mentioned);
                    }
                    collect_ty_params(&case_result_ty, Some(&universe), &mut mentioned);
                    for predicate in &predicates {
                        collect_predicate_params(predicate, Some(&universe), &mut mentioned);
                    }
                    let scheme_params = all_params
                        .into_iter()
                        .filter(|param| mentioned.contains(param))
                        .map(|symbol| SchemeParam { symbol })
                        .collect();
                    let constructor_scheme = Scheme {
                        params: scheme_params,
                        eff_params: vec![],
                        row_params: vec![],
                        perm_params: vec![],
                        predicates,
                        ty: Ty::Func(payloads, Box::new(case_result_ty), EffectRow::pure()),
                    };
                    info.variants.insert(
                        name.name_str(),
                        Variant {
                            symbol: variant,
                            payload_labels,
                            constructor_scheme,
                        },
                    );
                }
                DeclKind::Method {
                    func,
                    is_static: false,
                    ..
                } => {
                    if let Ok(method) = func.name.symbol() {
                        info.methods.insert(func.name.name_str(), method);
                    }
                }
                DeclKind::TypeAlias(..) => {}
                other => self.unsupported(member.id, decl_kind_name(other)),
            }
        }
        self.catalog.enums.insert(symbol, info);
    }

    pub(super) fn report_variant_generic_shadowing(
        &mut self,
        enum_generics: &[GenericDecl],
        case_generics: &[GenericDecl],
    ) {
        let enum_param_names: FxHashSet<String> = enum_generics
            .iter()
            .map(|generic| generic.name.name_str())
            .collect();
        for generic in case_generics {
            let name = generic.name.name_str();
            if enum_param_names.contains(&name) {
                self.diagnostics
                    .errors
                    .push((TypeError::GenericShadowing { name }, generic.id));
            }
        }
    }

    pub(super) fn valid_variant_result(
        &mut self,
        enum_symbol: Symbol,
        arity: usize,
        result: &Ty,
    ) -> bool {
        match self.store.shallow(result) {
            Ty::Nominal(symbol, args) => symbol == enum_symbol && args.len() == arity,
            Ty::Error => true,
            _ => false,
        }
    }

    /// Register a protocol: associated types, supers, and requirement
    /// signatures over `Self = Ty::Param(protocol)` and the assoc params
    /// (Wadler & Blott 1989 classes; Chakravarty et al. 2005 assoc types).
    pub(super) fn register_protocol(
        &mut self,
        symbol: Symbol,
        decl: &'a Decl,
        protocol_defaults: &mut Vec<(Symbol, Symbol, &'a Func)>,
    ) {
        let DeclKind::Protocol {
            generics,
            where_clause,
            body,
            conformances,
            ..
        } = &decl.kind
        else {
            return;
        };
        self.self_types.push(Ty::Param(symbol));
        let params = generic_symbols(generics);
        let param_defaults = generics
            .iter()
            .map(|generic| {
                generic
                    .default
                    .as_ref()
                    .map(|default| self.lower_annotation(default))
            })
            .collect();
        let self_ty = Ty::Param(symbol);
        let supers: Vec<ProtocolRef> = conformances
            .iter()
            .filter_map(|c| {
                self.lower_protocol_ref_with_self(c, Some(&self_ty))
                    .map(|(protocol, _)| protocol)
            })
            .collect();

        let mut info = ProtocolInfo {
            params: params.clone(),
            param_defaults,
            supers,
            ..Default::default()
        };
        self.register_where_bounds(where_clause.as_ref());
        self.catalog.param_bounds.entry(symbol).or_insert_with(|| {
            vec![ProtocolRef {
                protocol: symbol,
                args: params.iter().copied().map(Ty::Param).collect(),
            }]
        });
        for member in &body.decls {
            if let DeclKind::Associated {
                generic,
                where_clause,
            } = &member.kind
                && let Ok(assoc) = generic.name.symbol()
            {
                info.assoc.insert(generic.name.name_str(), assoc);
                // `associated T: Iterator` — bounds on the assoc
                // param discharge member access through it.
                self.register_generic_bounds(std::slice::from_ref(generic));
                self.register_where_bounds(where_clause.as_ref());
                let assoc_predicates =
                    self.declared_predicates(std::slice::from_ref(generic), where_clause.as_ref());
                for predicate in assoc_predicates {
                    if !info.predicates.contains(&predicate) {
                        info.predicates.push(predicate);
                    }
                }
            }
        }
        self.catalog.protocols.insert(symbol, info.clone());
        for predicate in self.declared_predicates(&[], where_clause.as_ref()) {
            if !info.predicates.contains(&predicate) {
                info.predicates.push(predicate);
            }
        }
        for predicate in &info.predicates {
            if let Predicate::Conforms { ty, protocol } = predicate
                && *ty == Ty::Param(symbol)
                && !info.supers.contains(protocol)
            {
                info.supers.push(protocol.clone());
            }
        }
        for member in &body.decls {
            match &member.kind {
                DeclKind::Associated { .. } => {}
                DeclKind::MethodRequirement { signature, .. }
                | DeclKind::FuncSignature(signature) => {
                    if let Some(requirement) = self.lower_requirement(signature, false) {
                        info.requirements
                            .insert(signature.name.name_str(), requirement);
                    }
                }
                // Default-bodied requirements: register the signature now;
                // the body checks generically over Self after all groups.
                DeclKind::Method { func, .. } => {
                    if let Some(requirement) = self.lower_default_requirement(func) {
                        protocol_defaults.push((symbol, requirement.symbol, func));
                        info.requirements.insert(func.name.name_str(), requirement);
                    }
                }
                DeclKind::TypeAlias(..) => {}
                other => self.unsupported(member.id, decl_kind_name(other)),
            }
        }
        self.self_types.pop();

        for label in info.requirements.keys() {
            self.catalog.add_owner(label, MemberOwner::Protocol(symbol));
        }
        // Showable and same-type Equatable are auto-derived for structs and
        // enums. The lowerer synthesizes their required witnesses.
        if let DeclKind::Protocol { name, .. } = &decl.kind
            && matches!(name.name_str().as_str(), "Showable" | "Equatable")
            && !self.catalog.derivable.contains(&symbol)
        {
            self.catalog.derivable.push(symbol);
        }
        self.catalog.protocols.insert(symbol, info);
    }

    pub(super) fn lower_requirement(
        &mut self,
        signature: &FuncSignature,
        has_default: bool,
    ) -> Option<Requirement> {
        self.register_generic_bounds(&signature.generics);
        self.register_where_bounds(signature.where_clause.as_ref());
        let predicates =
            self.declared_predicates(&signature.generics, signature.where_clause.as_ref());
        let symbol = signature.name.symbol().ok()?;
        let params: Vec<Ty> = signature
            .params
            .iter()
            .map(|p| match &p.type_annotation {
                Some(annotation) => {
                    let ty = self.lower_annotation(annotation);
                    elaborate::apply_param_mode(self.catalog, p.mode, ty)
                }
                None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, p.id)),
            })
            .collect();
        let ret = match &signature.ret {
            Some(annotation) => self.lower_annotation(annotation),
            None => {
                self.unsupported(
                    signature.id,
                    "protocol requirements without a return type annotation",
                );
                Ty::Error
            }
        };
        // The effect tail is a parameter keyed by the requirement symbol so
        // every use substitutes a fresh one (no accidental row sharing).
        let eff = EffectRow {
            effects: Default::default(),
            tail: Some(EffTail::Param(symbol)),
        };
        self.insert_requirement_scheme(
            symbol,
            Ty::Func(params, Box::new(ret), eff),
            generic_symbols(&signature.generics),
            predicates,
        );
        Some(Requirement {
            symbol,
            has_default,
        })
    }

    /// A requirement's TYPE is an ordinary scheme entry — the one
    /// signature carrier the whole compiler shares. params = the method's
    /// own generics; eff_params = the symbol-keyed outer tail plus each
    /// inner closure row; every consumer freshens through the scheme.
    fn insert_requirement_scheme(
        &mut self,
        symbol: Symbol,
        sig: Ty,
        generics: Vec<Symbol>,
        predicates: Vec<Predicate>,
    ) {
        let (sig, inner_eff_params) = self.quantify_signature_eff_vars(sig);
        let mut eff_params = vec![symbol];
        eff_params.extend(inner_eff_params);
        self.schemes.insert(
            symbol,
            Scheme {
                params: generics
                    .into_iter()
                    .map(|symbol| SchemeParam { symbol })
                    .collect(),
                eff_params,
                row_params: vec![],
                perm_params: vec![],
                predicates,
                ty: sig,
            },
        );
    }

    pub(super) fn lower_default_requirement(&mut self, func: &Func) -> Option<Requirement> {
        self.register_func_bounds(func);
        let predicates = self.declared_predicates(&func.generics, func.where_clause.as_ref());
        let symbol = func.name.symbol().ok()?;
        let params: Vec<Ty> = func
            .params
            .iter()
            .map(|p| match &p.type_annotation {
                Some(annotation) => {
                    let ty = self.lower_annotation(annotation);
                    elaborate::apply_param_mode(self.catalog, p.mode, ty)
                }
                None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, p.id)),
            })
            .collect();
        let ret = match &func.ret {
            Some(annotation) => self.lower_annotation(annotation),
            None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, func.id)),
        };
        let eff = EffectRow {
            effects: Default::default(),
            tail: Some(EffTail::Param(symbol)),
        };
        self.insert_requirement_scheme(
            symbol,
            Ty::Func(params, Box::new(ret), eff),
            generic_symbols(&func.generics),
            predicates,
        );
        Some(Requirement {
            symbol,
            has_default: true,
        })
    }

    /// Replace leftover inner effect-row variables in a catalog-bound
    /// signature (a closure-typed parameter's latent row) with fresh rigid
    /// params, returned for the requirement's `eff_params`. Catalog types
    /// outlive this module's solver store, so a raw variable would be read
    /// as a foreign id by importers; consumers freshen the params per use.
    fn quantify_signature_eff_vars(&mut self, sig: Ty) -> (Ty, Vec<Symbol>) {
        struct EffVarParams<'x> {
            symbols: &'x mut Symbols,
            module_id: ModuleId,
            minted: Vec<Symbol>,
        }
        impl crate::types::ty::TyFold for EffVarParams<'_> {
            fn fold_eff(&mut self, eff: &EffectRow) -> EffectRow {
                let entries = eff
                    .effects
                    .iter()
                    .map(|entry| EffectEntry {
                        effect: entry.effect,
                        args: entry.args.iter().map(|ty| self.fold_ty(ty)).collect(),
                    })
                    .collect();
                let tail = match &eff.tail {
                    Some(EffTail::Var(_)) => {
                        let param =
                            Symbol::TypeParameter(self.symbols.next_type_parameter(self.module_id));
                        self.minted.push(param);
                        Some(EffTail::Param(param))
                    }
                    other => other.clone(),
                };
                EffectRow::new(entries, tail)
            }
        }
        let mut folder = EffVarParams {
            symbols: self.symbols,
            module_id: self.module_id,
            minted: vec![],
        };
        use crate::types::ty::TyFold;
        let sig = folder.fold_ty(&sig);
        (sig, folder.minted)
    }

    /// A top-level `extend` whose head names a protocol (rather than a
    /// nominal type getting witnesses or inherent members).
    pub(super) fn protocol_extension_head(&self, decl: &Decl) -> Option<Symbol> {
        let DeclKind::Extend { name, .. } = &decl.kind else {
            return None;
        };
        let head = name.symbol().ok()?;
        self.catalog.protocols.contains_key(&head).then_some(head)
    }

    /// Register `extend SomeProtocol { ... }`: each method joins the
    /// protocol as a defaulted requirement — checked generically over
    /// Self like an in-body default, witnessable by conforming extends.
    pub(super) fn register_protocol_extension(
        &mut self,
        protocol: Symbol,
        decl: &'a Decl,
        protocol_defaults: &mut Vec<(Symbol, Symbol, &'a Func)>,
    ) {
        let DeclKind::Extend {
            conformances,
            generics,
            where_clause,
            body,
            ..
        } = &decl.kind
        else {
            return;
        };
        if !conformances.is_empty() {
            self.unsupported(decl.id, "declaring conformances on a protocol extension");
            return;
        }
        if !generics.is_empty() {
            self.unsupported(decl.id, "generic protocol extensions");
            return;
        }
        self.self_types.push(Ty::Param(protocol));
        self.register_where_bounds(where_clause.as_ref());
        let extension_predicates = self.declared_predicates(&[], where_clause.as_ref());
        for member in &body.decls {
            let DeclKind::Method { func, .. } = &member.kind else {
                self.unsupported(member.id, decl_kind_name(&member.kind));
                continue;
            };
            let label = func.name.name_str();
            if self
                .catalog
                .protocols
                .get(&protocol)
                .is_some_and(|info| info.requirements.contains_key(&label))
            {
                self.unsupported(
                    member.id,
                    "redeclaring an existing protocol member in a protocol extension",
                );
                continue;
            }
            let Some(requirement) = self.lower_default_requirement(func) else {
                continue;
            };
            // The extension-level where clause joins the requirement's
            // scheme context (the scheme is the signature carrier).
            if let Some(scheme) = self.schemes.get_mut(&requirement.symbol) {
                for predicate in &extension_predicates {
                    if !scheme.predicates.contains(predicate) {
                        scheme.predicates.push(predicate.clone());
                    }
                }
            }
            protocol_defaults.push((protocol, requirement.symbol, func));
            if let Some(info) = self.catalog.protocols.get_mut(&protocol) {
                info.requirements.insert(label.clone(), requirement);
            }
            self.catalog
                .add_owner(&label, MemberOwner::Protocol(protocol));
        }
        self.self_types.pop();
    }

    pub(super) fn register_effect(
        &mut self,
        symbol: Symbol,
        generics: &[crate::node_kinds::generic_decl::GenericDecl],
        where_clause: Option<&WhereClause>,
        params: &[Parameter],
        ret: &TypeAnnotation,
    ) {
        self.register_generic_bounds(generics);
        self.register_where_bounds(where_clause);
        let predicates = self.declared_predicates(generics, where_clause);
        let generics: Vec<Symbol> = generics
            .iter()
            .filter_map(|generic| generic.name.symbol().ok())
            .collect();
        let params = params
            .iter()
            .map(|p| match &p.type_annotation {
                Some(annotation) => {
                    let ty = self.lower_annotation(annotation);
                    elaborate::apply_param_mode(self.catalog, p.mode, ty)
                }
                // Unannotated effect params share an outer variable that
                // perform sites and handlers refine during checking.
                None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, p.id)),
            })
            .collect();
        let ret = self.lower_annotation(ret);
        self.catalog.effects.insert(
            symbol,
            crate::types::catalog::EffectSig {
                generics,
                predicates,
                params,
                ret,
            },
        );
    }

    /// Register an `extend`: conformance rows (witness map + associated-type
    /// bindings inferred by matching witness annotations against requirement
    /// signatures — Chakravarty et al. 2005's instance-determined synonyms),
    /// conditional-conformance contexts (instances with contexts, Hall et
    /// al. TOPLAS 1996), inherent members, and completeness errors. Bodies
    /// check later (`check_extend`). `enclosing` is the struct whose body a
    /// nested `extend Self: P` appears in.
    pub(super) fn register_extend(
        &mut self,
        decl: &'a Decl,
        enclosing: Option<Symbol>,
    ) -> Option<ExtendWork<'a>> {
        let DeclKind::Extend {
            name,
            row_generics,
            conformances,
            generics,
            where_clause,
            body,
            ..
        } = &decl.kind
        else {
            return None;
        };
        let head = match (name, enclosing) {
            (Name::SelfType(_), Some(parent)) | (_, Some(parent)) => parent,
            _ => name.symbol().ok()?,
        };
        let protocol_head = enclosing.is_none() && self.catalog.protocols.contains_key(&head);
        if protocol_head && (!row_generics.is_empty() || !generics.is_empty()) {
            self.unsupported(decl.id, "generic protocol extensions");
            return None;
        }
        self.register_generic_bounds(row_generics);
        self.register_generic_bounds(generics);
        self.register_where_bounds(where_clause.as_ref());

        // The row's own rigid params and the head application they index:
        // a nested extend uses the enclosing struct's generics; a top-level
        // `extend Array<Element>` uses its declared generics; plain heads
        // (`extend Int`) have none. A protocol head is already a quantified
        // Self, so the conformance row's self pattern is empty and the
        // protocol's Self/params/associated types become row parameters.
        let self_params: Vec<Symbol> = if protocol_head {
            vec![]
        } else if enclosing.is_some() || generics.is_empty() {
            self.catalog
                .structs
                .get(&head)
                .map(|i| i.params.clone())
                .or_else(|| self.catalog.enums.get(&head).map(|i| i.params.clone()))
                .unwrap_or_default()
        } else {
            generic_symbols(generics)
        };
        let mut params = generic_symbols(row_generics);
        params.extend(self_params.iter().copied());
        if protocol_head {
            params.push(head);
            if let Some(info) = self.catalog.protocols.get(&head) {
                params.extend(info.params.iter().copied());
                params.extend(info.assoc.values().copied());
            }
        }
        let self_args: Vec<Ty> = self_params.iter().map(|p| Ty::Param(*p)).collect();
        let self_ty = if protocol_head {
            Ty::Param(head)
        } else {
            Ty::Nominal(head, self_args.clone())
        };
        self.self_types.push(self_ty.clone());
        let context_generics: Vec<GenericDecl> = row_generics
            .iter()
            .cloned()
            .chain(generics.iter().cloned())
            .collect();
        let mut context = self.declared_predicates(&context_generics, where_clause.as_ref());
        if protocol_head {
            let head_protocol = ProtocolRef {
                protocol: head,
                args: self
                    .catalog
                    .protocols
                    .get(&head)
                    .map(|info| info.params.iter().copied().map(Ty::Param).collect())
                    .unwrap_or_default(),
            };
            context.insert(
                0,
                Predicate::Conforms {
                    ty: self_ty.clone(),
                    protocol: head_protocol.clone(),
                },
            );
            for (_, owner, assoc) in self
                .catalog
                .declared_associated_types_in_ref(&head_protocol)
            {
                context.push(Predicate::TypeEq(
                    Ty::Param(assoc),
                    Ty::Proj(Box::new(self_ty.clone()), owner, assoc),
                ));
            }
        }
        self.self_types.pop();

        // Collect declared members (witnesses and inherent methods).
        let mut members: IndexMap<String, (Symbol, &'a Func)> = IndexMap::default();
        for member in &body.decls {
            if let DeclKind::Method { func, .. } = &member.kind
                && let Ok(method) = func.name.symbol()
            {
                members.insert(func.name.name_str(), (method, func));
            }
        }
        let mut witnessed: FxHashSet<String> = FxHashSet::default();
        let mut declared_assoc: FxHashMap<String, Ty> = FxHashMap::default();
        self.self_types.push(self_ty.clone());
        for member in &body.decls {
            if let DeclKind::TypeAlias(name, _, rhs) = &member.kind {
                declared_assoc.insert(name.name_str(), self.lower_annotation(rhs));
            }
        }
        self.self_types.pop();

        let mut protocols = vec![];
        let mut rows: IndexMap<ProtocolRef, Conformance> = IndexMap::default();
        let mut missing_requirements: FxHashSet<Symbol> = FxHashSet::default();
        for conformance_annotation in conformances {
            let Some((protocol, assoc_args)) =
                self.lower_protocol_ref_with_self(conformance_annotation, Some(&self_ty))
            else {
                continue;
            };
            if !self.catalog.protocols.contains_key(&protocol.protocol) {
                self.unsupported(decl.id, "conforming to an unknown protocol");
                continue;
            }
            protocols.push(protocol.clone());

            // A conformance to `B` is also a conformance to every super `A`.
            // Build a real row for each protocol in the closure so later
            // `T: A` constraints reduce through the same conformance table as
            // direct conformances.
            for conformed in self.catalog.protocol_and_supers(&protocol) {
                let Some(info) = self.catalog.protocols.get(&conformed.protocol).cloned() else {
                    continue;
                };
                let requirements = self.catalog.requirements_for_conformance(&conformed);
                let conformance = rows
                    .entry(conformed.clone())
                    .or_insert_with(|| Conformance {
                        params: params.clone(),
                        self_args: self_args.clone(),
                        protocol_args: conformed.args.clone(),
                        context: context.clone(),
                        ..Default::default()
                    });

                // Positional associated-type application: `Iterator<Element>`
                // binds the named protocol's own assoc params in declaration
                // order. Inherited assoc params bind through same-named
                // `typealias` declarations or witness inference below.
                if conformed == protocol {
                    for (assoc_symbol, arg) in info.assoc.values().zip(&assoc_args) {
                        let binding = self.lower_annotation(arg);
                        conformance.assoc.insert(*assoc_symbol, binding);
                    }
                }
                for (name, assoc_symbol) in &info.assoc {
                    if let Some(binding) = declared_assoc.get(name) {
                        conformance.assoc.insert(*assoc_symbol, binding.clone());
                    }
                }

                self.self_types.push(self_ty.clone());
                for (owner, label, requirement) in requirements {
                    match members.get(&label) {
                        Some((witness, func)) => {
                            conformance.witnesses.insert(label.clone(), *witness);
                            witnessed.insert(label.clone());
                            self.infer_assoc_bindings(&requirement, func, conformance);
                        }
                        None => {
                            let already_conforms_to_owner = self
                                .catalog
                                .conformances
                                .contains_key(&(head, owner.clone()));
                            let separately_claims_owner = owner != protocol
                                && self.explicit_conformances.contains(&(head, owner.clone()));
                            let intrinsic_marker_clone = label == "clone"
                                && matches!(owner.protocol, Symbol::Copy | Symbol::CheapClone);
                            if !requirement.has_default
                                && !intrinsic_marker_clone
                                && !already_conforms_to_owner
                                && !separately_claims_owner
                                && missing_requirements.insert(requirement.symbol)
                            {
                                self.diagnostics.errors.push((
                                    TypeError::MissingWitness {
                                        protocol: owner.to_string(),
                                        requirement: label.clone(),
                                    },
                                    decl.id,
                                ));
                            }
                        }
                    }
                }
                self.self_types.pop();
            }
        }

        for (protocol, conformance) in rows {
            let overlaps_existing = self
                .catalog
                .conformances
                .iter()
                .find(|((existing_head, existing_protocol), existing)| {
                    *existing_head == head
                        && existing_protocol != &protocol
                        && existing_protocol.protocol == protocol.protocol
                        && self.catalog.conformance_rows_overlap(
                            existing_protocol,
                            existing,
                            &protocol,
                            &conformance,
                        )
                })
                .map(|((_, existing_protocol), _)| existing_protocol.clone());
            if let Some(existing) = overlaps_existing {
                self.diagnostics.errors.push((
                    TypeError::OverlappingConformance {
                        ty: self_ty.render_mono(),
                        protocol: protocol.to_string(),
                        existing: existing.to_string(),
                    },
                    decl.id,
                ));
                continue;
            }
            match self.catalog.conformances.entry((head, protocol.clone())) {
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    let existing = entry.get_mut();
                    for (label, witness) in conformance.witnesses {
                        existing.witnesses.entry(label).or_insert(witness);
                    }
                    for (assoc, ty) in conformance.assoc {
                        existing.assoc.entry(assoc).or_insert(ty);
                    }
                    for context in conformance.context {
                        if !existing.context.contains(&context) {
                            existing.context.push(context);
                        }
                    }
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(conformance);
                }
            }
            let by_head = self.catalog.conformances_by_head.entry(head).or_default();
            if !by_head.contains(&protocol) {
                by_head.push(protocol.clone());
            }
        }

        if protocol_head {
            for label in members.keys() {
                if !witnessed.contains(label) {
                    self.unsupported(
                        decl.id,
                        "methods in a protocol-extension conformance must witness a target protocol requirement",
                    );
                }
            }
            return Some(ExtendWork {
                self_ty,
                context,
                decl,
                protocols,
            });
        }

        // Members that witness no requirement are inherent: register their
        // annotation-derived signatures so any group can dispatch on them.
        self.self_types.push(self_ty.clone());
        for (label, (method, func)) in &members {
            if witnessed.contains(label) {
                continue;
            }
            let sig_params: Vec<Ty> = func
                .params
                .iter()
                .map(|p| match &p.type_annotation {
                    Some(annotation) => {
                        let ty = self.lower_annotation(annotation);
                        elaborate::apply_param_mode(self.catalog, p.mode, ty)
                    }
                    None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, p.id)),
                })
                .collect();
            let ret = match &func.ret {
                Some(annotation) => self.lower_annotation(annotation),
                None => Ty::Var(self.store.fresh_ty(OUTER_LEVEL, func.id)),
            };
            let eff = EffectRow {
                effects: Default::default(),
                tail: Some(EffTail::Param(*method)),
            };
            // The annotation-derived signature is an ordinary scheme (the
            // one signature carrier); `check_extend` replaces it with the
            // inferred, zonked scheme after the body checks. The catalog
            // keeps only the instance-head pattern.
            let predicates = self.declared_predicates(&func.generics, func.where_clause.as_ref());
            self.insert_requirement_scheme(
                *method,
                Ty::Func(sig_params, Box::new(ret), eff),
                generic_symbols(&func.generics),
                predicates,
            );
            let member = crate::types::catalog::InherentMember {
                symbol: *method,
                params: params.clone(),
                self_args: self_args.clone(),
            };
            self.catalog
                .extend_members
                .entry(head)
                .or_default()
                .insert(label.clone(), member);
            self.catalog.add_owner(label, MemberOwner::Nominal(head));
        }
        self.self_types.pop();

        Some(ExtendWork {
            self_ty,
            context,
            decl,
            protocols,
        })
    }

    /// One-way match of a requirement signature against a witness's declared
    /// annotations: wherever the requirement says `Param(assoc)` and the
    /// witness annotation gives a concrete type, that's the conformance's
    /// binding for the associated type.
    pub(super) fn infer_assoc_bindings(
        &mut self,
        requirement: &Requirement,
        func: &Func,
        conformance: &mut Conformance,
    ) {
        let Some(Ty::Func(req_params, req_ret, _)) =
            self.schemes.get(&requirement.symbol).map(|s| s.ty.clone())
        else {
            return;
        };
        let req_params = &req_params;
        let req_ret: &Ty = &req_ret;
        let witness_params: Vec<Option<Ty>> = func
            .params
            .iter()
            .map(|p| {
                p.type_annotation.as_ref().map(|annotation| {
                    let ty = self.lower_annotation(annotation);
                    elaborate::apply_param_mode(self.catalog, p.mode, ty)
                })
            })
            .collect();
        let witness_ret = func
            .ret
            .as_ref()
            .map(|annotation| self.lower_annotation(annotation));

        for (pattern, witness) in req_params.iter().zip(&witness_params) {
            if let Some(witness) = witness {
                collect_assoc_bindings(pattern, witness, &mut conformance.assoc);
            }
        }
        if let Some(witness) = &witness_ret {
            collect_assoc_bindings(req_ret, witness, &mut conformance.assoc);
        }
    }
}
