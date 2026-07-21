use super::*;
use crate::types::ty::StaticCmpOp;

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
            obligations: std::mem::take(&mut self.obligations),
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
                .map(|owner| param_symbols(&nominal_params(self.catalog, owner)))
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
        // This pass pre-scans conformance heads; `register_extend`
        // re-lowers each with its row context and owns the formation
        // obligations, so this pass's duplicates are discarded below.
        let obligation_start = self.obligations.len();
        for decl in top_decls {
            if let DeclKind::Extend {
                binders,
                head: head_annotation,
                conformances,
                ..
            } = &decl.kind
                && let Ok(head) = head_annotation.symbol()
            {
                // Instance binders (including ADR 0035 static params) are
                // registered before the ordinary head annotation lowers.
                self.register_generic_bounds(binders);
                let Some((_, self_ty, _)) = self.lower_extension_head(head_annotation) else {
                    continue;
                };
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
                .map(|info| param_symbols(&info.params))
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
        self.obligations.truncate(obligation_start);
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
            // The claim's own conformance row is the authority for its
            // arguments: its where-clause context legalizes `T`-typed
            // fields, and its self-args rebind the declaration's params
            // (fields are stored under the DECLARATION's param symbols,
            // the row's context speaks about the EXTEND's).
            let row = self
                .catalog
                .conformances_for_head(head)
                .find_map(|(_, row)| (row.protocol == ProtocolRef::bare(protocol)).then_some(row));
            let context = row.map(|row| row.context.clone()).unwrap_or_default();
            let self_args = row.map(|row| row.self_args.clone()).unwrap_or_default();
            let decl_params = self
                .catalog
                .structs
                .get(&head)
                .map(|info| info.params.clone())
                .or_else(|| {
                    self.catalog
                        .enums
                        .get(&head)
                        .map(|info| info.params.clone())
                })
                .unwrap_or_default();
            let rebind: FxHashMap<Symbol, Ty> = decl_params
                .iter()
                .map(|param| param.symbol)
                .zip(self_args.iter().cloned())
                .collect();
            for (field, ty) in self.marker_checked_fields(head) {
                let ty = ty.substitute(&rebind, &FxHashMap::default(), &FxHashMap::default());
                if !self.catalog.ty_satisfies_marker(&ty, protocol, &context) {
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
        let self_ty = Ty::Nominal(
            symbol,
            generic_symbols(generics)
                .into_iter()
                .map(Ty::Param)
                .collect(),
        );
        let info = self.in_declaration_context(
            Some(self_ty),
            generics,
            where_clause.as_ref(),
            |this, context| {
                let mut info = StructInfo {
                    linear: *linear,
                    heap: *heap,
                    params: context.params.clone(),
                    predicates: context.predicates.clone(),
                    ..Default::default()
                };
                this.collect_struct_members(&mut info, symbol, body);
                info
            },
        );
        self.catalog.structs.insert(symbol, info);
    }

    fn collect_struct_members(&mut self, info: &mut StructInfo, symbol: Symbol, body: &Body) {
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
                DeclKind::Init { name, params, .. } => {
                    if let Ok(init) = name.symbol() {
                        info.inits.push((init, params.len()));
                    }
                }
                // Nested `extend Self: P` registers in pass B. Type aliases
                // are transparent type declarations, not value members.
                DeclKind::Extend { .. } | DeclKind::TypeAlias(..) => {}
                other => self.unsupported(member.id, decl_kind_name(other)),
            }
        }
        self.mint_field_eff_params(info);
        for label in info.fields.keys().chain(info.methods.keys()) {
            self.catalog.add_owner(label, MemberOwner::Nominal(symbol));
        }
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
        let result = Ty::Nominal(
            symbol,
            generic_symbols(generics)
                .into_iter()
                .map(Ty::Param)
                .collect(),
        );
        let info = self.in_declaration_context(
            Some(result.clone()),
            generics,
            where_clause.as_ref(),
            |this, context| {
                let mut info = Enum {
                    linear: *linear,
                    params: context.params.clone(),
                    predicates: context.predicates.clone(),
                    ..Default::default()
                };
                for member in &body.decls {
                    match &member.kind {
                        DeclKind::EnumVariant { .. } => {
                            this.register_enum_variant(&mut info, symbol, generics, member, &result)
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
                        other => this.unsupported(member.id, decl_kind_name(other)),
                    }
                }
                info
            },
        );
        self.catalog.enums.insert(symbol, info);
    }

    fn register_enum_variant(
        &mut self,
        info: &mut Enum,
        symbol: Symbol,
        enum_generics: &[GenericDecl],
        member: &Decl,
        result: &Ty,
    ) {
        let DeclKind::EnumVariant {
            name,
            generics: case_generics,
            payloads: payload_annotations,
            payload_labels: declared_payload_labels,
            result: case_result,
            ..
        } = &member.kind
        else {
            return;
        };
        let Ok(variant) = name.symbol() else { return };
        self.report_variant_generic_shadowing(enum_generics, case_generics);
        // A case's own generics form a nested declaration context: its
        // payload annotations prove their formation obligations under
        // the case's predicates before the enum's.
        let (payloads, payload_labels, case_result_ty, predicates) =
            self.in_declaration_context(None, case_generics, None, |this, case_context| {
                let payloads: Vec<Ty> = payload_annotations
                    .iter()
                    .map(|a| this.lower_annotation(a))
                    .collect();
                let payload_labels: Vec<Option<String>> = declared_payload_labels
                    .iter()
                    .map(|label| label.as_ref().map(Name::name_str))
                    .collect();
                let mut seen_labels = FxHashSet::default();
                for label in payload_labels.iter().flatten() {
                    if !seen_labels.insert(label.clone()) {
                        this.diagnostics.errors.push((
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
                    .map(|annotation| this.lower_annotation(annotation))
                    .unwrap_or_else(|| result.clone());
                (
                    payloads,
                    payload_labels,
                    case_result_ty,
                    case_context.predicates.clone(),
                )
            });
        if !self.valid_variant_result(symbol, info.params.len(), &case_result_ty) {
            self.diagnostics.errors.push((
                TypeError::InvalidVariantResultType {
                    variant: name.name_str(),
                },
                case_result
                    .as_ref()
                    .map_or(member.id, |annotation| annotation.id),
            ));
        } else if case_result.is_some() && case_result_ty == *result {
            self.diagnostics.warnings.push((
                TypeError::RedundantVariantResultType {
                    variant: name.name_str(),
                },
                case_result
                    .as_ref()
                    .map_or(member.id, |annotation| annotation.id),
            ));
        }

        let all_params: Vec<Symbol> = info
            .params
            .iter()
            .map(|param| param.symbol)
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
            .map(|symbol| scheme_param(self.catalog, symbol))
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
        // The protocol's where clause lowers mid-body (associated types
        // must register first so the clause can mention them), so the
        // context opens without it; the body extends the predicates and
        // the exit wrap honors the final set.
        let info = self.in_declaration_context(None, generics, None, |this, context| {
            let self_ty = Ty::Param(symbol);
            let supers: Vec<ProtocolRef> = conformances
                .iter()
                .filter_map(|c| {
                    this.lower_protocol_ref_with_self(c, Some(&self_ty))
                        .map(|(protocol, _)| protocol)
                })
                .collect();

            let mut info = ProtocolInfo {
                params: context.params.clone(),
                supers,
                ..Default::default()
            };
            this.register_where_bounds(where_clause.as_ref());
            this.catalog.param_bounds.entry(symbol).or_insert_with(|| {
                vec![ProtocolRef {
                    protocol: symbol,
                    args: context.params.iter().map(|p| Ty::Param(p.symbol)).collect(),
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
                    this.register_generic_bounds(std::slice::from_ref(generic));
                    this.register_where_bounds(where_clause.as_ref());
                    let assoc_predicates = this
                        .declared_predicates(std::slice::from_ref(generic), where_clause.as_ref());
                    for predicate in assoc_predicates {
                        if !info.predicates.contains(&predicate) {
                            info.predicates.push(predicate);
                        }
                    }
                }
            }
            this.catalog.protocols.insert(symbol, info.clone());
            // The protocol's own params and associated types are the
            // where clause's context (a static `where 0 < N` mentions
            // them alongside Self).
            let context_params: FxHashSet<Symbol> = generics
                .iter()
                .filter_map(|generic| generic.name.symbol().ok())
                .chain(self_context_param(&self_ty))
                .chain(info.assoc.values().copied())
                .collect();
            if let Some(where_clause) = where_clause {
                for predicate in this.lower_where_clause_predicates(
                    where_clause,
                    &context_params,
                    Some(&self_ty),
                ) {
                    if !info.predicates.contains(&predicate) {
                        info.predicates.push(predicate);
                    }
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
                    | DeclKind::FuncSignature(signature)
                    | DeclKind::InitRequirement { signature } => {
                        if let Some(requirement) = this.lower_requirement(signature, false) {
                            info.requirements
                                .insert(signature.name.name_str(), requirement);
                        }
                    }
                    // Default-bodied requirements: register the signature now;
                    // the body checks generically over Self after all groups.
                    DeclKind::Method { func, .. } => {
                        if let Some(requirement) = this.lower_default_requirement(func) {
                            protocol_defaults.push((symbol, requirement.symbol, func));
                            info.requirements.insert(func.name.name_str(), requirement);
                        }
                    }
                    DeclKind::TypeAlias(..) => {}
                    other => this.unsupported(member.id, decl_kind_name(other)),
                }
            }

            for label in info.requirements.keys() {
                this.catalog.add_owner(label, MemberOwner::Protocol(symbol));
            }
            // Showable and same-type Equatable are auto-derived for structs and
            // enums. The lowerer synthesizes their required witnesses.
            if let DeclKind::Protocol { name, .. } = &decl.kind
                && matches!(name.name_str().as_str(), "Showable" | "Equatable")
                && !this.catalog.derivable.contains(&symbol)
            {
                this.catalog.derivable.push(symbol);
            }
            for predicate in &info.predicates {
                if !context.predicates.contains(predicate) {
                    context.predicates.push(predicate.clone());
                }
            }
            info
        });
        self.self_types.pop();
        self.catalog.protocols.insert(symbol, info);
    }

    pub(super) fn lower_requirement(
        &mut self,
        signature: &FuncSignature,
        has_default: bool,
    ) -> Option<Requirement> {
        let symbol = signature.name.symbol().ok()?;
        // The requirement's generics and where clause are their own
        // declaration context: its signature's formation obligations
        // prove under the requirement's predicates, not the protocol's.
        let (params, ret, predicates) = self.in_declaration_context(
            None,
            &signature.generics,
            signature.where_clause.as_ref(),
            |this, context| {
                let params: Vec<Ty> = signature
                    .params
                    .iter()
                    .map(|p| match &p.type_annotation {
                        Some(annotation) => {
                            let ty = this.lower_annotation(annotation);
                            elaborate::apply_param_mode(this.catalog, p, ty, this.diagnostics)
                        }
                        None => Ty::Var(this.store.fresh_ty(OUTER_LEVEL, p.id)),
                    })
                    .collect();
                let ret = match &signature.ret {
                    Some(annotation) => this.lower_annotation(annotation),
                    None => {
                        this.unsupported(
                            signature.id,
                            "protocol requirements without a return type annotation",
                        );
                        Ty::Error
                    }
                };
                (params, ret, context.predicates.clone())
            },
        );
        // An omitted annotation is effect-polymorphic and gets a fresh tail
        // at every use. An explicit annotation is the requirement's closed
        // effect contract and must survive into witness dispatch.
        let eff = if signature.effects.is_open {
            EffectRow {
                effects: Default::default(),
                tail: Some(EffTail::Param(symbol)),
            }
        } else {
            EffectRow::new(
                signature
                    .effects
                    .names
                    .iter()
                    .filter_map(|name| name.symbol().ok())
                    .map(EffectEntry::label)
                    .collect(),
                None,
            )
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
        let has_open_outer = matches!(
            &sig,
            Ty::Func(_, _, EffectRow {
                tail: Some(EffTail::Param(param)),
                ..
            }) if *param == symbol
        );
        let (sig, inner_eff_params) = self.quantify_signature_eff_vars(sig);
        let mut eff_params = if has_open_outer { vec![symbol] } else { vec![] };
        eff_params.extend(inner_eff_params);
        self.schemes.insert(
            symbol,
            Scheme {
                params: generics
                    .into_iter()
                    .map(|symbol| scheme_param(self.catalog, symbol))
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
        let symbol = func.name.symbol().ok()?;
        let (params, ret, predicates) = self.in_declaration_context(
            None,
            &func.generics,
            func.where_clause.as_ref(),
            |this, context| {
                let params: Vec<Ty> = func
                    .params
                    .iter()
                    .map(|p| match &p.type_annotation {
                        Some(annotation) => {
                            let ty = this.lower_annotation(annotation);
                            elaborate::apply_param_mode(this.catalog, p, ty, this.diagnostics)
                        }
                        None => Ty::Var(this.store.fresh_ty(OUTER_LEVEL, p.id)),
                    })
                    .collect();
                let ret = match &func.ret {
                    Some(annotation) => this.lower_annotation(annotation),
                    None => Ty::Var(this.store.fresh_ty(OUTER_LEVEL, func.id)),
                };
                (params, ret, context.predicates.clone())
            },
        );
        let eff = if func.effects.is_open {
            EffectRow {
                effects: Default::default(),
                tail: Some(EffTail::Param(symbol)),
            }
        } else {
            EffectRow::new(
                func.effects
                    .names
                    .iter()
                    .filter_map(|name| name.symbol().ok())
                    .map(EffectEntry::label)
                    .collect(),
                None,
            )
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
        let DeclKind::Extend { head, .. } = &decl.kind else {
            return None;
        };
        let head = head.symbol().ok()?;
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
            binders,
            conformances,
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
        if !binders.is_empty() {
            self.unsupported(decl.id, "generic protocol extensions");
            return;
        }
        self.self_types.push(Ty::Param(protocol));
        self.in_declaration_context(None, &[], where_clause.as_ref(), |this, context| {
            for member in &body.decls {
                let DeclKind::Method { func, .. } = &member.kind else {
                    this.unsupported(member.id, decl_kind_name(&member.kind));
                    continue;
                };
                let label = func.name.name_str();
                if this
                    .catalog
                    .protocols
                    .get(&protocol)
                    .is_some_and(|info| info.requirements.contains_key(&label))
                {
                    this.unsupported(
                        member.id,
                        "redeclaring an existing protocol member in a protocol extension",
                    );
                    continue;
                }
                let Some(requirement) = this.lower_default_requirement(func) else {
                    continue;
                };
                // The extension-level where clause joins the requirement's
                // scheme context (the scheme is the signature carrier).
                if let Some(scheme) = this.schemes.get_mut(&requirement.symbol) {
                    for predicate in &context.predicates {
                        if !scheme.predicates.contains(predicate) {
                            scheme.predicates.push(predicate.clone());
                        }
                    }
                }
                protocol_defaults.push((protocol, requirement.symbol, func));
                if let Some(info) = this.catalog.protocols.get_mut(&protocol) {
                    info.requirements.insert(label.clone(), requirement);
                }
                this.catalog
                    .add_owner(&label, MemberOwner::Protocol(protocol));
            }
        });
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
        let sig = self.in_declaration_context(None, generics, where_clause, |this, context| {
            let params = params
                .iter()
                .map(|p| match &p.type_annotation {
                    Some(annotation) => {
                        let ty = this.lower_annotation(annotation);
                        elaborate::apply_param_mode(this.catalog, p, ty, this.diagnostics)
                    }
                    // Unannotated effect params share an outer variable that
                    // perform sites and handlers refine during checking.
                    None => Ty::Var(this.store.fresh_ty(OUTER_LEVEL, p.id)),
                })
                .collect();
            let ret = this.lower_annotation(ret);
            crate::types::catalog::EffectSig {
                generics: context.params.clone(),
                predicates: context.predicates.clone(),
                params,
                ret,
            }
        });
        self.catalog.effects.insert(symbol, sig);
    }

    /// Lower an extension target as an instance pattern. Explicit arguments
    /// use ordinary annotation elaboration; a completely bare generic nominal
    /// denotes its full rigid parameter pattern. Effect-row arguments are not
    /// source-level instance identity.
    fn lower_extension_head(
        &mut self,
        annotation: &TypeAnnotation,
    ) -> Option<(Symbol, Ty, Vec<Ty>)> {
        let head = annotation.symbol().ok()?;
        if self.catalog.protocols.contains_key(&head) {
            return Some((head, Ty::Param(head), vec![]));
        }
        let omitted = matches!(
            &annotation.kind,
            TypeAnnotationKind::Nominal { generics, .. } if generics.is_empty()
        );
        let ty = if omitted {
            let args = nominal_params(self.catalog, head)
                .iter()
                .map(|param| Ty::Param(param.symbol))
                .collect::<Vec<_>>();
            Ty::Nominal(head, args)
        } else {
            self.lower_annotation(annotation)
        };
        let Ty::Nominal(actual_head, args) = ty else {
            self.unsupported(
                annotation.id,
                "extension head must be a nominal type or protocol",
            );
            return None;
        };
        let args = args
            .into_iter()
            .filter(|arg| !matches!(arg, Ty::Eff(_)))
            .collect::<Vec<_>>();
        Some((actual_head, Ty::Nominal(actual_head, args.clone()), args))
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
            binders,
            head: head_annotation,
            where_clause,
            ..
        } = &decl.kind
        else {
            return None;
        };
        self.register_generic_bounds(binders);
        let (head, mut self_ty, mut self_args) = if let Some(parent) = enclosing {
            let args = param_symbols(&nominal_params(self.catalog, parent))
                .into_iter()
                .map(Ty::Param)
                .collect::<Vec<_>>();
            (parent, Ty::Nominal(parent, args.clone()), args)
        } else {
            self.lower_extension_head(head_annotation)?
        };
        let protocol_head = enclosing.is_none() && self.catalog.protocols.contains_key(&head);
        if protocol_head && !binders.is_empty() {
            self.unsupported(decl.id, "generic protocol extensions");
            return None;
        }
        if protocol_head {
            self_ty = Ty::Param(head);
            self_args.clear();
        }

        let mut params = generic_symbols(binders);
        for param in self_args.iter().filter_map(|arg| match arg {
            Ty::Param(param) => Some(*param),
            _ => None,
        }) {
            if !params.contains(&param) {
                params.push(param);
            }
        }
        if protocol_head {
            params.push(head);
            if let Some(info) = self.catalog.protocols.get(&head) {
                params.extend(info.params.iter().map(|param| param.symbol));
                params.extend(info.assoc.values().copied());
            }
        }
        self.in_declaration_context(
            Some(self_ty.clone()),
            binders,
            where_clause.as_ref(),
            |this, decl_context| {
                let (params, self_ty) =
                    this.refine_extension_head(params, self_ty, &mut decl_context.predicates);
                let self_args = match &self_ty {
                    Ty::Nominal(_, args) => args.clone(),
                    _ => vec![],
                };
                this.register_extend_body(
                    decl,
                    head,
                    protocol_head,
                    params,
                    self_args,
                    self_ty,
                    decl_context,
                )
            },
        )
    }

    /// Absorb solvable equality premises over self-pattern parameters into
    /// the instance head before coherence and lookup see the row.
    fn refine_extension_head(
        &mut self,
        mut params: Vec<Symbol>,
        mut self_ty: Ty,
        predicates: &mut Vec<Predicate>,
    ) -> (Vec<Symbol>, Ty) {
        let mut head_params = FxHashSet::default();
        collect_ty_params(&self_ty, None, &mut head_params);
        let mut substitution = FxHashMap::default();
        let mut retained = vec![];

        for predicate in std::mem::take(predicates) {
            let pair = match &predicate {
                Predicate::TypeEq(lhs, rhs) => Some((lhs.clone(), rhs.clone())),
                Predicate::StaticCmp {
                    op: StaticCmpOp::Eq,
                    lhs,
                    rhs,
                } => Some((lhs.clone(), rhs.clone())),
                _ => None,
            };
            let Some((lhs, rhs)) = pair else {
                retained.push(predicate);
                continue;
            };
            let binding = match (&lhs, &rhs) {
                (Ty::Param(param), other)
                    if head_params.contains(param) && !ty_mentions_param(other, *param) =>
                {
                    Some((*param, other.clone()))
                }
                (other, Ty::Param(param))
                    if head_params.contains(param) && !ty_mentions_param(other, *param) =>
                {
                    Some((*param, other.clone()))
                }
                _ => None,
            };
            if let Some((param, ty)) = binding {
                let ty = ty.substitute(&substitution, &Default::default(), &Default::default());
                substitution.insert(param, ty);
            } else {
                retained.push(predicate);
            }
        }

        if !substitution.is_empty() {
            self_ty = self_ty.substitute(&substitution, &Default::default(), &Default::default());
            retained = retained
                .into_iter()
                .map(|predicate| {
                    predicate.substitute(&substitution, &Default::default(), &Default::default())
                })
                .collect();
            params.retain(|param| !substitution.contains_key(param));
        }
        *predicates = retained;
        (params, self_ty)
    }

    #[allow(clippy::too_many_arguments)]
    fn register_extend_body(
        &mut self,
        decl: &'a Decl,
        head: Symbol,
        protocol_head: bool,
        params: Vec<Symbol>,
        self_args: Vec<Ty>,
        self_ty: Ty,
        decl_context: &mut elaborate::DeclContext,
    ) -> Option<ExtendWork<'a>> {
        let DeclKind::Extend {
            conformances, body, ..
        } = &decl.kind
        else {
            return None;
        };
        if protocol_head {
            let head_protocol = ProtocolRef {
                protocol: head,
                args: self
                    .catalog
                    .protocols
                    .get(&head)
                    .map(|info| info.params.iter().map(|p| Ty::Param(p.symbol)).collect())
                    .unwrap_or_default(),
            };
            decl_context.predicates.insert(
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
                decl_context.predicates.push(Predicate::TypeEq(
                    Ty::Param(assoc),
                    Ty::Proj(Box::new(self_ty.clone()), owner, assoc),
                ));
            }
        }
        let context = &decl_context.predicates;

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
                // A row is owned only by the protocol explicitly named in
                // the declaration. Superprotocol satisfaction is a derived
                // catalog query, not a second physical row with a competing
                // identity.
                if conformed != protocol {
                    continue;
                }
                let Some(info) = self.catalog.protocols.get(&conformed.protocol).cloned() else {
                    continue;
                };
                let requirements = self.catalog.requirements_for_conformance(&conformed);
                let conformance = rows.entry(conformed.clone()).or_insert_with(|| {
                    let mut row = Conformance::new(head, conformed.clone());
                    row.params = params.clone();
                    row.self_args = self_args.clone();
                    row.context = context.clone();
                    row
                });

                // Positional associated-type application: `Iterator<Element>`
                // binds the named protocol's own assoc params in declaration
                // order. Inherited assoc params bind through same-named
                // `typealias` declarations or witness inference below.
                if conformed == protocol {
                    for (assoc_symbol, arg) in info.assoc.values().zip(&assoc_args) {
                        let Some(annotation) = arg.as_type() else {
                            self.diagnostics
                                .errors
                                .push((TypeError::StaticValueInTypePosition, arg.id()));
                            continue;
                        };
                        let binding = self.lower_annotation(annotation);
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
                    // An init requirement witnesses through the conforming
                    // type's initializers (explicit or synthesized
                    // memberwise), matched by arity.
                    if label == "init"
                        && let Some(init) = self.init_witness(head, &requirement)
                    {
                        conformance.witnesses.insert(label.clone(), init);
                        witnessed.insert(label.clone());
                        continue;
                    }
                    match members.get(&label) {
                        Some((witness, func)) => {
                            conformance.witnesses.insert(label.clone(), *witness);
                            witnessed.insert(label.clone());
                            self.infer_assoc_bindings(&requirement, func, conformance);
                        }
                        None => {
                            let already_conforms_to_owner = self
                                .catalog
                                .conformances_for_head(head)
                                .any(|(_, row)| row.protocol == owner);
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

        let mut registered_rows = vec![];
        for (protocol, conformance) in rows {
            let overlaps_existing = self
                .catalog
                .conformances_for_head(head)
                .find(|(_, existing)| {
                    existing.protocol.protocol == protocol.protocol
                        && self.catalog.conformance_rows_overlap(
                            &existing.protocol,
                            existing,
                            &protocol,
                            &conformance,
                        )
                })
                .map(|(_, existing)| existing.protocol.clone());
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
            let id = self.catalog.insert_conformance(conformance);
            registered_rows.push((protocol, id));
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
                context: context.clone(),
                decl,
                protocols,
                rows: registered_rows,
            });
        }

        // Members that witness no requirement are inherent: register their
        // annotation-derived signatures so any group can dispatch on them.
        self.self_types.push(self_ty.clone());
        for (label, (method, func)) in &members {
            if witnessed.contains(label) {
                continue;
            }
            // The method's own generics and where clause are a nested
            // declaration context: its bounds (including static value
            // params) register before its annotations lower, and its
            // formation obligations prove under its own predicates.
            let (sig_params, ret, method_predicates) = self.in_declaration_context(
                None,
                &func.generics,
                func.where_clause.as_ref(),
                |this, method_context| {
                    let sig_params: Vec<Ty> = func
                        .params
                        .iter()
                        .map(|p| match &p.type_annotation {
                            Some(annotation) => {
                                let ty = this.lower_annotation(annotation);
                                elaborate::apply_param_mode(this.catalog, p, ty, this.diagnostics)
                            }
                            None => Ty::Var(this.store.fresh_ty(OUTER_LEVEL, p.id)),
                        })
                        .collect();
                    let ret = match &func.ret {
                        Some(annotation) => this.lower_annotation(annotation),
                        None => Ty::Var(this.store.fresh_ty(OUTER_LEVEL, func.id)),
                    };
                    (sig_params, ret, method_context.predicates.clone())
                },
            );
            let mut predicates = context.clone();
            for predicate in method_predicates {
                if !predicates.contains(&predicate) {
                    predicates.push(predicate);
                }
            }
            let eff = EffectRow {
                effects: Default::default(),
                tail: Some(EffTail::Param(*method)),
            };
            // The annotation-derived signature is an ordinary scheme (the
            // one signature carrier); `check_extend` replaces it with the
            // inferred, zonked scheme after the body checks. The catalog
            // keeps only the instance-head pattern.
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
            context: context.clone(),
            decl,
            protocols,
            rows: registered_rows,
        })
    }

    /// The initializer witnessing an init requirement: the conforming
    /// type's init whose arity matches the requirement's parameter list
    /// (initializer signatures carry a prepended `self`; the requirement's
    /// do not).
    fn init_witness(&self, head: Symbol, requirement: &Requirement) -> Option<Symbol> {
        let scheme = self.schemes.get(&requirement.symbol)?;
        let Ty::Func(params, ..) = &scheme.ty else {
            return None;
        };
        let arity = params.len();
        self.catalog
            .structs
            .get(&head)?
            .inits
            .iter()
            .find(|(_, init_arity)| *init_arity == arity + 1)
            .map(|(init, _)| *init)
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
                    elaborate::apply_param_mode(self.catalog, p, ty, self.diagnostics)
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
