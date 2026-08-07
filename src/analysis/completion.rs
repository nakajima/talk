use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::workspace::Workspace;
use crate::analysis::{CompletionItem, CompletionItemKind, DocumentId, node_ids_at_offset};
use crate::{
    ast::{AST, NameResolved},
    name_resolution::{
        name_resolver::{ResolvedNames, Scope},
        symbol::Symbol,
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        incomplete_expr::IncompleteExpr,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    types::{
        TypeOutput,
        catalog::Requirement,
        ty::{EffTail, ProtocolRef, RowTail, Ty},
    },
};

pub struct CompletionAnalysis<'a> {
    pub ast: &'a AST<NameResolved>,
    pub all_asts: Option<&'a [Option<AST<NameResolved>>]>,
    pub resolved_names: &'a ResolvedNames,
    pub types: &'a TypeOutput,
}

impl CompletionAnalysis<'_> {
    /// The ASTs a requirement-signature lookup may search: every file
    /// in the workspace when available, the completion file otherwise.
    fn requirement_source_asts(&self) -> Box<dyn Iterator<Item = &AST<NameResolved>> + '_> {
        match self.all_asts {
            Some(asts) => Box::new(asts.iter().flatten()),
            None => Box::new(std::iter::once(self.ast)),
        }
    }
}

/// The access site completion answers for: the session module and the
/// cursor's file (ADR 0042).
#[derive(Clone, Copy)]
struct Viewer {
    module: crate::compiling::module::ModuleId,
    file: crate::node_id::FileID,
}

impl Viewer {
    fn member_accessible(&self, types: &TypeOutput, symbol: Symbol) -> bool {
        types
            .catalog
            .member_accessible(symbol, self.module, self.file)
    }
}

pub fn complete_in_workspace(
    workspace: &Workspace,
    document_id: &DocumentId,
    byte_offset: u32,
) -> Vec<CompletionItem> {
    let Some(idx) = workspace.document_index(document_id) else {
        return vec![];
    };
    let Some(text) = workspace.texts.get(idx) else {
        return vec![];
    };
    let Some(ast) = workspace.asts.get(idx).and_then(|a| a.as_ref()) else {
        return vec![];
    };

    let completion = CompletionAnalysis {
        ast,
        all_asts: Some(&workspace.asts),
        resolved_names: &workspace.resolved_names,
        types: &workspace.types,
    };

    let mut items = complete(text.text(), &completion, byte_offset);
    if member_completion_dot(text.text(), byte_offset).is_none() {
        let visible_labels: FxHashSet<_> = items.iter().map(|item| item.label.clone()).collect();
        for candidate in workspace.import_candidates(document_id) {
            if visible_labels.contains(candidate.name.as_str()) {
                continue;
            }
            items.push(CompletionItem {
                label: candidate.name.clone(),
                kind: completion_kind(candidate.symbol),
                detail: Some(format!("Auto import from {}", candidate.module_path)),
                insert_text: None,
                insert_text_is_snippet: false,
                sort_text: Some(format!("~{}::{}", candidate.name, candidate.module_path)),
                import_from: Some(candidate.module_path),
            });
        }
    }
    items.sort_by(|left, right| {
        (&left.label, &left.import_from).cmp(&(&right.label, &right.import_from))
    });
    items
}

pub fn complete(
    text: &str,
    analysis: &CompletionAnalysis<'_>,
    byte_offset: u32,
) -> Vec<CompletionItem> {
    let _names =
        crate::name_resolution::symbol::set_symbol_names(analysis.types.display_names.clone());

    if let Some(dot_offset) = member_completion_dot(text, byte_offset) {
        return member_completions(analysis, dot_offset);
    }

    scope_completions(analysis, byte_offset)
}

fn member_completion_dot(text: &str, byte_offset: u32) -> Option<u32> {
    let bytes = text.as_bytes();
    let mut i = (byte_offset as usize).min(bytes.len());

    while i > 0 && is_ident_byte(bytes[i - 1]) {
        i -= 1;
    }

    while i > 0 && matches!(bytes[i - 1], b' ' | b'\t' | b'\r') {
        i -= 1;
    }

    if i > 0 && bytes[i - 1] == b'.' {
        return Some((i - 1) as u32);
    }

    None
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn scope_completions(analysis: &CompletionAnalysis<'_>, byte_offset: u32) -> Vec<CompletionItem> {
    let symbols = visible_symbols(analysis, byte_offset);
    let mut items: Vec<CompletionItem> = symbols
        .into_iter()
        .map(|(name, sym)| CompletionItem {
            label: name,
            kind: completion_kind(sym),
            detail: None,
            insert_text: None,
            insert_text_is_snippet: false,
            sort_text: None,
            import_from: None,
        })
        .collect();

    items.extend(conformance_requirement_completions(analysis, byte_offset));
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn member_completions(analysis: &CompletionAnalysis<'_>, dot_offset: u32) -> Vec<CompletionItem> {
    let Some(receiver) = member_completion_receiver(analysis.ast, dot_offset) else {
        return vec![];
    };
    let mut items = FxHashMap::default();
    let viewer = Viewer {
        module: analysis.types.module_id,
        file: analysis.ast.file_id,
    };
    if let Some(symbol) = type_receiver_symbol(&receiver) {
        add_type_member_items(analysis.types, symbol, viewer, &mut items);
    } else if let Some(receiver_ty) = analysis.types.node_types.get(&receiver.id) {
        add_member_items_for_ty(analysis.types, receiver_ty, viewer, &mut items);
    }

    let mut items: Vec<CompletionItem> = items.into_values().collect();
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn member_completion_receiver(ast: &AST<NameResolved>, dot_offset: u32) -> Option<Expr> {
    for node_id in node_ids_at_offset(ast, dot_offset) {
        let Some(node) = ast.find(node_id) else {
            continue;
        };
        let expr = match node {
            Node::Expr(expr) => expr,
            Node::Stmt(crate::node_kinds::stmt::Stmt {
                kind: crate::node_kinds::stmt::StmtKind::Expr(expr),
                ..
            }) => expr,
            Node::CallArg(arg) => arg.value,
            _ => continue,
        };
        match &expr.kind {
            ExprKind::Incomplete(IncompleteExpr::Member(Some(receiver)))
                if receiver.span.end <= dot_offset && dot_offset <= expr.span.end =>
            {
                return Some((**receiver).clone());
            }
            ExprKind::Member(Some(receiver), _, label_span)
                if receiver.span.end <= dot_offset && dot_offset <= label_span.start =>
            {
                return Some((**receiver).clone());
            }
            _ => {}
        }
    }
    None
}

fn type_receiver_symbol(receiver: &Expr) -> Option<Symbol> {
    let ExprKind::Constructor(name, ..) = &receiver.kind else {
        return None;
    };
    name.symbol().ok()
}

fn add_member_items_for_ty(
    types: &TypeOutput,
    receiver_ty: &Ty,
    viewer: Viewer,
    items: &mut FxHashMap<String, CompletionItem>,
) {
    match member_lookup_ty(receiver_ty) {
        // Stripped by member_lookup_ty; unreachable here.
        Ty::Unique(_) => {}
        Ty::Forall(scheme) => add_member_items_for_ty(types, &scheme.ty, viewer, items),
        Ty::Nominal(symbol, args) => {
            add_nominal_member_items(types, *symbol, args, receiver_ty, viewer, items);
        }
        Ty::Record(row) => {
            for (label, ty) in &row.fields {
                add_member_item(
                    items,
                    label.to_string(),
                    CompletionItemKind::Field,
                    Some(ty.render_mono()),
                );
            }
        }
        Ty::Any { protocol, .. } => {
            add_protocol_requirement_items(types, protocol, receiver_ty, items);
        }
        Ty::Param(param) => {
            if let Some(bounds) = types.catalog.param_bounds.get(param) {
                for protocol in bounds {
                    add_protocol_requirement_items(types, protocol, receiver_ty, items);
                }
            }
        }
        Ty::Proj(_, _, assoc_symbol) => {
            if let Some(bounds) = types.catalog.param_bounds.get(assoc_symbol) {
                for protocol in bounds {
                    add_protocol_requirement_items(types, protocol, receiver_ty, items);
                }
            }
        }
        Ty::Borrow(..)
        | Ty::Func(..)
        | Ty::Tuple(_)
        | Ty::Var(_)
        | Ty::Eff(_)
        | Ty::Static(_)
        | Ty::Error => {}
    }
}

fn member_lookup_ty(mut ty: &Ty) -> &Ty {
    loop {
        match ty {
            Ty::Borrow(_, inner) | Ty::Unique(inner) => ty = inner,
            _ => return ty,
        }
    }
}

fn add_nominal_member_items(
    types: &TypeOutput,
    symbol: Symbol,
    args: &[Ty],
    receiver_ty: &Ty,
    viewer: Viewer,
    items: &mut FxHashMap<String, CompletionItem>,
) {
    if let Some(info) = types.catalog.structs.get(&symbol) {
        let substitution = param_subst(&info.params, args);
        for (label, (property, field_ty)) in &info.fields {
            if !viewer.member_accessible(types, *property) {
                continue;
            }
            let ty = substitute_ty(field_ty, &substitution);
            add_member_item(
                items,
                label.clone(),
                CompletionItemKind::Field,
                Some(ty.render_mono()),
            );
        }
        for (label, set) in &info.methods {
            for method in set {
                if !viewer.member_accessible(types, *method) {
                    continue;
                }
                add_symbol_member_item(types, label, *method, &info.params, args, true, items);
            }
        }
    }

    if let Some(info) = types.catalog.enums.get(&symbol) {
        for (label, set) in &info.methods {
            for method in set {
                if !viewer.member_accessible(types, *method) {
                    continue;
                }
                add_symbol_member_item(types, label, *method, &info.params, args, true, items);
            }
        }
    }

    if types.catalog.conformances_by_head.contains_key(&symbol) {
        for (id, row) in types.catalog.conformances_for_head(symbol) {
            let applies = types
                .catalog
                .matching_conformances(symbol, args, &row.protocol)
                .iter()
                .any(|matched| matched.id == id);
            if applies {
                add_protocol_requirement_items(types, &row.protocol, receiver_ty, items);
            }
        }
    }

    let is_derivable_head =
        types.catalog.structs.contains_key(&symbol) || types.catalog.enums.contains_key(&symbol);
    if is_derivable_head {
        for protocol in crate::types::catalog::TypeCatalog::derivable_protocols() {
            add_protocol_requirement_items(types, &ProtocolRef::bare(protocol), receiver_ty, items);
        }
    }

    if let Some(members) = types.catalog.extend_members.get(&symbol) {
        for (label, rows) in members {
            // Only rows whose instance head matches the receiver's complete
            // application are completable (ADR 0036): a member on Box<Int>
            // is absent from Box<String>.
            let Some(inherent) = rows.iter().find(|row| {
                if !viewer.member_accessible(types, row.symbol) {
                    return false;
                }
                let mut probe = FxHashMap::default();
                row.self_args.iter().zip(args).all(|(pattern, actual)| {
                    crate::types::ty::match_pattern(pattern, actual, &mut probe)
                })
            }) else {
                continue;
            };
            let mut substitution = FxHashMap::default();
            for (pattern, actual) in inherent.self_args.iter().zip(args) {
                crate::types::solve::bind_param_pattern(pattern, actual, &mut substitution);
            }
            let Some(scheme) = types.schemes.get(&inherent.symbol) else {
                continue;
            };
            let ty = substitute_ty(&scheme.ty, &substitution);
            add_member_item(
                items,
                label.clone(),
                CompletionItemKind::Method,
                Some(drop_self_from_func(ty).render_mono()),
            );
        }
    }
}

fn add_type_member_items(
    types: &TypeOutput,
    symbol: Symbol,
    viewer: Viewer,
    items: &mut FxHashMap<String, CompletionItem>,
) {
    if let Some(info) = types.catalog.enums.get(&symbol) {
        for (label, variant) in &info.variants {
            add_member_item(
                items,
                label.clone(),
                CompletionItemKind::EnumMember,
                Some(variant.constructor_scheme.render()),
            );
        }
    }

    if let Some(info) = types.catalog.structs.get(&symbol) {
        for (label, set) in &info.statics {
            for method in set {
                if !viewer.member_accessible(types, *method) {
                    continue;
                }
                add_symbol_member_item(types, label, *method, &info.params, &[], false, items);
            }
        }
    }

    if types.catalog.protocols.contains_key(&symbol) {
        for (_, label, requirement) in types
            .catalog
            .requirements_for_conformance(&ProtocolRef::bare(symbol))
        {
            add_member_item(
                items,
                label,
                CompletionItemKind::Method,
                types
                    .schemes
                    .get(&requirement.symbol)
                    .map(|scheme| scheme.ty.render_mono()),
            );
        }
    }
}

fn add_symbol_member_item(
    types: &TypeOutput,
    label: &str,
    symbol: Symbol,
    owner_params: &[crate::types::ty::SchemeParam],
    owner_args: &[Ty],
    drop_self: bool,
    items: &mut FxHashMap<String, CompletionItem>,
) {
    let detail = types.schemes.get(&symbol).map(|scheme| {
        let substitution = param_subst(owner_params, owner_args);
        let ty = substitute_ty(&scheme.ty, &substitution);
        if drop_self {
            drop_self_from_func(ty).render_mono()
        } else {
            ty.render_mono()
        }
    });
    add_member_item(items, label.to_string(), CompletionItemKind::Method, detail);
}

fn add_protocol_requirement_items(
    types: &TypeOutput,
    protocol: &ProtocolRef,
    receiver_ty: &Ty,
    items: &mut FxHashMap<String, CompletionItem>,
) {
    for (owner, label, requirement) in types.catalog.requirements_for_conformance(protocol) {
        add_member_item(
            items,
            label,
            CompletionItemKind::Method,
            requirement_detail(types, owner, &requirement, receiver_ty),
        );
    }
}

fn requirement_detail(
    types: &TypeOutput,
    owner: ProtocolRef,
    requirement: &Requirement,
    receiver_ty: &Ty,
) -> Option<String> {
    let lookup_ty = member_lookup_ty(receiver_ty).clone();
    let mut substitution = FxHashMap::default();
    substitution.insert(owner.protocol, lookup_ty.clone());
    if let Some(info) = types.catalog.protocols.get(&owner.protocol) {
        for (param, arg) in info
            .params
            .iter()
            .map(|param| param.symbol)
            .zip(owner.args.iter().cloned())
        {
            substitution.insert(param, arg);
        }
    }
    for (_, _, assoc) in types.catalog.associated_types_in_ref(&owner) {
        let binding = associated_binding(&lookup_ty, assoc)
            .unwrap_or_else(|| Ty::Proj(Box::new(lookup_ty.clone()), owner.clone(), assoc));
        substitution.insert(assoc, binding);
    }
    let sig = types.schemes.get(&requirement.symbol)?.ty.clone();
    let ty = substitute_ty(&sig, &substitution);
    Some(drop_self_from_func(ty).render_mono())
}

fn associated_binding(receiver_ty: &Ty, assoc_symbol: Symbol) -> Option<Ty> {
    let Ty::Any { assoc, .. } = receiver_ty else {
        return None;
    };
    assoc
        .iter()
        .find_map(|(symbol, ty)| (*symbol == assoc_symbol).then(|| ty.clone()))
}

fn param_subst(params: &[crate::types::ty::SchemeParam], args: &[Ty]) -> FxHashMap<Symbol, Ty> {
    params
        .iter()
        .map(|param| param.symbol)
        .zip(args.iter().cloned())
        .collect()
}

fn substitute_ty(ty: &Ty, tys: &FxHashMap<Symbol, Ty>) -> Ty {
    let effs: FxHashMap<Symbol, EffTail> = FxHashMap::default();
    let rows: FxHashMap<Symbol, RowTail> = FxHashMap::default();
    ty.substitute(tys, &effs, &rows)
}

fn drop_self_from_func(ty: Ty) -> Ty {
    match ty {
        Ty::Func(params, ret, eff) if !params.is_empty() => {
            Ty::Func(params[1..].to_vec(), ret, eff)
        }
        other => other,
    }
}

fn add_member_item(
    items: &mut FxHashMap<String, CompletionItem>,
    label: String,
    kind: CompletionItemKind,
    detail: Option<String>,
) {
    items.entry(label.clone()).or_insert(CompletionItem {
        label,
        kind: Some(kind),
        detail,
        insert_text: None,
        insert_text_is_snippet: false,
        sort_text: None,
        import_from: None,
    });
}

struct ImplementedConformanceMembers {
    methods: FxHashSet<String>,
    associated: FxHashSet<String>,
}

fn conformance_requirement_completions(
    analysis: &CompletionAnalysis<'_>,
    byte_offset: u32,
) -> Vec<CompletionItem> {
    let Some(extend) = enclosing_extend_decl(analysis.ast, byte_offset) else {
        return vec![];
    };
    if !directly_in_extend_body(&extend, byte_offset) {
        return vec![];
    }

    let protocols = conformance_protocol_refs(analysis.types, &extend);
    if protocols.is_empty() {
        return vec![];
    }

    let implemented = implemented_conformance_members(&extend);
    let mut items: FxHashMap<String, CompletionItem> = FxHashMap::default();
    for protocol in protocols {
        for (owner, label, requirement) in analysis
            .types
            .catalog
            .requirements_for_conformance(&protocol)
        {
            if implemented.methods.contains(&label) {
                continue;
            }
            let suggestion = crate::analysis::requirements::requirement_suggestion(
                analysis.requirement_source_asts(),
                analysis.types,
                owner.to_string(),
                label.clone(),
                &requirement,
            );
            items.entry(label.clone()).or_insert(CompletionItem {
                label,
                kind: Some(CompletionItemKind::Method),
                detail: Some(format!("required by {}: {}", suggestion.owner, suggestion.signature)),
                insert_text: Some(suggestion.stub(true)),
                insert_text_is_snippet: true,
                sort_text: None,
                import_from: None,
            });
        }

        for (name, owner, _) in analysis.types.catalog.associated_types_in_ref(&protocol) {
            if implemented.associated.contains(&name) {
                continue;
            }
            items.entry(name.clone()).or_insert(CompletionItem {
                label: name.clone(),
                kind: Some(CompletionItemKind::TypeParameter),
                detail: Some(format!("associated type required by {owner}")),
                insert_text: Some(format!("typealias {name} = $0")),
                insert_text_is_snippet: true,
                sort_text: None,
                import_from: None,
            });
        }
    }

    let mut items: Vec<_> = items.into_values().collect();
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn enclosing_extend_decl(ast: &AST<NameResolved>, byte_offset: u32) -> Option<Decl> {
    node_ids_at_offset(ast, byte_offset)
        .into_iter()
        .filter_map(|node_id| match ast.find(node_id) {
            Some(Node::Decl(
                decl @ Decl {
                    kind: DeclKind::Extend { .. },
                    ..
                },
            )) => Some(decl),
            _ => None,
        })
        .find(|decl| match &decl.kind {
            DeclKind::Extend { body, .. } => {
                body.span.start <= byte_offset && byte_offset <= body.span.end
            }
            _ => false,
        })
}

fn directly_in_extend_body(extend: &Decl, byte_offset: u32) -> bool {
    let DeclKind::Extend { body, .. } = &extend.kind else {
        return false;
    };
    if !(body.span.start <= byte_offset && byte_offset <= body.span.end) {
        return false;
    }
    !body
        .decls
        .iter()
        .any(|decl| decl.span.start <= byte_offset && byte_offset <= decl.span.end)
}

fn implemented_conformance_members(extend: &Decl) -> ImplementedConformanceMembers {
    let mut methods = FxHashSet::default();
    let mut associated = FxHashSet::default();
    let DeclKind::Extend { body, .. } = &extend.kind else {
        return ImplementedConformanceMembers {
            methods,
            associated,
        };
    };

    for decl in &body.decls {
        match &decl.kind {
            DeclKind::Method { func, .. } => {
                methods.insert(func.name.name_str());
            }
            DeclKind::TypeAlias(name, ..) => {
                associated.insert(name.name_str());
            }
            _ => {}
        }
    }

    ImplementedConformanceMembers {
        methods,
        associated,
    }
}

fn conformance_protocol_refs(types: &TypeOutput, extend: &Decl) -> Vec<ProtocolRef> {
    let DeclKind::Extend {
        head, conformances, ..
    } = &extend.kind
    else {
        return vec![];
    };
    let Some(head) = head.symbol().ok() else {
        return vec![];
    };

    let mut refs = vec![];
    for conformance in conformances {
        let Some(protocol) = type_annotation_symbol(conformance) else {
            continue;
        };
        let mut matched = false;
        for (_, row) in types.catalog.conformances_for_head(head) {
            if row.protocol.protocol == protocol {
                if !refs.contains(&row.protocol) {
                    refs.push(row.protocol.clone());
                }
                matched = true;
            }
        }
        if !matched {
            let protocol_ref = ProtocolRef::bare(protocol);
            if !refs.contains(&protocol_ref) {
                refs.push(protocol_ref);
            }
        }
    }
    refs
}

fn type_annotation_symbol(annotation: &TypeAnnotation) -> Option<Symbol> {
    match &annotation.kind {
        TypeAnnotationKind::Nominal { .. } | TypeAnnotationKind::SelfType(_) => {
            annotation.symbol().ok()
        }
        _ => None,
    }
}

fn visible_symbols(
    analysis: &CompletionAnalysis<'_>,
    byte_offset: u32,
) -> FxHashMap<String, Symbol> {
    let root_id = NodeID(analysis.ast.file_id, 0);

    let mut best: Option<&Scope> = None;
    for scope in analysis.resolved_names.scopes.values() {
        let Some(meta) = analysis.ast.meta.get(&scope.node_id) else {
            continue;
        };

        let start = meta.start.start;
        let end = meta.end.end;
        if start <= byte_offset && byte_offset <= end {
            best = match best {
                Some(current) if current.depth >= scope.depth => Some(current),
                _ => Some(scope),
            };
        }
    }

    let mut result: FxHashMap<String, Symbol> = FxHashMap::default();
    let mut chain: FxHashSet<NodeID> = FxHashSet::default();
    let mut current_id: Option<NodeID> = best.map(|s| s.node_id).or(Some(root_id));

    while let Some(id) = current_id {
        let Some(scope) = analysis.resolved_names.scopes.get(&id) else {
            break;
        };
        chain.insert(id);

        for (name, sym) in scope.types.iter().chain(scope.values.iter()) {
            // Sequential locals re-enter below with per-position facts:
            // the final scope map keeps only the last same-named binder,
            // which loses the binding visible before a shadow.
            // Func-valued binders hoist block-wide (ADR 0013) and stay
            // on the map path — their own scope wraps the binder span,
            // which defeats the containment test below.
            if matches!(sym, Symbol::DeclaredLocal(_) | Symbol::PatternBindLocal(_))
                && !matches!(
                    analysis.types.binder_ty(*sym),
                    Some(crate::types::ty::Ty::Func(..))
                )
            {
                continue;
            }
            result.entry(name.clone()).or_insert(*sym);
        }

        current_id = scope.parent_id;
    }

    // ADR 0013 locals: every binder declared in a chain scope, visible
    // at the cursor — a `let` after its full declaration, a func-valued
    // binder block-wide — with the latest pre-cursor binder winning per
    // name.
    let mut latest: FxHashMap<String, (u32, Symbol)> = FxHashMap::default();
    for (&symbol, record) in &analysis.resolved_names.declarations {
        if record.file != analysis.ast.file_id
            || !matches!(
                record.role,
                crate::name_resolution::symbol::SymbolKind::DeclaredLocal
                    | crate::name_resolution::symbol::SymbolKind::PatternBindLocal
            )
        {
            continue;
        }
        let Some(&node) = analysis.resolved_names.symbols_to_node.get(&symbol) else {
            continue;
        };
        let Some(meta) = analysis.ast.meta.get(&node) else {
            continue;
        };
        let binder_start = meta.start.start;
        let binder_end = meta.end.end;
        if !chain.contains(&tightest_scope(analysis, binder_start, binder_end)) {
            continue;
        }
        // Func-valued binders took the map path above.
        if matches!(
            analysis.types.binder_ty(symbol),
            Some(crate::types::ty::Ty::Func(..))
        ) {
            continue;
        }
        // Visibility begins after the binder's full declaration
        // (initializer included); match binders and loop binders
        // have no enclosing `let` and settle at the binder itself.
        let visible_from = enclosing_let_end(analysis, binder_start).unwrap_or(binder_end);
        if byte_offset < visible_from {
            continue;
        }
        let Some(name) = analysis.resolved_names.symbol_names.get(&symbol) else {
            continue;
        };
        match latest.get(name.as_str()) {
            Some((start, _)) if *start >= binder_start => {}
            _ => {
                latest.insert(name.clone(), (binder_start, symbol));
            }
        }
    }
    for (name, (_, symbol)) in latest {
        result.insert(name, symbol);
    }

    result
}

/// The deepest scope whose span contains the binder — the scope it was
/// declared in.
fn tightest_scope(analysis: &CompletionAnalysis<'_>, start: u32, end: u32) -> NodeID {
    let root_id = NodeID(analysis.ast.file_id, 0);
    let mut tightest: Option<(NodeID, u32)> = None;
    for scope in analysis.resolved_names.scopes.values() {
        let Some(meta) = analysis.ast.meta.get(&scope.node_id) else {
            continue;
        };
        let (scope_start, scope_end) = (meta.start.start, meta.end.end);
        if scope_start <= start && end <= scope_end {
            let size = scope_end - scope_start;
            if tightest.is_none_or(|(_, best)| size < best) {
                tightest = Some((scope.node_id, size));
            }
        }
    }
    tightest.map(|(id, _)| id).unwrap_or(root_id)
}

/// The end of the `let` declaration containing a binder at
/// `binder_start`, initializer included.
fn enclosing_let_end(analysis: &CompletionAnalysis<'_>, binder_start: u32) -> Option<u32> {
    for node_id in node_ids_at_offset(analysis.ast, binder_start) {
        let Some(crate::node::Node::Decl(decl)) = analysis.ast.find(node_id) else {
            continue;
        };
        if matches!(decl.kind, crate::node_kinds::decl::DeclKind::Let { .. }) {
            return analysis.ast.meta.get(&decl.id).map(|meta| meta.end.end);
        }
    }
    None
}

fn completion_kind(symbol: Symbol) -> Option<CompletionItemKind> {
    Some(match symbol {
        Symbol::Struct(..) => CompletionItemKind::Struct,
        Symbol::Enum(..) => CompletionItemKind::Enum,
        Symbol::Protocol(..) => CompletionItemKind::Interface,
        Symbol::TypeAlias(..) => CompletionItemKind::Class,
        Symbol::TypeParameter(..) | Symbol::AssociatedType(..) => CompletionItemKind::TypeParameter,
        Symbol::Effect(..) => CompletionItemKind::Effect,
        Symbol::Global(..)
        | Symbol::DeclaredLocal(..)
        | Symbol::PatternBindLocal(..)
        | Symbol::ParamLocal(..)
        | Symbol::Synthesized(..) => CompletionItemKind::Variable,

        Symbol::Property(..) => CompletionItemKind::Field,
        Symbol::InstanceMethod(..) | Symbol::StaticMethod(..) | Symbol::MethodRequirement(..) => {
            CompletionItemKind::Method
        }
        Symbol::Initializer(..) => CompletionItemKind::Constructor,
        Symbol::Variant(..) => CompletionItemKind::EnumMember,

        Symbol::Builtin(..) => CompletionItemKind::Keyword,
        Symbol::Main | Symbol::Library => CompletionItemKind::Module,
    })
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use crate::{
        analysis::completion::CompletionAnalysis,
        ast::{AST, NameResolved},
        compiling::driver::{Driver, DriverConfig, Source},
        name_resolution::name_resolver::ResolvedNames,
        types::TypeOutput,
    };

    pub(crate) struct Analyzed {
        pub(crate) ast: AST<NameResolved>,
        pub(crate) resolved_names: ResolvedNames,
        pub(crate) types: TypeOutput,
    }

    pub(crate) fn analyze(code: &str) -> Analyzed {
        analyze_with_driver(code, Driver::new_bare)
    }

    fn analyze_with_stdlib(code: &str) -> Analyzed {
        analyze_with_driver(code, Driver::new)
    }

    fn analyze_with_driver(
        code: &str,
        driver: impl FnOnce(Vec<Source>, DriverConfig) -> Driver,
    ) -> Analyzed {
        let source = Source::in_memory(PathBuf::from("test.tlk"), code.to_string());
        let driver = driver(
            vec![source],
            DriverConfig::new("Test")
                .lenient_parsing()
                .preserve_comments(true),
        );
        let resolved = driver
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve");
        let ast = resolved.phase.asts.values().next().expect("ast").clone();
        let typed = resolved.type_check();
        let (resolved_names, types) = typed.phase.program.into_semantic_parts();
        Analyzed {
            ast,
            resolved_names,
            types,
        }
    }

    fn completion(analyzed: &Analyzed) -> CompletionAnalysis<'_> {
        CompletionAnalysis {
            ast: &analyzed.ast,
            all_asts: None,
            resolved_names: &analyzed.resolved_names,
            types: &analyzed.types,
        }
    }

    fn byte_offset_for(code: &str, needle: &str, nth: usize) -> u32 {
        code.match_indices(needle)
            .nth(nth)
            .map(|(i, _)| i as u32)
            .expect("needle")
    }

    #[test]
    fn completes_visible_names() {
        let code = "let foo = 1\nf\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "f", 0);
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "foo"),
            "expected foo in {items:?}"
        );
    }

    // ADR 0042 §6 / ADR 0013: scope completion uses source-position
    // facts — a sequential local is not suggested before its
    // declaration, while hoisted local funcs stay visible block-wide.
    #[test]
    fn scope_completion_is_sequential_for_locals() {
        let code = "func f() -> Int {\n\tlet early = 1\n\tx \n\tlet late = 2\n\tlate + early\n}\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "x ", 0) + 1;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "early"),
            "expected early in {items:?}"
        );
        assert!(
            !items.iter().any(|i| i.label == "late"),
            "late suggested before its declaration: {items:?}"
        );
    }

    // The final scope map keeps only the last same-named binder; the
    // binding visible BEFORE a later shadow must still complete.
    #[test]
    fn scope_completion_keeps_the_binding_before_a_shadow() {
        let code =
            "func f() -> Int {\n\tlet value = 1\n\tx \n\tlet value = 2\n\tvalue + value\n}\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "x ", 0) + 1;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "value"),
            "the pre-shadow binding must complete: {items:?}"
        );
    }

    // A binder is visible after its initializer, not inside it.
    #[test]
    fn scope_completion_excludes_the_binder_inside_its_initializer() {
        let code = "func f() -> Int {\n\tlet value = x + 1\n\tvalue\n}\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "x +", 0) + 1;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            !items.iter().any(|i| i.label == "value"),
            "a binder must not complete inside its own initializer: {items:?}"
        );
    }

    #[test]
    fn scope_completion_keeps_hoisted_local_funcs() {
        let code = "func f() -> Int {\n\tx \n\tfunc helper() -> Int { 2 }\n\thelper()\n}\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "x ", 0) + 1;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "helper"),
            "expected hoisted helper in {items:?}"
        );
    }

    #[test]
    fn completes_members_after_dot() {
        let code = "struct Dog {\n\tlet age: Int\n\tfunc bark() -> Int { self.age }\n}\nlet dog = Dog(age: 1)\ndog.\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "dog.", 0) + 4;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "age"
                && i.kind == Some(crate::analysis::CompletionItemKind::Field)
                && i.detail.as_deref() == Some("Int")),
            "expected age field in {items:?}"
        );
        assert!(
            items.iter().any(|i| i.label == "bark"
                && i.kind == Some(crate::analysis::CompletionItemKind::Method)),
            "expected bark method in {items:?}"
        );
    }

    #[test]
    fn completes_members_after_partial_label() {
        let code = "struct Dog {\n\tlet age: Int\n}\nlet dog = Dog(age: 1)\ndog.a\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "dog.a", 0) + 5;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "age"),
            "expected age in {items:?}"
        );
    }

    #[test]
    fn completes_members_after_dot_in_if_condition_before_body() {
        let code = "struct String {\n\tlet byte_count: Int\n}\nfunc starts_with(needle: &String) {\n\tif needle. {\n\t}\n}\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "needle.", 0) + 7;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "byte_count"
                && i.kind == Some(crate::analysis::CompletionItemKind::Field)),
            "expected byte_count field in {items:?}"
        );
    }

    #[test]
    fn completes_members_after_dot_in_unclosed_if_condition() {
        let code = "struct String {\n\tlet byte_count: Int\n}\nfunc starts_with(needle: &String) {\n\tif needle.\n}\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "needle.", 0) + 7;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "byte_count"
                && i.kind == Some(crate::analysis::CompletionItemKind::Field)),
            "expected byte_count field in {items:?}"
        );
    }

    #[test]
    fn completes_members_after_dot_in_loop_condition_before_body() {
        let code = "struct String {\n\tlet byte_count: Int\n}\nfunc starts_with(needle: &String) {\n\tlet i = 0\n\tloop i < needle. {\n\t}\n}\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "needle.", 0) + 7;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "byte_count"
                && i.kind == Some(crate::analysis::CompletionItemKind::Field)),
            "expected byte_count field in {items:?}"
        );
    }

    #[test]
    fn completes_members_after_dot_in_recovered_expression_delimiters() {
        let cases = [
            "match needle.\n",
            "match 0 {\n\t\t_ -> needle.\n",
            "sink(needle.\n",
            "sink(needle.,\n",
            "'sink_effect(needle.\n",
            "let x = [needle.\n",
            "let x = [needle.,\n",
            "let x = { value: needle.\n",
            "let x = { ...needle.\n",
            "let x = (needle.\n",
            "let x = if needle.\n",
        ];

        for body in cases {
            let code = format!(
                "effect 'sink_effect(value: Int) -> Int\nstruct String {{\n\tlet byte_count: Int\n}}\nfunc sink(value: Int) {{}}\nfunc starts_with(needle: &String) {{\n\t{body}}}\n"
            );
            let analyzed = analyze(&code);
            let byte_offset = byte_offset_for(&code, "needle.", 0) + 7;
            let completion = completion(&analyzed);
            let items = super::complete(&code, &completion, byte_offset);
            assert!(
                items.iter().any(|i| i.label == "byte_count"
                    && i.kind == Some(crate::analysis::CompletionItemKind::Field)),
                "{body}: expected byte_count field in {items:?}"
            );
        }
    }

    #[test]
    fn completes_members_for_borrowed_core_string_with_unknown_current_member() {
        let code = "extend String {\n\tfunc starts_with(needle: &String) -> Bool {\n\t\tif self.storage.get(0) != needle.byte_at(0) { return false }\n\t\ttrue\n\t}\n}\n";
        let analyzed = analyze_with_stdlib(code);
        let byte_offset = byte_offset_for(code, "needle.", 0) + 7;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "byte_count"
                && i.kind == Some(crate::analysis::CompletionItemKind::Field)),
            "expected byte_count field in {items:?}"
        );
    }

    #[test]
    fn completes_type_members_after_dot() {
        let code = "enum Opt {\n\tcase none\n\tcase some(Int)\n}\nOpt.\n";
        let analyzed = analyze(code);
        let byte_offset = byte_offset_for(code, "Opt.", 0) + 4;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "none"
                && i.kind == Some(crate::analysis::CompletionItemKind::EnumMember)),
            "expected none case in {items:?}"
        );
        assert!(
            items.iter().any(|i| i.label == "some"
                && i.kind == Some(crate::analysis::CompletionItemKind::EnumMember)),
            "expected some case in {items:?}"
        );
    }

    #[test]
    fn completes_missing_conformance_requirements_in_extend_body() {
        let code = "protocol Foo {\n\tassociated Item\n\tfunc foo() -> Int\n\tfunc bar(value: Int) -> Bool\n}\nstruct Thing {}\nextend Thing: Foo {\n\tfunc foo() -> Int { 1 }\n\t\n}\n";
        let analyzed = analyze(code);
        let byte_offset = code.rfind("\t\n}").expect("blank line") as u32 + 1;
        let completion = completion(&analyzed);
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "bar"
                && i.kind == Some(crate::analysis::CompletionItemKind::Method)
                && i.insert_text.as_deref().is_some_and(|text| text
                    .contains("func bar(value: Int) -> Bool")
                    && text.contains("$0"))),
            "expected bar requirement in {items:?}"
        );
        assert!(
            items
                .iter()
                .any(|i| i.label == "Item"
                    && i.insert_text.as_deref() == Some("typealias Item = $0")),
            "expected Item associated type in {items:?}"
        );
        assert!(
            !items.iter().any(|i| i.label == "foo"
                && i.insert_text
                    .as_deref()
                    .is_some_and(|text| text.contains("func foo"))),
            "implemented requirement should not be offered: {items:?}"
        );
    }
}

#[cfg(test)]
mod scratch_tests {
    #[test]
    #[ignore = "debugging scaffold: dumps completion internals and panics"]
    fn scratch_dump_incomplete_member() {
        let with_tail = "pub func generate(code: String) -> [String] {\n\tlet parsed = code\n\tparsed.\n\n\t[]\n}\n";
        let without_tail = "pub func generate(code: String) -> [String] {\n\tlet parsed = code\n\tparsed.\n}\n";
        for (label, code) in [("with_tail", with_tail), ("without_tail", without_tail)] {
            let analyzed = super::tests::analyze(code);
            let dot = code.find("parsed.").unwrap() as u32 + 6;
            let items = super::complete(code, &super::CompletionAnalysis {
                ast: &analyzed.ast,
                all_asts: None,
                resolved_names: &analyzed.resolved_names,
                types: &analyzed.types,
            }, dot + 1);
            eprintln!("== {label}: {} items: {:?}", items.len(), items.iter().map(|i| i.label.clone()).collect::<Vec<_>>());
            eprintln!("{:#?}", analyzed.ast.roots);
        }
        panic!("dump");
    }
}
