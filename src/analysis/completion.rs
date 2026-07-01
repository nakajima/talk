use rustc_hash::FxHashMap;

use crate::analysis::workspace::Workspace;
use crate::analysis::{CompletionItem, CompletionItemKind, DocumentId, node_ids_at_offset};
use crate::{
    ast::{AST, NameResolved},
    name_resolution::{
        name_resolver::{ResolvedNames, Scope},
        symbol::Symbol,
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        expr::{Expr, ExprKind},
        incomplete_expr::IncompleteExpr,
    },
    types::{
        TypeOutput,
        catalog::{Requirement, TypeCatalog},
        ty::{EffTail, RowTail, Ty},
    },
};

pub struct CompletionAnalysis<'a> {
    pub ast: &'a AST<NameResolved>,
    pub resolved_names: &'a ResolvedNames,
    pub types: &'a TypeOutput,
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
        resolved_names: &workspace.resolved_names,
        types: &workspace.types,
    };

    complete(text, &completion, byte_offset)
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
        })
        .collect();

    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn member_completions(analysis: &CompletionAnalysis<'_>, dot_offset: u32) -> Vec<CompletionItem> {
    let Some(receiver) = member_completion_receiver(analysis.ast, dot_offset) else {
        return vec![];
    };
    let mut items = FxHashMap::default();
    if let Some(symbol) = type_receiver_symbol(&receiver) {
        add_type_member_items(analysis.types, symbol, &mut items);
    } else if let Some(receiver_ty) = analysis.types.node_types.get(&receiver.id) {
        add_member_items_for_ty(analysis.types, receiver_ty, &mut items);
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
    let ExprKind::Constructor(name) = &receiver.kind else {
        return None;
    };
    name.symbol().ok()
}

fn add_member_items_for_ty(
    types: &TypeOutput,
    receiver_ty: &Ty,
    items: &mut FxHashMap<String, CompletionItem>,
) {
    match member_lookup_ty(receiver_ty) {
        Ty::Nominal(symbol, args) => {
            add_nominal_member_items(types, *symbol, args, receiver_ty, items);
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
            add_protocol_requirement_items(types, *protocol, receiver_ty, items);
        }
        Ty::Param(param) => {
            if let Some(bounds) = types.catalog.param_bounds.get(param) {
                for protocol in bounds {
                    add_protocol_requirement_items(types, *protocol, receiver_ty, items);
                }
            }
        }
        Ty::Proj(_, _, assoc_symbol) => {
            if let Some(bounds) = types.catalog.param_bounds.get(assoc_symbol) {
                for protocol in bounds {
                    add_protocol_requirement_items(types, *protocol, receiver_ty, items);
                }
            }
        }
        Ty::Borrow(..) | Ty::Func(..) | Ty::Tuple(_) | Ty::Var(_) | Ty::Error => {}
    }
}

fn member_lookup_ty(mut ty: &Ty) -> &Ty {
    while let Ty::Borrow(_, inner) = ty {
        ty = inner;
    }
    ty
}

fn add_nominal_member_items(
    types: &TypeOutput,
    symbol: Symbol,
    args: &[Ty],
    receiver_ty: &Ty,
    items: &mut FxHashMap<String, CompletionItem>,
) {
    if let Some(info) = types.catalog.structs.get(&symbol) {
        let substitution = param_subst(&info.params, args);
        for (label, (_, field_ty)) in &info.fields {
            let ty = substitute_ty(field_ty, &substitution);
            add_member_item(
                items,
                label.clone(),
                CompletionItemKind::Field,
                Some(ty.render_mono()),
            );
        }
        for (label, method) in &info.methods {
            add_symbol_member_item(
                types,
                label,
                *method,
                &info.params,
                args,
                CompletionItemKind::Method,
                true,
                items,
            );
        }
    }

    if let Some(info) = types.catalog.enums.get(&symbol) {
        for (label, method) in &info.methods {
            add_symbol_member_item(
                types,
                label,
                *method,
                &info.params,
                args,
                CompletionItemKind::Method,
                true,
                items,
            );
        }
    }

    if let Some(protocols) = types.catalog.conformances_by_head.get(&symbol) {
        for protocol in protocols {
            add_protocol_requirement_items(types, *protocol, receiver_ty, items);
        }
    }

    let is_derivable_head =
        types.catalog.structs.contains_key(&symbol) || types.catalog.enums.contains_key(&symbol);
    if is_derivable_head {
        for protocol in &types.catalog.derivable {
            add_protocol_requirement_items(types, *protocol, receiver_ty, items);
        }
    }

    if let Some(members) = types.catalog.extend_members.get(&symbol) {
        for (label, inherent) in members {
            let mut substitution = FxHashMap::default();
            for (pattern, actual) in inherent.self_args.iter().zip(args) {
                crate::types::solve::bind_param_pattern(pattern, actual, &mut substitution);
            }
            let ty = substitute_ty(&inherent.sig, &substitution);
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
        for (label, method) in &info.statics {
            add_symbol_member_item(
                types,
                label,
                *method,
                &info.params,
                &[],
                CompletionItemKind::Method,
                false,
                items,
            );
        }
    }

    if types.catalog.protocols.contains_key(&symbol) {
        for (_, label, requirement) in types.catalog.requirements_for_conformance(symbol) {
            add_member_item(
                items,
                label,
                CompletionItemKind::Method,
                Some(requirement.sig.render_mono()),
            );
        }
    }
}

fn add_symbol_member_item(
    types: &TypeOutput,
    label: &str,
    symbol: Symbol,
    owner_params: &[Symbol],
    owner_args: &[Ty],
    kind: CompletionItemKind,
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
    add_member_item(items, label.to_string(), kind, detail);
}

fn add_protocol_requirement_items(
    types: &TypeOutput,
    protocol: Symbol,
    receiver_ty: &Ty,
    items: &mut FxHashMap<String, CompletionItem>,
) {
    for (owner, label, requirement) in types.catalog.requirements_for_conformance(protocol) {
        add_member_item(
            items,
            label,
            CompletionItemKind::Method,
            requirement_detail(&types.catalog, owner, &requirement, receiver_ty),
        );
    }
}

fn requirement_detail(
    catalog: &TypeCatalog,
    owner: Symbol,
    requirement: &Requirement,
    receiver_ty: &Ty,
) -> Option<String> {
    let lookup_ty = member_lookup_ty(receiver_ty).clone();
    let mut substitution = FxHashMap::default();
    substitution.insert(owner, lookup_ty.clone());
    for (_, assoc) in catalog.associated_types_in(owner) {
        let binding = associated_binding(&lookup_ty, assoc)
            .unwrap_or_else(|| Ty::Proj(Box::new(lookup_ty.clone()), owner, assoc));
        substitution.insert(assoc, binding);
    }
    let ty = substitute_ty(&requirement.sig, &substitution);
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

fn param_subst(params: &[Symbol], args: &[Ty]) -> FxHashMap<Symbol, Ty> {
    params.iter().copied().zip(args.iter().cloned()).collect()
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
    });
}

fn visible_symbols(
    analysis: &CompletionAnalysis<'_>,
    byte_offset: u32,
) -> FxHashMap<String, Symbol> {
    let root_id = NodeID(FileID(0), 0);

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
    let mut current_id: Option<NodeID> = best.map(|s| s.node_id).or(Some(root_id));

    while let Some(id) = current_id {
        let Some(scope) = analysis.resolved_names.scopes.get(&id) else {
            break;
        };

        for (name, sym) in scope.types.iter().chain(scope.values.iter()) {
            result.entry(name.clone()).or_insert(*sym);
        }

        current_id = scope.parent_id;
    }

    result
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

    struct Analyzed {
        ast: AST<NameResolved>,
        resolved_names: ResolvedNames,
        types: TypeOutput,
    }

    fn analyze(code: &str) -> Analyzed {
        let source = Source::in_memory(PathBuf::from("test.tlk"), code.to_string());
        let driver = Driver::new_bare(
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
        Analyzed {
            ast,
            resolved_names: typed.phase.resolved_names,
            types: typed.phase.types,
        }
    }

    fn completion(analyzed: &Analyzed) -> CompletionAnalysis<'_> {
        CompletionAnalysis {
            ast: &analyzed.ast,
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
}
