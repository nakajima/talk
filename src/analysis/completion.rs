use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::{CompletionItem, CompletionItemKind, DocumentId};
use crate::analysis::workspace::Workspace;
use crate::{
    ast::{AST, NameResolved},
    label::Label,
    name_resolution::{
        name_resolver::{ResolvedNames, Scope},
        symbol::Symbol,
    },
    node_id::{FileID, NodeID},
    node_kinds::expr::ExprKind,
    types::{
        format::{SymbolNames, TypeFormatter},
        row::Row,
        type_session::Types,
        ty::Ty,
    },
};

pub struct CompletionAnalysis<'a> {
    pub ast: &'a AST<NameResolved>,
    pub resolved_names: &'a ResolvedNames,
    pub types: Option<&'a Types>,
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
        types: workspace.types.as_ref(),
    };

    complete(text, &completion, byte_offset)
}

pub fn complete(
    text: &str,
    analysis: &CompletionAnalysis<'_>,
    byte_offset: u32,
) -> Vec<CompletionItem> {
    if let Some(dot_pos) = member_completion_dot(text, byte_offset) {
        return member_completions(text, analysis, dot_pos);
    }

    scope_completions(analysis, byte_offset)
}

fn type_formatter<'a>(analysis: &'a CompletionAnalysis<'a>) -> TypeFormatter<'a> {
    TypeFormatter::new(SymbolNames::single(&analysis.resolved_names.symbol_names))
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

fn member_completions(
    text: &str,
    analysis: &CompletionAnalysis<'_>,
    dot_pos: u32,
) -> Vec<CompletionItem> {
    let Some(types) = analysis.types else {
        return vec![];
    };
    let formatter = type_formatter(analysis);

    let bytes = text.as_bytes();
    let mut receiver_end = (dot_pos as usize).min(bytes.len());
    while receiver_end > 0 && matches!(bytes[receiver_end - 1], b' ' | b'\t' | b'\r') {
        receiver_end -= 1;
    }
    let Some(receiver_probe) = receiver_end.checked_sub(1) else {
        return vec![];
    };

    let Some(receiver_node_id) = smallest_node_at_offset(analysis, receiver_probe as u32) else {
        return vec![];
    };

    let Some(receiver_node) = analysis.ast.find(receiver_node_id) else {
        return vec![];
    };

    let crate::node::Node::Expr(receiver_expr) = receiver_node else {
        return vec![];
    };

    match &receiver_expr.kind {
        ExprKind::Constructor(name) => {
            let Ok(receiver_sym) = name.symbol() else {
                return vec![];
            };

            let members = static_member_symbols(types, receiver_sym);
            let receiver_type = types
                .catalog
                .nominals
                .get(&receiver_sym)
                .map(|_| {
                    formatter.format_ty(
                        &Ty::Nominal {
                            symbol: receiver_sym,
                            type_args: vec![],
                        },
                    )
                })
                .unwrap_or_else(|| receiver_sym.to_string());
            let variant_values = types
                .catalog
                .nominals
                .get(&receiver_sym)
                .map(|nominal| nominal.substituted_variant_values(&[]));

            symbol_member_items(
                &formatter,
                types,
                members.into_iter(),
                None,
                None,
                variant_values.as_ref(),
                Some(&receiver_type),
            )
        }
        _ => {
            let Some(entry) = types.get(&receiver_expr.id) else {
                return vec![];
            };
            match entry.as_mono_ty() {
                Ty::Nominal { symbol, type_args } => {
                    let subs = types
                        .catalog
                        .nominals
                        .get(symbol)
                        .map(|nominal| nominal.substitutions(type_args));
                    let property_types = types
                        .catalog
                        .nominals
                        .get(symbol)
                        .map(|nominal| nominal.substitute_properties(type_args));
                    let variant_values = types
                        .catalog
                        .nominals
                        .get(symbol)
                        .map(|nominal| nominal.substituted_variant_values(type_args));
                    let receiver_type = formatter.format_ty(&Ty::Nominal {
                        symbol: *symbol,
                        type_args: type_args.clone(),
                    });

                    let members = instance_member_symbols(types, *symbol);
                    symbol_member_items(
                        &formatter,
                        types,
                        members.into_iter(),
                        subs.as_ref(),
                        property_types.as_ref(),
                        variant_values.as_ref(),
                        Some(&receiver_type),
                    )
                }
                Ty::Record(.., row) => record_member_items(&formatter, row),
                _ => vec![],
            }
        }
    }
}

fn static_member_symbols(
    types: &crate::types::type_session::Types,
    receiver: Symbol,
) -> Vec<(Label, Symbol)> {
    let mut seen = FxHashSet::<Label>::default();
    let mut result: Vec<(Label, Symbol)> = vec![];

    for map in [
        types.catalog.static_methods.get(&receiver),
        types.catalog.variants.get(&receiver),
        types.catalog.instance_methods.get(&receiver),
        types.catalog.method_requirements.get(&receiver),
    ] {
        let Some(map) = map else { continue };
        for (label, sym) in map {
            if seen.insert(label.clone()) {
                result.push((label.clone(), *sym));
            }
        }
    }

    result.sort_by(|(a, _), (b, _)| a.to_string().cmp(&b.to_string()));
    result
}

fn instance_member_symbols(
    types: &crate::types::type_session::Types,
    receiver: Symbol,
) -> Vec<(Label, Symbol)> {
    let mut seen = FxHashSet::<Label>::default();
    let mut result: Vec<(Label, Symbol)> = vec![];

    for map in [
        types.catalog.properties.get(&receiver),
        types.catalog.instance_methods.get(&receiver),
        types.catalog.variants.get(&receiver),
        types.catalog.method_requirements.get(&receiver),
    ] {
        let Some(map) = map else { continue };
        for (label, sym) in map {
            if seen.insert(label.clone()) {
                result.push((label.clone(), *sym));
            }
        }
    }

    result.sort_by(|(a, _), (b, _)| a.to_string().cmp(&b.to_string()));
    result
}

fn scope_completions(analysis: &CompletionAnalysis<'_>, byte_offset: u32) -> Vec<CompletionItem> {
    let symbols = visible_symbols(analysis, byte_offset);
    let types = analysis.types;
    let formatter = type_formatter(analysis);
    let mut items: Vec<CompletionItem> = symbols
        .into_iter()
        .map(|(name, sym)| {
            let detail = types
                .and_then(|types| types.get_symbol(&sym))
                .map(|entry| format_type_entry(&formatter, entry.as_mono_ty(), None));
            CompletionItem {
                label: name,
                kind: completion_kind(sym),
                detail,
            }
        })
        .collect();

    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
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

fn symbol_member_items(
    formatter: &TypeFormatter<'_>,
    types: &crate::types::type_session::Types,
    members: impl Iterator<Item = (Label, Symbol)>,
    receiver_substitutions: Option<&FxHashMap<Ty, Ty>>,
    property_types: Option<&IndexMap<Label, Ty>>,
    variant_values: Option<&IndexMap<Label, Vec<Ty>>>,
    variant_receiver: Option<&str>,
) -> Vec<CompletionItem> {
    let mut items: Vec<CompletionItem> = members
        .map(|(label, sym)| {
            let detail = match sym {
                Symbol::Property(..) => property_types
                    .and_then(|props| props.get(&label))
                    .map(|ty| formatter.format_ty(ty)),
                Symbol::Variant(..) => variant_values
                    .and_then(|variants| variants.get(&label))
                    .and_then(|payload| {
                        let receiver = variant_receiver?;
                        let payload = payload
                            .iter()
                            .map(|t| formatter.format_ty(t))
                            .collect::<Vec<_>>()
                            .join(", ");
                        Some(format!("({payload}) -> {receiver}"))
                    }),
                _ => types.get_symbol(&sym).map(|entry| {
                    format_type_entry(formatter, entry.as_mono_ty(), receiver_substitutions)
                }),
            };
            CompletionItem {
                label: label.to_string(),
                kind: completion_kind(sym),
                detail,
            }
        })
        .collect();

    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn record_member_items(formatter: &TypeFormatter<'_>, row: &Row) -> Vec<CompletionItem> {
    let fields = record_fields(row);
    let mut items: Vec<CompletionItem> = fields
        .into_iter()
        .map(|(label, ty)| CompletionItem {
            label: label.to_string(),
            kind: Some(CompletionItemKind::Field),
            detail: Some(formatter.format_ty(&ty)),
        })
        .collect();
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn record_fields(row: &Row) -> Vec<(Label, Ty)> {
    let mut result = vec![];
    let mut seen: FxHashSet<Label> = FxHashSet::default();
    let mut cursor = row;
    loop {
        match cursor {
            Row::Empty(..) | Row::Param(..) => break,
            Row::Extend { row, label, ty } => {
                if seen.insert(label.clone()) {
                    result.push((label.clone(), ty.clone()));
                }
                cursor = row;
            }
        }
    }
    result
}

fn format_type_entry(
    formatter: &TypeFormatter<'_>,
    ty: &Ty,
    substitutions: Option<&FxHashMap<Ty, Ty>>,
) -> String {
    let ty = substitutions
        .map(|subs| substitute_ty(ty, subs))
        .unwrap_or_else(|| ty.clone());
    formatter.format_ty(&ty)
}

fn substitute_ty(ty: &Ty, substitutions: &FxHashMap<Ty, Ty>) -> Ty {
    if let Some(subst) = substitutions.get(ty) {
        return subst.clone();
    }

    match ty {
        Ty::Primitive(..) | Ty::Param(..) => ty.clone(),
        Ty::Constructor { name, params, ret } => Ty::Constructor {
            name: name.clone(),
            params: params
                .iter()
                .map(|p| substitute_ty(p, substitutions))
                .collect(),
            ret: substitute_ty(ret, substitutions).into(),
        },
        Ty::Func(param, ret) => Ty::Func(
            substitute_ty(param, substitutions).into(),
            substitute_ty(ret, substitutions).into(),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .iter()
                .map(|t| substitute_ty(t, substitutions))
                .collect(),
        ),
        Ty::Record(symbol, row) => {
            Ty::Record(*symbol, substitute_row(row, substitutions).into())
        }
        Ty::Nominal { symbol, type_args } => Ty::Nominal {
            symbol: *symbol,
            type_args: type_args
                .iter()
                .map(|t| substitute_ty(t, substitutions))
                .collect(),
        },
    }
}

fn substitute_row(row: &Row, substitutions: &FxHashMap<Ty, Ty>) -> Row {
    match row {
        Row::Empty(kind) => Row::Empty(*kind),
        Row::Param(param) => Row::Param(*param),
        Row::Extend { row, label, ty } => Row::Extend {
            row: substitute_row(row, substitutions).into(),
            label: label.clone(),
            ty: substitute_ty(ty, substitutions),
        },
    }
}

fn smallest_node_at_offset(
    analysis: &CompletionAnalysis<'_>,
    byte_offset: u32,
) -> Option<NodeID> {
    analysis
        .ast
        .meta
        .iter()
        .filter_map(|(id, meta)| {
            let start = meta.start.start;
            let end = meta.end.end;
            if start <= byte_offset && byte_offset <= end {
                Some((*id, end.saturating_sub(start)))
            } else {
                None
            }
        })
        .min_by_key(|(_, len)| *len)
        .map(|(id, _)| id)
}

#[cfg(test)]
mod tests {
    use crate::analysis::{completion::CompletionAnalysis, DocumentInput, Workspace};

    fn analyze(code: &str) -> Workspace {
        let doc = DocumentInput {
            id: "test.tlk".to_string(),
            path: "test.tlk".to_string(),
            version: 0,
            text: code.to_string(),
        };

        Workspace::new(vec![doc]).expect("workspace")
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
        let workspace = analyze(code);
        let byte_offset = byte_offset_for(code, "f", 0);
        let ast = workspace.asts[0].as_ref().expect("ast");
        let completion = CompletionAnalysis {
            ast,
            resolved_names: &workspace.resolved_names,
            types: workspace.types.as_ref(),
        };
        let items = super::complete(code, &completion, byte_offset);
        let foo = items.iter().find(|i| i.label == "foo").expect("items");
        assert_eq!(foo.detail.as_deref(), Some("Int"), "{items:?}");
    }

    #[test]
    fn completes_struct_members_after_dot() {
        let code = r#"
        struct Foo {
            let bar: Int
        }
        let foo = Foo(bar: 1)
        foo.
        foo.bar
        "#;
        let workspace = analyze(code);
        let byte_offset = byte_offset_for(code, "foo.", 0) + 4;
        let ast = workspace.asts[0].as_ref().expect("ast");
        let completion = CompletionAnalysis {
            ast,
            resolved_names: &workspace.resolved_names,
            types: workspace.types.as_ref(),
        };
        let items = super::complete(code, &completion, byte_offset);
        let bar = items.iter().find(|i| i.label == "bar").expect("items");
        assert_eq!(bar.detail.as_deref(), Some("Int"), "{items:?}");
    }

    #[test]
    fn completes_record_members_after_dot() {
        let code = r#"
        let foo = { bar: 1, baz: true }
        foo.
        foo.bar
        "#;
        let workspace = analyze(code);
        let byte_offset = byte_offset_for(code, "foo.", 0) + 4;
        let ast = workspace.asts[0].as_ref().expect("ast");
        let completion = CompletionAnalysis {
            ast,
            resolved_names: &workspace.resolved_names,
            types: workspace.types.as_ref(),
        };
        let items = super::complete(code, &completion, byte_offset);
        let bar = items.iter().find(|i| i.label == "bar").expect("items");
        let baz = items.iter().find(|i| i.label == "baz").expect("items");
        assert_eq!(bar.detail.as_deref(), Some("Int"), "{items:?}");
        assert_eq!(baz.detail.as_deref(), Some("Bool"), "{items:?}");
    }
}
