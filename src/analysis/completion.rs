use rustc_hash::FxHashMap;

use crate::analysis::workspace::Workspace;
use crate::analysis::{CompletionItem, CompletionItemKind, DocumentId};
use crate::{
    ast::{AST, NameResolved},
    name_resolution::{
        name_resolver::{ResolvedNames, Scope},
        symbol::Symbol,
    },
    node_id::{FileID, NodeID},
};

pub struct CompletionAnalysis<'a> {
    pub ast: &'a AST<NameResolved>,
    pub resolved_names: &'a ResolvedNames,
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
    };

    complete(text, &completion, byte_offset)
}

pub fn complete(
    text: &str,
    analysis: &CompletionAnalysis<'_>,
    byte_offset: u32,
) -> Vec<CompletionItem> {
    // Member completion requires type information, which is not available
    // until the type checker is rebuilt. Avoid offering junk scope
    // completions after a dot.
    if member_completion_dot(text, byte_offset).is_some() {
        return vec![];
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
    use crate::analysis::{DocumentInput, Workspace, completion::CompletionAnalysis};

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
        };
        let items = super::complete(code, &completion, byte_offset);
        assert!(
            items.iter().any(|i| i.label == "foo"),
            "expected foo in {items:?}"
        );
    }

    #[test]
    fn no_completions_after_dot() {
        let code = "let foo = 1\nfoo.\n";
        let workspace = analyze(code);
        let byte_offset = byte_offset_for(code, "foo.", 0) + 4;
        let ast = workspace.asts[0].as_ref().expect("ast");
        let completion = CompletionAnalysis {
            ast,
            resolved_names: &workspace.resolved_names,
        };
        let items = super::complete(code, &completion, byte_offset);
        assert!(items.is_empty(), "expected no items, got {items:?}");
    }
}
