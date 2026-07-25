use async_lsp::lsp_types::{CompletionItem, CompletionItemKind, InsertTextFormat};

use crate::analysis::{
    CompletionItem as AnalysisCompletionItem, CompletionItemKind as AnalysisKind,
};

pub fn to_lsp_items(
    items: Vec<AnalysisCompletionItem>,
    text: &str,
    roots: &[crate::node::Node],
) -> Vec<CompletionItem> {
    items
        .into_iter()
        .filter_map(|item| {
            let additional_text_edits = match item.import_from.as_ref() {
                Some(module_path) => {
                    let import_statement = format!("use {module_path}::{{ {} }}", item.label);
                    let edit =
                        super::code_actions::auto_import_edit(text, roots, &import_statement)?;
                    Some(vec![edit])
                }
                None => None,
            };
            Some(CompletionItem {
                label: item.label,
                kind: item.kind.map(kind_to_lsp),
                detail: item.detail,
                sort_text: item.sort_text,
                insert_text: item.insert_text,
                insert_text_format: item
                    .insert_text_is_snippet
                    .then_some(InsertTextFormat::SNIPPET),
                additional_text_edits,
                ..Default::default()
            })
        })
        .collect()
}

fn kind_to_lsp(kind: AnalysisKind) -> CompletionItemKind {
    match kind {
        AnalysisKind::Struct => CompletionItemKind::STRUCT,
        AnalysisKind::Enum => CompletionItemKind::ENUM,
        AnalysisKind::Interface => CompletionItemKind::INTERFACE,
        AnalysisKind::Class => CompletionItemKind::CLASS,
        AnalysisKind::TypeParameter => CompletionItemKind::TYPE_PARAMETER,
        AnalysisKind::Variable => CompletionItemKind::VARIABLE,
        AnalysisKind::Field => CompletionItemKind::FIELD,
        AnalysisKind::Method => CompletionItemKind::METHOD,
        AnalysisKind::Constructor => CompletionItemKind::CONSTRUCTOR,
        AnalysisKind::EnumMember => CompletionItemKind::ENUM_MEMBER,
        AnalysisKind::Keyword => CompletionItemKind::KEYWORD,
        AnalysisKind::Module => CompletionItemKind::MODULE,
        AnalysisKind::Effect => CompletionItemKind::EVENT,
    }
}
