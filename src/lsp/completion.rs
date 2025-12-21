use async_lsp::lsp_types::{CompletionItem, CompletionItemKind};

use crate::analysis::{CompletionItem as AnalysisCompletionItem, CompletionItemKind as AnalysisKind};

pub fn to_lsp_items(items: Vec<AnalysisCompletionItem>) -> Vec<CompletionItem> {
    items
        .into_iter()
        .map(|item| CompletionItem {
            label: item.label,
            kind: item.kind.map(kind_to_lsp),
            detail: item.detail,
            ..Default::default()
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
    }
}
