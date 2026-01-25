use async_lsp::lsp_types::{TextEdit, Url, WorkspaceEdit};

use crate::analysis::workspace::Workspace as AnalysisWorkspace;
use crate::compiling::module::ModuleId;
use crate::lexer::Lexer;
use crate::name_resolution::symbol::{EffectId, Symbol};
use crate::token_kind::TokenKind;

use super::server::{byte_span_to_range_utf16, document_id_for_uri, url_from_document_id};

fn is_valid_identifier(name: &str) -> bool {
    let mut lexer = Lexer::new(name);
    let Ok(token) = lexer.next() else {
        return false;
    };
    if !matches!(token.kind, TokenKind::Identifier(..)) {
        return false;
    }
    matches!(lexer.next().ok().map(|t| t.kind), Some(TokenKind::EOF))
}

fn is_symbol_renamable(symbol: Symbol) -> bool {
    use crate::name_resolution::symbol::{
        AssociatedTypeId, EnumId, GlobalId, InitializerId, InstanceMethodId, MethodRequirementId,
        PropertyId, ProtocolId, StaticMethodId, StructId, TypeAliasId, VariantId,
    };

    match symbol {
        Symbol::Builtin(..) | Symbol::Main | Symbol::Library | Symbol::Synthesized(..) => false,

        Symbol::Struct(StructId { module_id, .. })
        | Symbol::Enum(EnumId { module_id, .. })
        | Symbol::TypeAlias(TypeAliasId { module_id, .. })
        | Symbol::Global(GlobalId { module_id, .. })
        | Symbol::Property(PropertyId { module_id, .. })
        | Symbol::InstanceMethod(InstanceMethodId { module_id, .. })
        | Symbol::Initializer(InitializerId { module_id, .. })
        | Symbol::StaticMethod(StaticMethodId { module_id, .. })
        | Symbol::Variant(VariantId { module_id, .. })
        | Symbol::Protocol(ProtocolId { module_id, .. })
        | Symbol::AssociatedType(AssociatedTypeId { module_id, .. })
        | Symbol::Effect(EffectId { module_id, .. })
        | Symbol::MethodRequirement(MethodRequirementId { module_id, .. }) => {
            module_id == ModuleId::Current
        }

        Symbol::TypeParameter(..)
        | Symbol::DeclaredLocal(..)
        | Symbol::PatternBindLocal(..)
        | Symbol::ParamLocal(..) => true,
    }
}

pub fn rename_at(
    module: &AnalysisWorkspace,
    uri: &Url,
    byte_offset: u32,
    new_name: &str,
) -> Option<WorkspaceEdit> {
    if !is_valid_identifier(new_name) {
        return None;
    }

    let symbol = rename_symbol_at_offset(module, uri, byte_offset)?;
    if !is_symbol_renamable(symbol) {
        return None;
    }

    // Get all spans for this symbol from the index
    let spans = module
        .resolved_names
        .symbol_to_spans
        .get(&symbol)
        .cloned()
        .unwrap_or_default();

    let mut changes: std::collections::HashMap<Url, Vec<TextEdit>> = Default::default();

    for (file_id, start, end) in spans {
        let Some(doc_id) = module.file_id_to_document.get(file_id.0 as usize) else {
            continue;
        };
        let Some(file_uri) = url_from_document_id(doc_id) else {
            continue;
        };
        let Some(text) = module.texts.get(file_id.0 as usize) else {
            continue;
        };
        let Some(range) = byte_span_to_range_utf16(text, start, end) else {
            continue;
        };

        changes
            .entry(file_uri)
            .or_default()
            .push(TextEdit::new(range, new_name.to_string()));
    }

    // Sort edits by position
    for edits in changes.values_mut() {
        edits.sort_by_key(|edit| (edit.range.start.line, edit.range.start.character));
    }

    if changes.is_empty() {
        return None;
    }

    Some(WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    })
}

fn rename_symbol_at_offset(
    module: &AnalysisWorkspace,
    uri: &Url,
    byte_offset: u32,
) -> Option<Symbol> {
    let document_id = document_id_for_uri(uri);
    let file_id = *module.document_to_file_id.get(&document_id)?;
    let (symbol, ..) = module.resolved_names.symbol_at_offset(file_id, byte_offset)?;
    Some(symbol)
}
