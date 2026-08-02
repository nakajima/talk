use async_lsp::lsp_types::{TextEdit, Url, WorkspaceEdit};

use crate::analysis::workspace::Workspace as AnalysisWorkspace;

use super::server::{byte_span_to_range_utf16, document_id_for_uri, url_from_document_id};

/// The analysis rename as an LSP workspace edit: the same byte-ranged
/// edits re-keyed by document URL with UTF-16 positions.
pub fn rename_at(
    module: &AnalysisWorkspace,
    uri: &Url,
    byte_offset: u32,
    new_name: &str,
) -> Option<WorkspaceEdit> {
    let document_id = document_id_for_uri(uri);
    let edit = crate::analysis::rename_at(module, &document_id, byte_offset, new_name)?;

    let mut changes: std::collections::HashMap<Url, Vec<TextEdit>> = Default::default();
    for document in edit.documents {
        let Some(file_uri) = url_from_document_id(&document.document_id) else {
            continue;
        };
        let Some(file_id) = module.document_to_file_id.get(&document.document_id) else {
            continue;
        };
        let Some(text) = module.texts.get(file_id.0 as usize) else {
            continue;
        };
        let edits: Vec<TextEdit> = document
            .edits
            .into_iter()
            .filter_map(|edit| {
                let range = byte_span_to_range_utf16(text, edit.range.start, edit.range.end)?;
                Some(TextEdit::new(range, edit.replacement))
            })
            .collect();
        if !edits.is_empty() {
            changes.insert(file_uri, edits);
        }
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
