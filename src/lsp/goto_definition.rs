use async_lsp::lsp_types::{Location, Range, Url};

use crate::analysis::workspace::Workspace as AnalysisWorkspace;

use super::server::{byte_span_to_range_utf16, document_id_for_uri, url_from_document_id};

/// The analysis definition lookup as an LSP location: the target
/// document's URL plus its byte range as UTF-16 positions. The target's
/// text can live in either workspace or — for package imports — in an
/// embedded stdlib module outside both.
pub fn goto_definition(
    module: &AnalysisWorkspace,
    core: Option<&AnalysisWorkspace>,
    uri: &Url,
    byte_offset: u32,
) -> Option<Location> {
    let document_id = document_id_for_uri(uri);
    let location = crate::analysis::goto_definition(module, core, &document_id, byte_offset)?;
    let target_uri = url_from_document_id(&location.document_id)?;

    if location.range.start == 0 && location.range.end == 0 {
        return Some(Location {
            uri: target_uri,
            range: Range::default(),
        });
    }

    let text = [Some(module), core]
        .into_iter()
        .flatten()
        .find_map(|workspace| {
            let file_id = workspace.document_to_file_id.get(&location.document_id)?;
            workspace.texts.get(file_id.0 as usize).cloned()
        })
        .or_else(|| module.stdlib_document_text(&location.document_id))?;
    let range = byte_span_to_range_utf16(&text, location.range.start, location.range.end)?;

    Some(Location {
        uri: target_uri,
        range,
    })
}
