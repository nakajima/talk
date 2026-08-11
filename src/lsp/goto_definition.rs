use async_lsp::lsp_types::{Location, Range, Url};
use rustc_hash::FxHashMap;
use std::sync::Arc;

use crate::analysis::workspace::Workspace as AnalysisWorkspace;
use crate::compiling::module::ModuleId;

use super::server::{document_id_for_uri, url_from_document_id};

pub enum LspGoto {
    Found(Location),
    /// The target stdlib module's workspace is not built yet; the
    /// handler kicks an off-loop build and answers empty this once.
    NeedsModule(ModuleId),
    NotFound,
}

/// The analysis definition lookup as an LSP location: the target
/// document's URL plus its byte range as UTF-16 positions. The text
/// comes back with the lookup itself — the target can live in an
/// embedded stdlib module outside both workspaces, and positions must
/// convert against exactly the text the lookup resolved in.
pub fn goto_definition(
    module: &AnalysisWorkspace,
    core: Option<&AnalysisWorkspace>,
    stdlib_modules: &FxHashMap<ModuleId, Arc<AnalysisWorkspace>>,
    uri: &Url,
    byte_offset: u32,
) -> LspGoto {
    let document_id = document_id_for_uri(uri);
    let result = crate::analysis::goto_definition_with(
        module,
        core,
        &|module_id| {
            stdlib_modules
                .get(&module_id)
                .map(|workspace| std::borrow::Cow::Borrowed(workspace.as_ref()))
        },
        &document_id,
        byte_offset,
    );
    match result {
        crate::analysis::GotoDefinition::NotFound => LspGoto::NotFound,
        crate::analysis::GotoDefinition::NeedsModule(module_id) => {
            LspGoto::NeedsModule(module_id)
        }
        crate::analysis::GotoDefinition::Found { location, text } => {
            let Some(target_uri) = url_from_document_id(&location.document_id) else {
                return LspGoto::NotFound;
            };
            if location.range.start == 0 && location.range.end == 0 {
                return LspGoto::Found(Location {
                    uri: target_uri,
                    range: Range::default(),
                });
            }
            let Some(range) = super::server::byte_span_to_range_utf16_in(
                text.line_index(),
                text.text(),
                location.range.start,
                location.range.end,
            ) else {
                return LspGoto::NotFound;
            };
            LspGoto::Found(Location {
                uri: target_uri,
                range,
            })
        }
    }
}
