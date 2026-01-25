use async_lsp::lsp_types::{Location, Position, Range, Url};

use crate::analysis::span_contains;
use crate::analysis::workspace::Workspace as AnalysisWorkspace;
use crate::compiling::module::ModuleId;
use crate::name_resolution::symbol::Symbol;

use super::server::{byte_span_to_range_utf16, document_id_for_uri, url_from_document_id};

pub fn goto_definition(
    module: &AnalysisWorkspace,
    core: Option<&AnalysisWorkspace>,
    uri: &Url,
    byte_offset: u32,
) -> Option<Location> {
    let document_id = document_id_for_uri(uri);
    let file_id = *module.document_to_file_id.get(&document_id)?;

    // Handle imports specially (need AST to get import path for file navigation)
    if let Some(ast) = module.asts.get(file_id.0 as usize).and_then(|a| a.as_ref()) {
        // Find the node at this offset to check for import declarations
        for (node_id, meta) in ast.meta.iter() {
            if meta.start.start <= byte_offset && byte_offset <= meta.end.end {
                if let Some(crate::node::Node::Decl(ref decl)) = ast.find(*node_id) {
                    if let Some(location) = goto_definition_from_import(module, uri, decl, byte_offset) {
                        return Some(location);
                    }
                }
            }
        }
    }

    // Use symbol index for everything else
    let (symbol, ..) = module.resolved_names.symbol_at_offset(file_id, byte_offset)?;
    definition_location_for_symbol(module, core, symbol)
}

/// Handle go-to-definition for import declarations.
/// Returns a location if the cursor is on an imported symbol or the import path.
fn goto_definition_from_import(
    module: &AnalysisWorkspace,
    uri: &Url,
    decl: &crate::node_kinds::decl::Decl,
    byte_offset: u32,
) -> Option<Location> {
    use crate::node_kinds::decl::{DeclKind, ImportedSymbols};

    let DeclKind::Import(import) = &decl.kind else {
        return None;
    };

    // Check if cursor is on the import path - navigate to the file
    if span_contains(import.path_span, byte_offset) {
        let target_path = resolve_import_path(uri, &import.path)?;
        let target_uri = Url::from_file_path(&target_path).ok()?;
        return Some(Location {
            uri: target_uri,
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 0,
                    character: 0,
                },
            },
        });
    }

    // Check if cursor is on an imported symbol - navigate to its definition
    if let ImportedSymbols::Named(symbols) = &import.symbols {
        for imported in symbols {
            if span_contains(imported.span, byte_offset) {
                // Find the target file and look up the symbol there
                let target_path = resolve_import_path(uri, &import.path)?;
                let target_uri = Url::from_file_path(&target_path).ok()?;
                let target_doc_id = document_id_for_uri(&target_uri);
                let target_file_id = *module.document_to_file_id.get(&target_doc_id)?;
                let target_scope_id = crate::node_id::NodeID(target_file_id, 0);

                // Look up the symbol in the target file's scope
                let target_scope = module.resolved_names.scopes.get(&target_scope_id)?;
                let symbol = target_scope
                    .types
                    .get(&imported.name)
                    .or_else(|| target_scope.values.get(&imported.name))?;

                return definition_location_in_module(module, *symbol);
            }
        }
    }

    None
}

/// Resolve an import path relative to the importing file's URI.
fn resolve_import_path(uri: &Url, import_path: &crate::node_kinds::decl::ImportPath) -> Option<std::path::PathBuf> {
    use crate::node_kinds::decl::ImportPath;

    match import_path {
        ImportPath::Relative(rel_path) => {
            let source_path = uri.to_file_path().ok()?;
            let source_dir = source_path.parent()?;
            // Strip leading "./" if present
            let clean_rel = rel_path.strip_prefix("./").unwrap_or(rel_path);
            Some(source_dir.join(clean_rel))
        }
        ImportPath::Package(_) => {
            // Package imports not yet supported for go-to-definition
            None
        }
    }
}

pub(crate) fn definition_location_for_symbol(
    module: &AnalysisWorkspace,
    core: Option<&AnalysisWorkspace>,
    symbol: Symbol,
) -> Option<Location> {
    if let Some(module_id) = symbol.external_module_id() {
        if module_id == ModuleId::Core {
            let core = core?;
            return definition_location_in_module(core, symbol);
        }
        return None;
    }

    definition_location_in_module(module, symbol)
}

pub(crate) fn definition_location_in_module(module: &AnalysisWorkspace, symbol: Symbol) -> Option<Location> {
    let def_node = *module.resolved_names.symbols_to_node.get(&symbol)?;
    let file_id = def_node.0;
    let doc_id = module.file_id_to_document.get(file_id.0 as usize)?;
    let uri = url_from_document_id(doc_id)?;
    let text = module.texts.get(file_id.0 as usize)?;
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|a| a.as_ref())?;

    let meta = ast.meta.get(&def_node)?;
    let (start, end) = match meta.identifiers.first() {
        Some(tok) => (tok.start, tok.end),
        None => (meta.start.start, meta.end.end),
    };
    let range = byte_span_to_range_utf16(text, start, end)?;

    Some(Location { uri, range })
}
