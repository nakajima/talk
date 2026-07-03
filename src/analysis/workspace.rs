use rustc_hash::FxHashMap;
use std::path::PathBuf;

use crate::analysis::{Diagnostic, DiagnosticSeverity, DocumentId, DocumentInput, TextRange};
use crate::ast::{AST, NameResolved};
use crate::compiling::driver::{Driver, DriverConfig, Source};
use crate::compiling::module::ModuleId;
use crate::diagnostic::AnyDiagnostic;
use crate::name_resolution::symbol::set_symbol_names;
use crate::node_id::FileID;
use crate::parser_error::ParserError;

#[derive(Clone)]
pub struct Workspace {
    pub versions: FxHashMap<DocumentId, i32>,
    pub file_id_to_document: Vec<DocumentId>,
    pub document_to_file_id: FxHashMap<DocumentId, FileID>,
    pub texts: Vec<String>,
    pub asts: Vec<Option<AST<NameResolved>>>,
    pub resolved_names: crate::name_resolution::name_resolver::ResolvedNames,
    /// The checker's output tables (node types, schemes) — hover reads
    /// them.
    pub types: crate::types::TypeOutput,
    /// Move, borrow, and drop facts from the flow checker (editor product).
    pub flow: crate::flow::FlowFacts,
    pub diagnostics: FxHashMap<DocumentId, Vec<Diagnostic>>,
}

impl Workspace {
    pub fn new(mut docs: Vec<DocumentInput>) -> Option<Self> {
        if docs.is_empty() {
            return None;
        }

        docs.sort_by(|a, b| a.id.cmp(&b.id));
        let typecheck_as_core = Self::should_typecheck_as_core(&docs);
        if typecheck_as_core {
            docs = Self::core_documents_with_overrides(&docs);
        }

        let mut file_id_to_document: Vec<DocumentId> =
            docs.iter().map(|doc| doc.id.clone()).collect();
        let file_count = file_id_to_document.len();
        if file_count == 0 {
            return None;
        }

        let mut document_to_file_id: FxHashMap<DocumentId, FileID> = file_id_to_document
            .iter()
            .enumerate()
            .map(|(i, id)| (id.clone(), FileID(i as u32)))
            .collect();

        let versions: FxHashMap<DocumentId, i32> = docs
            .iter()
            .map(|doc| (doc.id.clone(), doc.version))
            .collect();

        let mut texts: Vec<String> = docs.iter().map(|doc| doc.text.clone()).collect();

        let sources: Vec<Source> = docs
            .iter()
            .map(|doc| Source::in_memory(PathBuf::from(&doc.path), doc.text.clone()))
            .collect();

        let mut config = DriverConfig::new(if typecheck_as_core {
            "Core"
        } else {
            "Workspace"
        })
        .lenient_parsing()
        .preserve_comments(true);
        if typecheck_as_core {
            config.module_id = ModuleId::Core;
        }

        let driver = if typecheck_as_core {
            Driver::new_bare(sources, config)
        } else {
            Driver::new(sources, config)
        };
        let parsed = driver.parse().ok()?;
        let resolved = parsed.resolve_names().ok()?;
        // The editor keeps the source-faithful surface AST (type annotations,
        // imports, identifier spans the HIR strips). Capture it here, before
        // `type_check` consumes the AST into the compile pipeline's HIR.
        let asts_by_source = resolved.phase.asts.clone();
        // Files discovered through imports get FileIDs past the input docs
        // (Driver::parse appends them). Extend the file-id-indexed tables so
        // their ASTs and diagnostics map to documents instead of being
        // silently dropped.
        let mut discovered: Vec<(FileID, &Source)> = asts_by_source
            .iter()
            .map(|(source, ast)| (ast.file_id, source))
            .filter(|(file_id, _)| (file_id.0 as usize) >= file_id_to_document.len())
            .collect();
        discovered.sort_by_key(|(file_id, _)| file_id.0);
        for (file_id, source) in discovered {
            debug_assert_eq!(file_id.0 as usize, file_id_to_document.len());
            let doc_id = source.path().into_owned();
            document_to_file_id.insert(doc_id.clone(), file_id);
            file_id_to_document.push(doc_id);
            texts.push(source.read().unwrap_or_default());
        }
        let typed = resolved.type_check();
        let Driver { phase, .. } = typed;
        let resolved_names = phase.resolved_names;
        let types = phase.types;
        // The flow checker's editor facts: moves, borrows, drops — no
        // second ownership walk.
        let flow = phase.flow;
        let diagnostics_any = phase.diagnostics;

        let _symbol_guard = set_symbol_names(resolved_names.symbol_names.clone());
        let mut asts: Vec<Option<AST<NameResolved>>> = vec![None; file_id_to_document.len()];
        for ast in asts_by_source.values() {
            let idx = ast.file_id.0 as usize;
            if idx < asts.len() {
                asts[idx] = Some(ast.clone());
            }
        }

        let mut diagnostics: FxHashMap<DocumentId, Vec<Diagnostic>> = FxHashMap::default();
        for diagnostic in diagnostics_any.iter() {
            if let Some((doc_id, diagnostic)) =
                diagnostic_for_any(&file_id_to_document, &texts, &asts, diagnostic)
            {
                diagnostics.entry(doc_id).or_default().push(diagnostic);
            }
        }

        for diagnostics in diagnostics.values_mut() {
            diagnostics.sort_by_key(|d| (d.range.start, d.range.end, d.message.clone()));
        }

        Some(Self {
            versions,
            file_id_to_document,
            document_to_file_id,
            texts,
            asts,
            resolved_names,
            types,
            flow,
            diagnostics,
        })
    }

    fn should_typecheck_as_core(docs: &[DocumentInput]) -> bool {
        let Some(first_doc) = docs.first() else {
            return false;
        };
        let first_path = PathBuf::from(&first_doc.path);
        let Some(core_dir) = first_path.parent().map(|path| path.to_path_buf()) else {
            return false;
        };

        if core_dir.file_name().and_then(|name| name.to_str()) != Some("core") {
            return false;
        }

        docs.iter().all(|doc| {
            let path = PathBuf::from(&doc.path);
            let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
                return false;
            };

            path.parent() == Some(core_dir.as_path())
                && crate::compiling::core::CORE_SOURCE_NAMES.contains(&file_name)
                && doc.text.trim_start().starts_with("// no-core")
        })
    }

    fn core_documents_with_overrides(docs: &[DocumentInput]) -> Vec<DocumentInput> {
        let core_dir = docs
            .first()
            .and_then(|doc| {
                PathBuf::from(&doc.path)
                    .parent()
                    .map(|path| path.to_path_buf())
            })
            .unwrap_or_else(|| PathBuf::from("core"));

        crate::compiling::core::core_sources()
            .into_iter()
            .map(|(name, bundled_text)| {
                if let Some(doc) = docs.iter().find(|doc| {
                    PathBuf::from(&doc.path)
                        .file_name()
                        .and_then(|file_name| file_name.to_str())
                        == Some(name)
                }) {
                    return doc.clone();
                }

                let path = core_dir.join(name);
                let text =
                    std::fs::read_to_string(&path).unwrap_or_else(|_| bundled_text.to_string());
                let path = path.to_string_lossy().into_owned();

                DocumentInput {
                    id: path.clone(),
                    path,
                    version: 0,
                    text,
                }
            })
            .collect()
    }

    pub fn core() -> Option<Self> {
        let core_dir = std::env::temp_dir().join("talk-core");
        let _ = std::fs::create_dir_all(&core_dir);

        let core_files: Vec<(PathBuf, &str)> = crate::compiling::core::core_sources()
            .into_iter()
            .map(|(name, content)| {
                let path = core_dir.join(name);
                let _ = std::fs::write(&path, content);
                (path, content)
            })
            .collect();

        let file_id_to_document: Vec<DocumentId> = core_files
            .iter()
            .map(|(path, _)| path.to_string_lossy().into_owned())
            .collect();

        let document_to_file_id: FxHashMap<DocumentId, FileID> = file_id_to_document
            .iter()
            .enumerate()
            .map(|(i, id)| (id.clone(), FileID(i as u32)))
            .collect();

        let texts: Vec<String> = core_files
            .iter()
            .map(|(_, text)| (*text).to_string())
            .collect();
        let sources: Vec<Source> = core_files
            .iter()
            .map(|(path, text)| Source::in_memory(path.clone(), *text))
            .collect();

        let mut config = DriverConfig::new("Core").preserve_comments(true);
        config.module_id = ModuleId::Core;

        let driver = Driver::new_bare(sources, config);
        let resolved = driver.parse().ok()?.resolve_names().ok()?;

        let resolved_names = resolved.phase.resolved_names.clone();

        let mut asts: Vec<Option<AST<NameResolved>>> = vec![None; file_id_to_document.len()];
        for ast in resolved.phase.asts.values() {
            let idx = ast.file_id.0 as usize;
            if idx < asts.len() {
                asts[idx] = Some(ast.clone());
            }
        }

        Some(Self {
            versions: FxHashMap::default(),
            file_id_to_document,
            document_to_file_id,
            texts,
            asts,
            resolved_names,
            // Name resolution only: the core workspace exists for symbol
            // rendering, not hover.
            types: Default::default(),
            flow: Default::default(),
            diagnostics: FxHashMap::default(),
        })
    }

    pub fn document_index(&self, id: &DocumentId) -> Option<usize> {
        self.document_to_file_id.get(id).map(|id| id.0 as usize)
    }

    pub fn text_for(&self, id: &DocumentId) -> Option<&str> {
        let idx = self.document_index(id)?;
        self.texts.get(idx).map(|text| text.as_str())
    }

    pub fn ast_for(&self, id: &DocumentId) -> Option<&AST<NameResolved>> {
        let idx = self.document_index(id)?;
        self.asts.get(idx).and_then(|ast| ast.as_ref())
    }

    pub fn document_id_for_node(&self, id: crate::node_id::NodeID) -> Option<&DocumentId> {
        self.file_id_to_document.get(id.0.0 as usize)
    }

    pub fn range_for_node(
        &self,
        id: crate::node_id::NodeID,
        prefer_identifier: bool,
    ) -> Option<(DocumentId, TextRange)> {
        let file_idx = id.0.0 as usize;
        let doc_id = self.file_id_to_document.get(file_idx)?.clone();
        let ast = self.asts.get(file_idx)?.as_ref()?;
        Some((doc_id, range_for_node(ast, id, prefer_identifier)))
    }
}

fn parser_error_range(text: &str, err: &ParserError) -> TextRange {
    let eof = text.len() as u32;

    match err {
        ParserError::UnexpectedToken {
            token: Some(token), ..
        } => TextRange::new(token.start, token.end),
        ParserError::InfiniteLoop(Some(token))
        | ParserError::ExpectedIdentifier(Some(token))
        | ParserError::ConformanceListNotAllowed {
            token: Some(token), ..
        } => TextRange::new(token.start, token.end),
        ParserError::UnexpectedEndOfInput(..) => TextRange::new(eof, eof),
        _ => TextRange::new(0, 0),
    }
}

fn diagnostic_for_any(
    file_id_to_document: &[DocumentId],
    texts: &[String],
    asts: &[Option<AST<NameResolved>>],
    diagnostic: &AnyDiagnostic,
) -> Option<(DocumentId, Diagnostic)> {
    let (id, message, parse_error, prefer_identifier, severity) = match diagnostic {
        AnyDiagnostic::Parsing(diagnostic) => (
            diagnostic.id,
            diagnostic.kind.to_string(),
            Some(&diagnostic.kind),
            false,
            &diagnostic.severity,
        ),
        AnyDiagnostic::NameResolution(diagnostic) => (
            diagnostic.id,
            diagnostic.kind.to_string(),
            None,
            true,
            &diagnostic.severity,
        ),
        AnyDiagnostic::Types(diagnostic) => (
            diagnostic.id,
            diagnostic.kind.to_string(),
            None,
            false,
            &diagnostic.severity,
        ),
        AnyDiagnostic::Ownership(diagnostic) => (
            diagnostic.id,
            diagnostic.kind.to_string(),
            None,
            false,
            &diagnostic.severity,
        ),
    };
    let severity = match severity {
        crate::diagnostic::Severity::Error => DiagnosticSeverity::Error,
        crate::diagnostic::Severity::Warn => DiagnosticSeverity::Warning,
    };

    let file_idx = id.0.0 as usize;
    let doc_id = file_id_to_document.get(file_idx)?.clone();

    let range = if let Some(err) = parse_error {
        texts
            .get(file_idx)
            .map(|text| parser_error_range(text, err))
            .unwrap_or_else(|| TextRange::new(0, 0))
    } else {
        match (
            texts.get(file_idx),
            asts.get(file_idx).and_then(|a| a.as_ref()),
        ) {
            (Some(_text), Some(ast)) => range_for_node(ast, id, prefer_identifier),
            _ => TextRange::new(0, 0),
        }
    };

    Some((
        doc_id,
        Diagnostic {
            range,
            severity,
            message,
        },
    ))
}

fn range_for_node(
    ast: &AST<NameResolved>,
    id: crate::node_id::NodeID,
    prefer_identifier: bool,
) -> TextRange {
    if let Some(meta) = ast.meta.get(&id) {
        let (start, end) = if prefer_identifier {
            meta.identifiers
                .last()
                .map(|t| (t.start, t.end))
                .unwrap_or((meta.start.start, meta.end.end))
        } else {
            (meta.start.start, meta.end.end)
        };

        if start != 0 || end != 0 {
            return TextRange::new(start, end);
        }
    }

    if let Some(node) = ast.find(id) {
        let span = node.span();
        if span.file_id != FileID::SYNTHESIZED {
            return TextRange::new(span.start, span.end);
        }
    }

    TextRange::new(0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_sources_do_not_report_workspace_diagnostics() {
        let docs = crate::compiling::core::core_sources()
            .into_iter()
            .map(|(name, text)| {
                let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                    .join("core")
                    .join(name)
                    .to_string_lossy()
                    .into_owned();

                DocumentInput {
                    id: path.clone(),
                    path,
                    version: 0,
                    text: text.to_string(),
                }
            })
            .collect();

        let workspace = Workspace::new(docs).expect("workspace");
        assert!(
            workspace.diagnostics.is_empty(),
            "expected no core diagnostics, got {:?}",
            workspace.diagnostics
        );
    }

    #[test]
    fn diagnostic_severities_survive_into_the_workspace() {
        // An unreachable match arm is a warning; a non-exhaustive match is
        // an error. `talk check`'s exit code and the editor's squiggle
        // color both key on this mapping.
        let text = "enum Color {\n\tcase red, green\n}\nlet c = Color.red\nmatch c {\n\t_ -> 1,\n\tColor.red -> 2\n}\nmatch c {\n\tColor.red -> 1\n}\n";
        let docs = vec![DocumentInput {
            id: "test.tlk".to_string(),
            path: "test.tlk".to_string(),
            version: 0,
            text: text.to_string(),
        }];
        let workspace = Workspace::new(docs).expect("workspace");
        let diagnostics = workspace
            .diagnostics
            .get("test.tlk")
            .expect("diagnostics for the document");
        let severities: Vec<(DiagnosticSeverity, &str)> = diagnostics
            .iter()
            .map(|d| (d.severity, d.message.as_str()))
            .collect();
        assert!(
            severities
                .iter()
                .any(|(s, m)| *s == DiagnosticSeverity::Warning && m.contains("never runs")),
            "expected an unreachable-arm warning, got {severities:?}"
        );
        assert!(
            severities
                .iter()
                .any(|(s, m)| *s == DiagnosticSeverity::Error && m.contains(".green")),
            "expected a non-exhaustive error naming .green, got {severities:?}"
        );
    }

    #[test]
    fn ownership_diagnostics_survive_into_the_workspace() {
        let text = "let s = \"a\" + \"b\"\nlet t = s\ns.length\n";
        let docs = vec![DocumentInput {
            id: "test.tlk".to_string(),
            path: "test.tlk".to_string(),
            version: 0,
            text: text.to_string(),
        }];
        let workspace = Workspace::new(docs).expect("workspace");
        let diagnostics = workspace
            .diagnostics
            .get("test.tlk")
            .cloned()
            .unwrap_or_default();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("Use of moved value")),
            "expected ownership diagnostic, got {diagnostics:?}"
        );
    }

    #[test]
    fn import_discovered_files_report_diagnostics() {
        // A file pulled in by `use ... from` gets a FileID past the input
        // docs; its diagnostics must still reach the workspace instead of
        // being silently dropped (`talk check` exit code depends on this).
        let dir = std::env::temp_dir().join("talk-import-diagnostics");
        std::fs::create_dir_all(&dir).expect("temp dir");
        let lib_path = dir.join("lib.tlk");
        let main_path = dir.join("main.tlk");
        std::fs::write(&lib_path, "public let broken: Int = \"not an int\"\n").expect("lib");
        let main_text = "use { broken } from ./lib.tlk\nprint(broken)\n";
        std::fs::write(&main_path, main_text).expect("main");

        let main_id = main_path.to_string_lossy().into_owned();
        let docs = vec![DocumentInput {
            id: main_id.clone(),
            path: main_id.clone(),
            version: 0,
            text: main_text.to_string(),
        }];
        let workspace = Workspace::new(docs).expect("workspace");
        let lib_diagnostics: Vec<_> = workspace
            .diagnostics
            .iter()
            .filter(|(doc, _)| doc.contains("lib.tlk"))
            .flat_map(|(_, diagnostics)| diagnostics.iter())
            .collect();
        assert!(
            lib_diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("mismatch")),
            "expected the imported file's type error to surface, got {:?}",
            workspace.diagnostics
        );
    }

    #[test]
    fn ownership_diagnostics_survive_unrelated_file_errors() {
        let bad_text = "func bad() -> Int {\n\ttrue\n}\n";
        let copy_text = "let thing = \"Pat\"\nlet a = thing\nlet b = thing\nprint(a)\nprint(b)\n";
        let docs = vec![
            DocumentInput {
                id: "bad.tlk".to_string(),
                path: "bad.tlk".to_string(),
                version: 0,
                text: bad_text.to_string(),
            },
            DocumentInput {
                id: "copy.tlk".to_string(),
                path: "copy.tlk".to_string(),
                version: 0,
                text: copy_text.to_string(),
            },
        ];
        let workspace = Workspace::new(docs).expect("workspace");
        let bad_diagnostics = workspace
            .diagnostics
            .get("bad.tlk")
            .cloned()
            .unwrap_or_default();
        assert!(
            bad_diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("Type mismatch")),
            "expected type diagnostic in bad.tlk, got {bad_diagnostics:?}"
        );

        let copy_diagnostics = workspace
            .diagnostics
            .get("copy.tlk")
            .cloned()
            .unwrap_or_default();
        assert!(
            copy_diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("Use of moved value")),
            "expected ownership diagnostic in copy.tlk, got {copy_diagnostics:?}"
        );
    }
}
