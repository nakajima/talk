use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    path::{Path, PathBuf},
    rc::Rc,
};

use crate::analysis::{
    Diagnostic, DiagnosticKind, DiagnosticSeverity, DocumentId, DocumentInput, TextRange,
};
use crate::ast::{AST, NameResolved};
use crate::compiling::driver::{CompilationMode, Driver, DriverConfig, Source};
use crate::compiling::module::{ModuleEnvironment, ModuleId};
use crate::compiling::module_path::LocalModulePaths;
use crate::diagnostic::AnyDiagnostic;
use crate::name_resolution::symbol::{Symbol, set_symbol_names};
use crate::node_id::FileID;
use crate::parser_error::ParserError;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WorkspaceCompileContext {
    Core,
    Stdlib(&'static str),
    Normal,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ImportCandidate {
    pub name: String,
    pub symbol: Symbol,
    pub module_path: String,
}

#[derive(Clone)]
pub struct Workspace {
    pub local_module_id: ModuleId,
    pub source_root: PathBuf,
    pub versions: FxHashMap<DocumentId, i32>,
    pub file_id_to_document: Vec<DocumentId>,
    pub document_to_file_id: FxHashMap<DocumentId, FileID>,
    /// Shared immutable snapshots (text plus cached line index): the
    /// same allocation the compiler parsed from (CLEAN-04/07).
    pub texts: Vec<crate::common::source_snapshot::SourceSnapshot>,
    pub asts: Vec<Option<AST<NameResolved>>>,
    /// Doc-comment attachments per document (parallel to `asts`):
    /// declaration span plus its comment spans, from the frontend's
    /// documenting parse entry. Hover renders them as markdown.
    pub docs: Vec<Vec<crate::compiling::bridge::BridgedDoc>>,
    pub resolved_names: crate::name_resolution::name_resolver::ResolvedNames,
    /// The checker's program-level residue (catalog, schemes, names).
    pub types: crate::types::TypeOutput,
    /// Per-node facts collected from the typed tree (ADR 0057): hover,
    /// completion, occurrences, and code actions resolve source NodeIDs
    /// against this index into the one authority.
    pub facts: crate::typed_ast::facts::NodeFacts,
    pub diagnostics: FxHashMap<DocumentId, Vec<Diagnostic>>,
    pub stdlib_module_ids: FxHashMap<ModuleId, String>,
    pub importable_modules: FxHashMap<String, Vec<(String, Symbol)>>,
}

impl Workspace {
    pub fn new(docs: Vec<DocumentInput>) -> Option<Self> {
        Self::new_with_package(docs, None)
    }

    /// Check the documents as a package's workspace: sources compile
    /// against the locked dependency graph (dependency imports resolve,
    /// and the backend sees the same inputs `talk run` and `talk test`
    /// accept), with `package::` anchored at the package's source root.
    /// `new` is the dependency-free session (editor).
    pub fn new_with_package(
        docs: Vec<DocumentInput>,
        package: Option<crate::compiling::package::PackageCompileContext>,
    ) -> Option<Self> {
        Self::build(docs, package, None)
    }

    /// `new_with_package` with a per-file parse cache shared across
    /// rebuilds (the LSP's analysis worker): unchanged documents skip
    /// the frontend entirely.
    pub fn new_with_parse_cache(
        docs: Vec<DocumentInput>,
        package: Option<crate::compiling::package::PackageCompileContext>,
        parse_cache: std::rc::Rc<std::cell::RefCell<crate::compiling::driver::ParseCache>>,
    ) -> Option<Self> {
        Self::build(docs, package, Some(parse_cache))
    }

    fn build(
        mut docs: Vec<DocumentInput>,
        package: Option<crate::compiling::package::PackageCompileContext>,
        parse_cache: Option<std::rc::Rc<std::cell::RefCell<crate::compiling::driver::ParseCache>>>,
    ) -> Option<Self> {
        if docs.is_empty() {
            return None;
        }

        docs.sort_by(|a, b| a.id.cmp(&b.id));
        let compile_context = Self::compile_context(&docs);
        if compile_context == WorkspaceCompileContext::Core {
            docs = Self::core_documents_with_overrides(&docs);
        } else if Self::has_test_document(&docs) {
            let harness_root = package
                .as_ref()
                .map(|package| package.source_root.clone())
                .or_else(|| {
                    LocalModulePaths::infer_source_root(
                        docs.iter().map(|doc| PathBuf::from(&doc.path)),
                    )
                })
                .unwrap_or_default();
            let [prelude, postlude] = crate::testing::Harness::human_sources(&harness_root);
            let prelude_path = prelude.path().into_owned();
            let postlude_path = postlude.path().into_owned();
            docs.insert(
                0,
                DocumentInput {
                    id: prelude_path.clone(),
                    path: prelude_path,
                    version: 0,
                    text: prelude.read().ok()?,
                },
            );
            docs.push(DocumentInput {
                id: postlude_path.clone(),
                path: postlude_path,
                version: 0,
                text: postlude.read().ok()?,
            });
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

        let mut texts: Vec<crate::common::source_snapshot::SourceSnapshot> = docs
            .iter()
            .map(|doc| crate::common::source_snapshot::SourceSnapshot::new(doc.text.clone()))
            .collect();

        // The compiler's source inputs share the documents' text
        // allocation: no copy between the workspace and the driver.
        let sources: Vec<Source> = docs
            .iter()
            .map(|doc| Source::in_memory(PathBuf::from(&doc.path), doc.text.clone()))
            .collect();

        let source_root = package
            .as_ref()
            .map(|package| package.source_root.clone())
            .or_else(|| {
                LocalModulePaths::infer_source_root(docs.iter().map(|doc| PathBuf::from(&doc.path)))
            })
            .unwrap_or_default();

        let module_name = match compile_context {
            WorkspaceCompileContext::Core => "Core",
            WorkspaceCompileContext::Stdlib(name) => name,
            WorkspaceCompileContext::Normal => "Workspace",
        };
        let mut config = DriverConfig::new(module_name)
            .source_root(source_root.clone())
            .lenient_parsing()
            .collect_docs(true);
        config.parse_cache = parse_cache;
        match compile_context {
            WorkspaceCompileContext::Core => {
                config.module_id = ModuleId::Core;
            }
            WorkspaceCompileContext::Stdlib(_) => {
                let mut modules = ModuleEnvironment::default();
                modules.import_core(crate::compiling::core::compile());
                config.mode = CompilationMode::Library;
                config.modules = Rc::new(modules);
            }
            WorkspaceCompileContext::Normal => {}
        }

        let local_module_id = config.module_id;
        let driver = match compile_context {
            WorkspaceCompileContext::Core | WorkspaceCompileContext::Stdlib(_) => {
                Driver::new_bare(sources, config)
            }
            WorkspaceCompileContext::Normal => match package {
                Some(package) => {
                    // The package environment already holds core and the
                    // locked dependencies (one shared module numbering
                    // across the graph); stdlib modules still register
                    // on demand as parsing discovers their imports.
                    config.modules = Rc::new(package.modules);
                    config.libraries = package.libraries;
                    config.catalog = package.catalog;
                    config.workspace_root = Some(package.workspace_root);
                    Driver::new_bare(sources, config)
                }
                None => {
                    // The manifest DSL names Package without a `use`, so it
                    // registers like core. Every other builtin package stays
                    // demand-driven: a document's own imports activate them
                    // during parse, and only modules loaded that way serve
                    // auto-import completions and cross-module navigation.
                    if let Some((id, module, _)) =
                        crate::compiling::builtin_packages::try_compiled("Package")
                    {
                        Rc::make_mut(&mut config.modules)
                            .import_shared(module, id)
                            .expect("Package builtin registers once per session");
                    }
                    Driver::new(sources, config)
                }
            },
        };
        // Name+id registration only: nothing compiles here. Definition
        // lookups resolve a symbol's module through this map and compile
        // the target builtin package on demand (definition.rs), so every
        // builtin is reachable no matter what the session imported.
        let stdlib_module_ids = match compile_context {
            WorkspaceCompileContext::Normal => crate::compiling::builtin_packages::all()
                .map(|(name, module_id)| (module_id, name.to_string()))
                .collect(),
            _ => FxHashMap::default(),
        };
        let parsed = driver.parse().ok()?;
        // Auto-import candidates come from the modules this session
        // actually loaded: locked package dependencies plus the stdlib
        // modules parse discovery activated from the documents' own
        // imports. Stdlib modules nobody imported stay unloaded and
        // unindexed.
        let importable_modules = match compile_context {
            WorkspaceCompileContext::Normal => parsed
                .config
                .modules
                .all_modules()
                .filter(|module| module.name != "Core")
                .map(|module| {
                    (
                        module.name.clone(),
                        module
                            .exports
                            .iter()
                            .flat_map(|(name, set)| {
                                set.iter().map(move |&symbol| (name.clone(), symbol))
                            })
                            .filter(|(_, symbol)| module.symbol_names.contains_key(symbol))
                            .collect(),
                    )
                })
                .collect(),
            _ => FxHashMap::default(),
        };
        let resolved = parsed.resolve_names().ok()?;
        // The editor keeps the source-faithful surface AST (type annotations,
        // imports, identifier spans the typed compiler tree strips). Capture it
        // here, before `type_check` consumes the AST.
        let asts_by_source = resolved.phase.asts.clone();
        // Doc attachments likewise move out before `type_check`
        // consumes the resolve phase.
        let docs_by_file = resolved.phase.docs.clone();
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
            texts.push(crate::common::source_snapshot::SourceSnapshot::new(
                source.read().unwrap_or_default(),
            ));
        }
        let typed = resolved.type_check();
        // The MIR-analysis half of `talk check` (ownership, exclusivity,
        // initialization, the unsafe gate): the editor surfaces exactly
        // what compiling would reject. Frontend errors gate it — the
        // backend assumes a well-typed program — and only the normal
        // context runs it (core and stdlib compile against themselves).
        let ownership_rejection =
            if matches!(compile_context, WorkspaceCompileContext::Normal) && !typed.has_errors() {
                typed.check_ownership().err()
            } else {
                None
            };
        let Driver { phase, .. } = typed;
        let (resolved_names, types, facts) = phase.program.into_semantic_parts();
        let diagnostics_any = phase.diagnostics;

        let _symbol_guard = set_symbol_names(resolved_names.symbol_names.clone());
        // One clone of the resolved ASTs is unavoidable today (the
        // driver consumes them in type_check); move each out of the
        // cloned map rather than cloning again into the vector.
        let mut asts: Vec<Option<AST<NameResolved>>> = vec![None; file_id_to_document.len()];
        for ast in asts_by_source.into_values() {
            let idx = ast.file_id.0 as usize;
            if idx < asts.len() {
                asts[idx] = Some(ast);
            }
        }
        let mut docs: Vec<Vec<crate::compiling::bridge::BridgedDoc>> =
            vec![Vec::new(); file_id_to_document.len()];
        for (file_id, file_docs) in docs_by_file {
            let idx = file_id.0 as usize;
            if idx < docs.len() {
                docs[idx] = file_docs;
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
        if let Some((message, location)) = ownership_rejection {
            // File ids index this compile's document list, exactly like
            // frontend diagnostics (`diagnostic_for_any`). A span-less
            // rejection (a synthesized frame) still surfaces, anchored to
            // the first document.
            let located = location.and_then(|(file_id, start, end)| {
                let doc_id = file_id_to_document.get(file_id.0 as usize)?;
                Some((doc_id.clone(), TextRange::new(start, end)))
            });
            let (doc_id, range) = match located {
                Some(located) => located,
                // A span-less rejection anchors to the first real
                // document: harness sources are synthetic and their
                // paths do not exist on disk.
                None => match file_id_to_document
                    .iter()
                    .find(|doc_id| !crate::testing::Harness::is_source_path(Path::new(doc_id)))
                    .or_else(|| file_id_to_document.first())
                {
                    Some(doc_id) => (doc_id.clone(), TextRange::new(0, 0)),
                    None => (String::new(), TextRange::new(0, 0)),
                },
            };
            diagnostics.entry(doc_id).or_default().push(Diagnostic {
                node_id: None,
                kind: None,
                range,
                severity: DiagnosticSeverity::Error,
                message,
            });
        }

        for ast in asts.iter().flatten() {
            let manifest_path = Path::new(&ast.path);
            if manifest_path.file_name().and_then(|name| name.to_str()) != Some("package.tlk") {
                continue;
            }
            let Some(root) = manifest_path.parent() else {
                continue;
            };
            let Ok(manifest) =
                crate::compiling::package::PackageManifest::from_roots(manifest_path, &ast.roots)
            else {
                continue;
            };
            let Err(error) = manifest.validate_targets(root) else {
                continue;
            };
            let Some(doc_id) = file_id_to_document.get(ast.file_id.0 as usize) else {
                continue;
            };
            diagnostics
                .entry(doc_id.clone())
                .or_default()
                .push(Diagnostic {
                    node_id: None,
                    kind: None,
                    range: TextRange::new(0, 0),
                    severity: DiagnosticSeverity::Error,
                    message: error.to_string(),
                });
        }

        for diagnostics in diagnostics.values_mut() {
            diagnostics.sort_by_key(|d| (d.range.start, d.range.end, d.message.clone()));
        }

        Some(Self {
            local_module_id,
            source_root,
            versions,
            file_id_to_document,
            document_to_file_id,
            texts,
            asts,
            docs,
            resolved_names,
            types,
            facts,
            diagnostics,
            stdlib_module_ids,
            importable_modules,
        })
    }

    fn has_test_document(docs: &[DocumentInput]) -> bool {
        docs.iter().any(|doc| {
            Path::new(&doc.path)
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.ends_with(".test.tlk"))
        })
    }

    fn compile_context(docs: &[DocumentInput]) -> WorkspaceCompileContext {
        if Self::should_typecheck_as_core(docs) {
            return WorkspaceCompileContext::Core;
        }
        if let Some(name) = Self::stdlib_module_name_for_docs(docs) {
            return WorkspaceCompileContext::Stdlib(name);
        }
        WorkspaceCompileContext::Normal
    }

    fn should_typecheck_as_core(docs: &[DocumentInput]) -> bool {
        let Some(first_doc) = docs.first() else {
            return false;
        };
        let first_path = PathBuf::from(&first_doc.path);
        let Some(core_dir) = first_path.parent().map(|path| path.to_path_buf()) else {
            return false;
        };

        if core_dir.file_name().and_then(|name| name.to_str()) != Some("core")
            && !Self::is_core_path_override(&core_dir)
        {
            return false;
        }

        docs.iter().all(|doc| {
            let path = PathBuf::from(&doc.path);
            let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
                return false;
            };

            if file_name.ends_with("test.tlk") {
                return true;
            }

            path.parent() == Some(core_dir.as_path())
                && crate::compiling::core::CORE_SOURCE_NAMES.contains(&file_name)
                && doc.text.trim_start().starts_with("// no-core")
        })
    }

    fn stdlib_module_name_for_docs(docs: &[DocumentInput]) -> Option<&'static str> {
        let mut names = docs
            .iter()
            .map(|doc| Self::stdlib_module_name_for_path(Path::new(&doc.path)));
        let first = names.next()??;
        if names.all(|name| name == Some(first)) {
            Some(first)
        } else {
            None
        }
    }

    fn stdlib_module_name_for_path(path: &Path) -> Option<&'static str> {
        crate::compiling::builtin_packages::module_name_for_path(path)
    }

    fn is_core_path_override(path: &Path) -> bool {
        let Some(override_path) = crate::compiling::core::path_override() else {
            return false;
        };

        let normalized_path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        let normalized_override = override_path
            .canonicalize()
            .unwrap_or_else(|_| override_path.to_path_buf());
        normalized_path == normalized_override
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
                    text: text.into(),
                }
            })
            .collect()
    }

    pub fn core() -> Option<Self> {
        let core_files: Vec<(PathBuf, String)> =
            if let Some(core_dir) = crate::compiling::core::path_override() {
                crate::compiling::core::CORE_SOURCE_NAMES
                    .iter()
                    .map(|name| {
                        let path = core_dir.join(name);
                        std::fs::read_to_string(&path).ok().map(|text| (path, text))
                    })
                    .collect::<Option<Vec<_>>>()?
            } else {
                let core_dir = std::env::temp_dir().join("talk-core");
                let _ = std::fs::create_dir_all(&core_dir);

                crate::compiling::core::core_sources()
                    .into_iter()
                    .map(|(name, content)| {
                        let path = core_dir.join(name);
                        let _ = std::fs::write(&path, content);
                        (path, content.to_string())
                    })
                    .collect()
            };

        let file_id_to_document: Vec<DocumentId> = core_files
            .iter()
            .map(|(path, _)| path.to_string_lossy().into_owned())
            .collect();

        let document_to_file_id: FxHashMap<DocumentId, FileID> = file_id_to_document
            .iter()
            .enumerate()
            .map(|(i, id)| (id.clone(), FileID(i as u32)))
            .collect();

        // One allocation per file, shared between the snapshot and the
        // compiler's source input.
        let texts: Vec<crate::common::source_snapshot::SourceSnapshot> = core_files
            .iter()
            .map(|(_, text)| crate::common::source_snapshot::SourceSnapshot::new(text.as_str()))
            .collect();
        let sources: Vec<Source> = core_files
            .iter()
            .zip(texts.iter())
            .map(|((path, _), text)| Source::in_memory(path.clone(), text.text_arc()))
            .collect();

        let source_root =
            LocalModulePaths::infer_source_root(core_files.iter().map(|(path, _)| path.clone()))
                .unwrap_or_default();
        let mut config = DriverConfig::new("Core")
            .source_root(source_root.clone())
            .collect_docs(true);
        config.module_id = ModuleId::Core;

        let driver = Driver::new_bare(sources, config);
        let resolved = driver.parse().ok()?.resolve_names().ok()?;

        let resolved_names = resolved.phase.resolved_names.clone();
        let docs_by_file = resolved.phase.docs.clone();

        let mut asts: Vec<Option<AST<NameResolved>>> = vec![None; file_id_to_document.len()];
        for ast in resolved.phase.asts.values() {
            let idx = ast.file_id.0 as usize;
            if idx < asts.len() {
                asts[idx] = Some(ast.clone());
            }
        }
        let mut docs: Vec<Vec<crate::compiling::bridge::BridgedDoc>> =
            vec![Vec::new(); file_id_to_document.len()];
        for (file_id, file_docs) in docs_by_file {
            let idx = file_id.0 as usize;
            if idx < docs.len() {
                docs[idx] = file_docs;
            }
        }

        Some(Self {
            local_module_id: ModuleId::Core,
            source_root,
            versions: FxHashMap::default(),
            file_id_to_document,
            document_to_file_id,
            texts,
            asts,
            docs,
            resolved_names,
            // Name resolution only: the core workspace exists for symbol
            // rendering, not hover.
            types: Default::default(),
            facts: Default::default(),
            diagnostics: FxHashMap::default(),
            stdlib_module_ids: FxHashMap::default(),
            importable_modules: FxHashMap::default(),
        })
    }

    pub fn stdlib_workspace_for_module_id(&self, module_id: ModuleId) -> Option<Self> {
        let name = self.stdlib_module_ids.get(&module_id)?;
        Self::stdlib_module(name, module_id, None)
    }

    pub fn stdlib_workspace_for_package(&self, package: &str) -> Option<Self> {
        let module_id = self
            .stdlib_module_ids
            .iter()
            .find_map(|(module_id, name)| (name == package).then_some(*module_id))?;
        Self::stdlib_module(package, module_id, None)
    }

    /// A stdlib module's navigation workspace by module id, for
    /// cross-module definition lookups — no session workspace needed.
    /// The LSP's analysis worker builds these off the event loop and
    /// caches them; the parse cache lets a rebuild after a stdlib edit
    /// skip the module's unchanged files.
    pub fn stdlib_module_workspace(
        module_id: ModuleId,
        parse_cache: Option<std::rc::Rc<std::cell::RefCell<crate::compiling::driver::ParseCache>>>,
    ) -> Option<Self> {
        let name = crate::compiling::builtin_packages::name_for_module_id(module_id)?;
        Self::stdlib_module(name, module_id, parse_cache)
    }

    pub(crate) fn exported_symbol(&self, name: &str) -> Option<Symbol> {
        self.resolved_names.exports().get(name)?.first().copied()
    }

    fn stdlib_module(
        name: &str,
        module_id: ModuleId,
        parse_cache: Option<std::rc::Rc<std::cell::RefCell<crate::compiling::driver::ParseCache>>>,
    ) -> Option<Self> {
        let documents = crate::compiling::builtin_packages::source_documents(name)?;
        let source_root =
            LocalModulePaths::infer_source_root(documents.iter().map(|(path, _)| path.clone()))?;
        let file_id_to_document: Vec<DocumentId> = documents
            .iter()
            .map(|(path, _)| path.to_string_lossy().into_owned())
            .collect();
        let document_to_file_id = file_id_to_document
            .iter()
            .enumerate()
            .map(|(index, document)| (document.clone(), FileID(index as u32)))
            .collect();
        let texts: Vec<crate::common::source_snapshot::SourceSnapshot> = documents
            .iter()
            .map(|(_, text)| crate::common::source_snapshot::SourceSnapshot::new(text.as_str()))
            .collect();
        let sources: Vec<Source> = documents
            .into_iter()
            .zip(texts.iter())
            .map(|((path, _), text)| Source::in_memory(path, text.text_arc()))
            .collect();

        let mut modules = ModuleEnvironment::default();
        modules.import_core(crate::compiling::core::compile());

        let mut config = DriverConfig::new(name)
            .source_root(source_root.clone())
            .collect_docs(true);
        config.module_id = module_id;
        config.mode = CompilationMode::Library;
        config.modules = Rc::new(modules);
        config.parse_cache = parse_cache;

        let driver = Driver::new_bare(sources, config);
        let resolved = driver.parse().ok()?.resolve_names().ok()?;
        let resolved_names = resolved.phase.resolved_names;
        let asts_by_source = resolved.phase.asts;
        let docs_by_file = resolved.phase.docs;

        let mut asts: Vec<Option<AST<NameResolved>>> = vec![None; file_id_to_document.len()];
        for ast in asts_by_source.values() {
            let idx = ast.file_id.0 as usize;
            if idx < asts.len() {
                asts[idx] = Some(ast.clone());
            }
        }
        let mut docs: Vec<Vec<crate::compiling::bridge::BridgedDoc>> =
            vec![Vec::new(); file_id_to_document.len()];
        for (file_id, file_docs) in docs_by_file {
            let idx = file_id.0 as usize;
            if idx < docs.len() {
                docs[idx] = file_docs;
            }
        }

        Some(Self {
            local_module_id: module_id,
            source_root,
            versions: FxHashMap::default(),
            file_id_to_document,
            document_to_file_id,
            texts,
            asts,
            docs,
            resolved_names,
            types: Default::default(),
            facts: Default::default(),
            diagnostics: FxHashMap::default(),
            stdlib_module_ids: FxHashMap::default(),
            importable_modules: FxHashMap::default(),
        })
    }

    pub(crate) fn import_candidates(&self, document_id: &DocumentId) -> Vec<ImportCandidate> {
        let current_file_id = self.document_to_file_id.get(document_id).copied();
        let mut seen = FxHashSet::default();
        let mut candidates = Vec::new();

        for symbol in self.resolved_names.public_symbols() {
            let Some(&definition) = self.resolved_names.symbols_to_node.get(&symbol) else {
                continue;
            };
            if Some(definition.0) == current_file_id {
                continue;
            }
            let Some(ast) = self
                .asts
                .get(definition.0.0 as usize)
                .and_then(|ast| ast.as_ref())
                .filter(|ast| !crate::testing::Harness::is_source_path(Path::new(&ast.path)))
            else {
                continue;
            };
            let Some(name) = self.resolved_names.symbol_names.get(&symbol) else {
                continue;
            };
            let Some(root_scope) = self
                .resolved_names
                .scopes
                .get(&crate::node_id::NodeID(definition.0, 0))
            else {
                continue;
            };
            if root_scope.values.get(name) != Some(&symbol)
                && root_scope.types.get(name) != Some(&symbol)
            {
                continue;
            }
            let Some(relative_path) = Path::new(&ast.path).strip_prefix(&self.source_root).ok()
            else {
                continue;
            };
            let segments: Vec<_> = relative_path
                .with_extension("")
                .components()
                .filter_map(|component| match component {
                    std::path::Component::Normal(segment) => {
                        segment.to_str().map(ToOwned::to_owned)
                    }
                    _ => None,
                })
                .collect();
            if segments.is_empty() {
                continue;
            }
            let module_path = format!("package::{}", segments.join("::"));
            if seen.insert((name.clone(), module_path.clone())) {
                candidates.push(ImportCandidate {
                    name: name.clone(),
                    symbol,
                    module_path,
                });
            }
        }

        for (module_path, exports) in &self.importable_modules {
            for (name, symbol) in exports {
                if seen.insert((name.clone(), module_path.clone())) {
                    candidates.push(ImportCandidate {
                        name: name.clone(),
                        symbol: *symbol,
                        module_path: module_path.clone(),
                    });
                }
            }
        }

        candidates.sort_by(|left, right| {
            (&left.name, &left.module_path).cmp(&(&right.name, &right.module_path))
        });
        candidates
    }

    pub fn document_index(&self, id: &DocumentId) -> Option<usize> {
        self.document_to_file_id.get(id).map(|id| id.0 as usize)
    }

    pub fn text_for(&self, id: &DocumentId) -> Option<&str> {
        let idx = self.document_index(id)?;
        self.texts.get(idx).map(|text| text.text())
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

fn parser_error_range(err: &ParserError) -> TextRange {
    match err {
        // Frontend-bridged diagnostics carry their position directly.
        ParserError::Frontend {
            span: Some(span), ..
        } => TextRange::new(span.start, span.end),
        _ => TextRange::new(0, 0),
    }
}

pub(crate) fn diagnostic_for_any(
    file_id_to_document: &[DocumentId],
    texts: &[crate::common::source_snapshot::SourceSnapshot],
    asts: &[Option<AST<NameResolved>>],
    diagnostic: &AnyDiagnostic,
) -> Option<(DocumentId, Diagnostic)> {
    let (id, message, kind, parse_error, prefer_identifier, severity) = match diagnostic {
        AnyDiagnostic::Parsing(diagnostic) => (
            diagnostic.id,
            diagnostic.kind.to_string(),
            DiagnosticKind::Parsing(diagnostic.kind.clone()),
            Some(&diagnostic.kind),
            false,
            &diagnostic.severity,
        ),
        AnyDiagnostic::Macro(diagnostic) => (
            diagnostic.id,
            diagnostic.kind.to_string(),
            DiagnosticKind::Macro(diagnostic.kind.clone()),
            None,
            false,
            &diagnostic.severity,
        ),
        AnyDiagnostic::NameResolution(diagnostic) => (
            diagnostic.id,
            diagnostic.kind.to_string(),
            DiagnosticKind::NameResolution(diagnostic.kind.clone()),
            None,
            true,
            &diagnostic.severity,
        ),
        AnyDiagnostic::Types(diagnostic) => (
            diagnostic.id,
            diagnostic.kind.to_string(),
            DiagnosticKind::Types(diagnostic.kind.clone()),
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
        parser_error_range(err)
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
            node_id: Some(id),
            kind: Some(kind),
            range,
            severity,
            message,
        },
    ))
}

/// One compiler diagnostic bound to the source text it renders against.
#[derive(Clone, Debug)]
pub struct CompileDiagnostic {
    pub document_id: DocumentId,
    pub text: String,
    pub diagnostic: Diagnostic,
}

/// The CLI's one diagnostic pipeline: `talk check`, `talk run`,
/// `talk test`, and package compilation all convert driver diagnostics
/// through here so every command prints the same annotated snippets.
/// Built from the resolved ASTs a driver reports — captured before
/// `type_check` consumes them.
#[derive(Clone, Debug)]
pub struct CompileDiagnostics {
    pub entries: Vec<CompileDiagnostic>,
}

impl CompileDiagnostics {
    pub fn from_driver_asts(
        asts_by_source: &indexmap::IndexMap<crate::compiling::driver::Source, AST<NameResolved>>,
        diagnostics: &[AnyDiagnostic],
    ) -> Self {
        let file_count = asts_by_source
            .values()
            .map(|ast| ast.file_id.0 as usize + 1)
            .max()
            .unwrap_or(0);
        let mut file_id_to_document = vec![String::new(); file_count];
        let mut texts: Vec<crate::common::source_snapshot::SourceSnapshot> =
            vec![crate::common::source_snapshot::SourceSnapshot::new(""); file_count];
        let mut asts = vec![None; file_count];

        for (source, ast) in asts_by_source {
            let index = ast.file_id.0 as usize;
            if index >= file_id_to_document.len() {
                continue;
            }
            file_id_to_document[index] = source.path().into_owned();
            texts[index] = crate::common::source_snapshot::SourceSnapshot::new(
                source.read().unwrap_or_default(),
            );
            asts[index] = Some(ast.clone());
        }

        let mut entries: Vec<_> = diagnostics
            .iter()
            .filter_map(|diagnostic| {
                let file_index = diagnostic_file_index(diagnostic);
                diagnostic_for_any(&file_id_to_document, &texts, &asts, diagnostic).map(
                    |(document_id, diagnostic)| CompileDiagnostic {
                        document_id,
                        text: texts
                            .get(file_index)
                            .map(|text| text.text().to_string())
                            .unwrap_or_default(),
                        diagnostic,
                    },
                )
            })
            .collect();
        entries.sort_by(|left, right| {
            left.document_id
                .cmp(&right.document_id)
                .then(
                    left.diagnostic
                        .range
                        .start
                        .cmp(&right.diagnostic.range.start),
                )
                .then(left.diagnostic.range.end.cmp(&right.diagnostic.range.end))
                .then(left.diagnostic.message.cmp(&right.diagnostic.message))
        });
        CompileDiagnostics { entries }
    }

    #[cfg(feature = "cli")]
    pub fn render_text(&self, color_mode: crate::cli::diagnostics::ColorMode) -> String {
        let mut output = String::new();
        for entry in &self.entries {
            output.push_str(&crate::cli::diagnostics::render_text(
                &entry.document_id,
                &entry.text,
                &entry.diagnostic,
                color_mode,
            ));
        }
        output
    }

    /// Message-per-line rendering for error channels that cannot carry
    /// the annotated snippet form (e.g. a `PackageError` payload
    /// printed by an embedder without the CLI renderer).
    pub fn render_brief(&self) -> String {
        if self.entries.is_empty() {
            return "compilation failed".to_string();
        }
        self.entries
            .iter()
            .map(|entry| format!("{}: {}", entry.document_id, entry.diagnostic.message))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

fn diagnostic_file_index(diagnostic: &AnyDiagnostic) -> usize {
    match diagnostic {
        AnyDiagnostic::Parsing(diagnostic) => diagnostic.id.0.0 as usize,
        AnyDiagnostic::Macro(diagnostic) => diagnostic.id.0.0 as usize,
        AnyDiagnostic::NameResolution(diagnostic) => diagnostic.id.0.0 as usize,
        AnyDiagnostic::Types(diagnostic) => diagnostic.id.0.0 as usize,
    }
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
                    text: text.into(),
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
    fn builtin_source_does_not_import_bundled_builtin_into_itself() {
        let (path, text) = crate::compiling::builtin_packages::source_documents("fs")
            .expect("fs builtin sources")
            .into_iter()
            .next()
            .expect("fs has a source");
        let path = path.to_string_lossy().into_owned();
        let docs = vec![DocumentInput {
            id: path.clone(),
            path,
            version: 0,
            text: text.into(),
        }];

        let workspace = Workspace::new(docs).expect("workspace");
        assert!(
            workspace.diagnostics.is_empty(),
            "expected no builtin diagnostics, got {:?}",
            workspace.diagnostics
        );
    }

    #[test]
    fn ownership_diagnostics_surface_in_the_workspace() {
        // The MIR-analysis half of `talk check` (ownership, exclusivity,
        // initialization) reports through the workspace, so the editor
        // shows these without compiling.
        let text = "func f() -> &String {\n\tlet s = \"x\" + \"y\"\n\ts\n}\nf().byte_count\n";
        let docs = vec![DocumentInput {
            id: "test.tlk".to_string(),
            path: "test.tlk".to_string(),
            version: 0,
            text: text.into(),
        }];
        let workspace = Workspace::new(docs).expect("workspace");
        let diagnostics = workspace
            .diagnostics
            .get("test.tlk")
            .expect("diagnostics for the document");
        let escape = diagnostics
            .iter()
            .find(|d| d.message.contains("cannot return a borrow"))
            .expect("the MIR ownership diagnostic surfaces");
        assert_eq!(escape.severity, DiagnosticSeverity::Error);
        assert!(
            escape.range.start < escape.range.end,
            "the diagnostic carries the frame's span, got {:?}",
            escape.range
        );
        // The editor addresses documents by URI while the compiler
        // reports filesystem paths, and the offending file is rarely the
        // first one: the rejection must land on the document that owns
        // its span, not on whatever sorted first (the LSP's ids are
        // `file://` URLs).
        let dir = std::env::temp_dir().join(format!("talk-ws-uri-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let first = dir.join("a_first.tlk");
        let offender = dir.join("z_offender.tlk");
        std::fs::write(&first, "let ok = 1\n").expect("first source");
        std::fs::write(&offender, text).expect("offending source");
        let doc = |path: &std::path::Path, text: &str| DocumentInput {
            id: format!("file://{}", path.display()),
            path: path.display().to_string(),
            version: 0,
            text: text.into(),
        };
        let docs = vec![doc(&first, "let ok = 1\n"), doc(&offender, text)];
        let workspace = Workspace::new(docs).expect("workspace");
        let offender_id = format!("file://{}", offender.display());
        let diagnostics = workspace
            .diagnostics
            .get(&offender_id)
            .cloned()
            .unwrap_or_default();
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains("cannot return a borrow")),
            "expected the ownership diagnostic on the offending document, got {:?}",
            workspace.diagnostics
        );
        std::fs::remove_dir_all(&dir).ok();

        // A `.test.tlk` document inserts the harness prelude at file 0,
        // shifting every other file id. The rejection must follow its
        // span's file, not the shifted position (this is the talk-syntax
        // shape: the editor saw silence because the diagnostic landed on
        // the prelude, which publishing skips).
        let dir = std::env::temp_dir().join(format!("talk-ws-harness-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let offender = dir.join("parser.test.tlk");
        let harness_text = "func f() -> &String {\n\tlet s = \"x\" + \"y\"\n\ts\n}\ntest(\"t\") {\n\tassert(1 == 1)\n}\n";
        std::fs::write(&offender, harness_text).expect("offending source");
        let docs = vec![doc(&offender, harness_text)];
        let workspace = Workspace::new(docs).expect("workspace");
        let offender_id = format!("file://{}", offender.display());
        let diagnostics = workspace
            .diagnostics
            .get(&offender_id)
            .cloned()
            .unwrap_or_default();
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains("cannot return a borrow")),
            "expected the ownership diagnostic on the test document, got {:?}",
            workspace.diagnostics
        );
        std::fs::remove_dir_all(&dir).ok();

        // Declaration-only programs check every body (`talk check`'s
        // check-all), with no entry required.
        let text = "func bad(consume x: *String) -> Int {\n\tlet y = x\n\tx.byte_count\n}\n";
        let docs = vec![DocumentInput {
            id: "decls.tlk".to_string(),
            path: "decls.tlk".to_string(),
            version: 0,
            text: text.into(),
        }];
        let workspace = Workspace::new(docs).expect("workspace");
        let diagnostics = workspace
            .diagnostics
            .get("decls.tlk")
            .expect("diagnostics for the document");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.message.contains("use of moved value")),
            "expected the moved-value diagnostic, got {diagnostics:?}"
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
            text: text.into(),
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
    fn static_argument_diagnostics_locate_the_argument() {
        // A static kind mismatch must point at the offending argument's
        // own tokens, not fall back to 1:1 (ADR 0035).
        let text = "struct Grid<static Rows: Int> {}\nfunc f(consume g: Grid<true>) -> Int { 1 }\n";
        let docs = vec![DocumentInput {
            id: "static.tlk".to_string(),
            path: "static.tlk".to_string(),
            version: 0,
            text: text.into(),
        }];
        let workspace = Workspace::new(docs).expect("workspace");
        let diagnostics = workspace
            .diagnostics
            .get("static.tlk")
            .expect("diagnostics for the document");
        let literal = text.find("true").expect("the static argument") as u32;
        assert!(
            diagnostics
                .iter()
                .any(|d| d.range.start == literal && d.range.end == literal + 4),
            "expected a diagnostic spanning `true`, got {diagnostics:?}"
        );
    }

    #[test]
    fn test_files_are_checked_with_the_test_harness() {
        let path = "example.test.tlk".to_string();
        let workspace = Workspace::new(vec![DocumentInput {
            id: path.clone(),
            path,
            version: 0,
            text: "test(\"example\") {\n\tassert(1 + 1 == 2)\n}\n".into(),
        }])
        .expect("workspace");
        let diagnostics = workspace
            .diagnostics
            .get("example.test.tlk")
            .cloned()
            .unwrap_or_default();

        assert!(
            diagnostics.is_empty(),
            "test file should type-check with the harness: {diagnostics:?}"
        );
    }

    #[test]
    fn question_mark_return_mismatches_blame_surface_syntax_without_internal_types() {
        let path = "propagation.test.tlk".to_string();
        let text = "func result() -> Result<Int, String> { .ok(1) }\n\ntest(\"example\") {\n\tassert(result()? == 1)\n}\n";
        let workspace = Workspace::new(vec![DocumentInput {
            id: path.clone(),
            path: path.clone(),
            version: 0,
            text: text.into(),
        }])
        .expect("workspace");
        let diagnostics = workspace
            .diagnostics
            .get(&path)
            .expect("diagnostics for the test document");
        let diagnostic = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.message.contains("Cannot use '?' here"))
            .expect("targeted propagation diagnostic");
        let expression = text.find("result()?").expect("propagation expression") as u32;

        assert_eq!(diagnostic.range, TextRange::new(expression, expression + 9));
        assert!(diagnostic.message.contains("returns ()"));
        assert!(
            !diagnostic
                .message
                .as_bytes()
                .windows(2)
                .any(|pair| pair[0] == b'?' && pair[1].is_ascii_digit()),
            "diagnostic exposed an internal inference variable: {diagnostic:?}"
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
        std::fs::write(&lib_path, "pub let broken: Int = \"not an int\"\n").expect("lib");
        let main_text = "use package::lib::{ broken }\nprint(broken)\n";
        std::fs::write(&main_path, main_text).expect("main");

        let main_id = main_path.to_string_lossy().into_owned();
        let docs = vec![DocumentInput {
            id: main_id.clone(),
            path: main_id.clone(),
            version: 0,
            text: main_text.into(),
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
}
