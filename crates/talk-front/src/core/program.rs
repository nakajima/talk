use indexmap::IndexMap;
use rustc_hash::FxHashSet;

use crate::ast::AST;
use crate::diagnostic::{AnyDiagnostic, Severity};
use crate::front::module::{ModuleEnvironment, ModuleId};
use crate::front::source::{SharedCatalog, Source};
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::symbol::{Symbol, Symbols};
use crate::node_id::FileID;
use crate::parsing::ast::NameResolved;
use crate::types::TypeOutput;

/// Type-check resolved sources into the frontend's one checked output.
#[allow(clippy::too_many_arguments)]
pub fn check_program(
    asts: IndexMap<Source, AST<NameResolved>>,
    symbols: &mut Symbols,
    resolved_names: ResolvedNames,
    modules: &ModuleEnvironment,
    module_id: ModuleId,
    shared: &mut SharedCatalog,
    diagnostics: &mut Vec<AnyDiagnostic>,
    file_dependencies: Vec<(FileID, FileID)>,
) -> CoreProgram {
    let (types, elaboration, type_diagnostics) = crate::types::generate::check_types(
        &asts,
        symbols,
        &resolved_names,
        modules,
        module_id,
        shared,
    );
    diagnostics.extend(type_diagnostics);
    let blocked_files = error_diagnostic_files(diagnostics);
    CoreProgram::from_checked_asts(
        asts,
        resolved_names,
        types,
        elaboration,
        &blocked_files,
        file_dependencies,
    )
}

pub fn error_diagnostic_files(diagnostics: &[AnyDiagnostic]) -> FxHashSet<FileID> {
    diagnostics
        .iter()
        .filter_map(|diagnostic| {
            let (id, severity) = match diagnostic {
                AnyDiagnostic::Parsing(diagnostic) => (diagnostic.id, &diagnostic.severity),
                AnyDiagnostic::Macro(diagnostic) => (diagnostic.id, &diagnostic.severity),
                AnyDiagnostic::NameResolution(diagnostic) => (diagnostic.id, &diagnostic.severity),
                AnyDiagnostic::Types(diagnostic) => (diagnostic.id, &diagnostic.severity),
            };
            (*severity == Severity::Error && id.0 != FileID::SYNTHESIZED).then_some(id.0)
        })
        .collect()
}

/// The phase-owned checked program and program-level semantic facts for one
/// module. Compiler phases after type checking receive this artifact instead
/// of a loose type output and separately owned tree.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct CoreProgram {
    core: crate::core::Core<crate::core::Nested>,
    resolved_names: ResolvedNames,
    types: TypeOutput,
    /// Editor facts for files blocked from the tree build by errors —
    /// those files have no typed tree, so their per-node facts keep index
    /// form here (one home per file; see `core::facts`).
    #[serde(default)]
    blocked_facts: crate::core::facts::NodeFacts,
    /// Canonical local import edges (importer, imported) recorded
    /// during parse discovery (CLEAN-03).
    #[serde(default)]
    file_dependencies: Vec<(FileID, FileID)>,
}

impl CoreProgram {
    fn from_checked_asts(
        asts: IndexMap<Source, AST<NameResolved>>,
        resolved_names: ResolvedNames,
        types: TypeOutput,
        elaboration: crate::types::output::Elaboration,
        blocked_files: &FxHashSet<FileID>,
        file_dependencies: Vec<(FileID, FileID)>,
    ) -> Self {
        let mut files = IndexMap::default();
        for (source, ast) in asts {
            if blocked_files.contains(&ast.file_id) {
                continue;
            }
            let file = super::build::build_file(&ast, &types, &elaboration);
            files.insert(source, file);
        }
        let blocked_facts =
            crate::core::facts::NodeFacts::from_blocked_elaboration(&elaboration, blocked_files);
        let core = crate::core::Core::new(in_initialization_order(files, &file_dependencies));
        core.assert_lint();
        Self {
            core,
            resolved_names,
            types,
            blocked_facts,
            file_dependencies,
        }
    }

    pub fn types(&self) -> &TypeOutput {
        &self.types
    }

    /// This module's own declared symbol names (local-only — imported
    /// names live in `types().display_names`). The naming view MIR debug
    /// info, the ABI, and the REPL read; the rest of the resolution
    /// artifacts (scopes, declarations) never leave the frontend, so a
    /// later phase cannot re-derive a resolution (ADR 0057).
    pub fn symbol_names(&self) -> &rustc_hash::FxHashMap<Symbol, String> {
        &self.resolved_names.symbol_names
    }

    /// Test-only access to the full resolution artifacts; production
    /// phases get the naming view above and nothing else.
    #[cfg(any(test, feature = "test-access"))]
    pub fn resolved_names(&self) -> &ResolvedNames {
        &self.resolved_names
    }

    /// Compatibility view for callers that iterate files. Semantic passes
    /// should preserve the phase marker through [`Self::core`].
    pub fn files(&self) -> &IndexMap<Source, crate::core::TypedFile> {
        self.core.files()
    }

    pub fn core(&self) -> &crate::core::Core<crate::core::Nested> {
        &self.core
    }

    /// The per-node facts index collected from the typed tree — the same
    /// view [`Self::into_semantic_parts`] hands the editor layer, for
    /// tests that keep the program whole.
    #[cfg(any(test, feature = "test-access"))]
    pub fn node_facts(&self) -> crate::core::facts::NodeFacts {
        let mut facts = crate::core::facts::NodeFacts::collect(self.core.files().values());
        facts.extend(self.blocked_facts.clone());
        facts
    }

    /// Decompose into the editor layer's holdings: resolution artifacts,
    /// the checker's program-level residue, and the per-node facts index
    /// collected from the typed tree (the tree is the one authority for
    /// per-occurrence facts; the index is rebuilt with it, ADR 0057).
    pub fn into_semantic_parts(self) -> (ResolvedNames, TypeOutput, crate::core::facts::NodeFacts) {
        let mut facts = crate::core::facts::NodeFacts::collect(self.core.files().values());
        facts.extend(self.blocked_facts);
        (self.resolved_names, self.types, facts)
    }
}

/// Order a program's files so a file's local imports initialize before
/// it (LINK-02: deterministic, dependency-first globals) — the published
/// order every consumer of `files()` iterates in. Edges are the canonical
/// pairs parse discovery recorded (explicit `use` decls and qualified
/// local references alike); files without edges keep their discovery
/// order, and a cycle falls back to discovery order for the remainder.
fn in_initialization_order(
    files: IndexMap<Source, crate::core::TypedFile>,
    file_dependencies: &[(FileID, FileID)],
) -> IndexMap<Source, crate::core::TypedFile> {
    use rustc_hash::FxHashMap;

    let position: FxHashMap<FileID, usize> = files
        .values()
        .enumerate()
        .map(|(index, file)| (file.file_id, index))
        .collect();
    let mut deps: Vec<Vec<usize>> = vec![Vec::new(); files.len()];
    for (importer, imported) in file_dependencies {
        let (Some(&from), Some(&to)) = (position.get(importer), position.get(imported)) else {
            // An edge can name a file blocked by earlier errors; the
            // remaining graph still orders.
            continue;
        };
        if from != to && !deps[from].contains(&to) {
            deps[from].push(to);
        }
    }
    // Depth-first with insertion-order roots: every file keeps its
    // discovery position except that its imports hoist ahead of it; a
    // cycle breaks at the back edge.
    fn visit(index: usize, deps: &[Vec<usize>], state: &mut [u8], order: &mut Vec<usize>) {
        if state[index] != 0 {
            return;
        }
        state[index] = 1;
        for &dep in &deps[index] {
            if state[dep] == 0 {
                visit(dep, deps, state, order);
            }
        }
        state[index] = 2;
        order.push(index);
    }
    let mut state = vec![0u8; files.len()];
    let mut indexes = Vec::with_capacity(files.len());
    for index in 0..files.len() {
        visit(index, &deps, &mut state, &mut indexes);
    }
    let mut entries: Vec<Option<(Source, crate::core::TypedFile)>> =
        files.into_iter().map(Some).collect();
    indexes
        .into_iter()
        .filter_map(|index| entries[index].take())
        .collect()
}
