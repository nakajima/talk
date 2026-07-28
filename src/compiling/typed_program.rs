pub(crate) mod build;

use indexmap::IndexMap;
use rustc_hash::FxHashSet;

use crate::ast::AST;
use crate::compiling::driver::Source;
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::node_id::FileID;
use crate::parsing::ast::NameResolved;
use crate::types::TypeOutput;

/// The checked program tree and checked semantic facts for one module.
///
/// Compiler phases after type checking receive this artifact instead of a
/// loose `TypeOutput` plus a separately-owned compiler tree phase. The current typed tree
/// representation is still backed by `typed_ast` nodes, but ownership of that tree is
/// local to this module-facing product; callers go through `TypedProgram`.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct TypedProgram {
    files: IndexMap<Source, crate::typed_ast::TypedFile>,
    resolved_names: ResolvedNames,
    types: TypeOutput,
}

impl TypedProgram {
    pub(crate) fn from_checked_asts(
        asts: IndexMap<Source, AST<NameResolved>>,
        resolved_names: ResolvedNames,
        types: TypeOutput,
        blocked_files: &FxHashSet<FileID>,
    ) -> Self {
        let mut files = IndexMap::default();
        for (source, ast) in asts {
            if blocked_files.contains(&ast.file_id) {
                continue;
            }
            let file = build::build_file(&ast, &types);
            files.insert(source, file);
        }
        Self {
            files: in_initialization_order(files),
            resolved_names,
            types,
        }
    }

    pub fn types(&self) -> &TypeOutput {
        &self.types
    }

    pub fn resolved_names(&self) -> &ResolvedNames {
        &self.resolved_names
    }

    pub(crate) fn files(&self) -> &IndexMap<Source, crate::typed_ast::TypedFile> {
        &self.files
    }

    pub(crate) fn into_semantic_parts(self) -> (ResolvedNames, TypeOutput) {
        (self.resolved_names, self.types)
    }
}

/// Order a program's files so a file's local imports initialize before
/// it (LINK-02: deterministic, dependency-first globals) — the published
/// order every consumer of `files()` iterates in. Import edges come from
/// `use package::Module` markers matched to sibling file stems; files
/// without edges keep their discovery order, and a cycle falls back to
/// discovery order for the remainder.
fn in_initialization_order(
    files: IndexMap<Source, crate::typed_ast::TypedFile>,
) -> IndexMap<Source, crate::typed_ast::TypedFile> {
    use crate::node_kinds::decl::ImportPath;
    use crate::typed_ast::{DeclKind, Node};
    use rustc_hash::FxHashMap;

    let position: FxHashMap<String, usize> = files
        .keys()
        .enumerate()
        .filter_map(|(index, source)| {
            source
                .source_path()
                .and_then(|path| path.file_stem())
                .and_then(|stem| stem.to_str())
                .map(|stem| (stem.to_string(), index))
        })
        .collect();
    let mut deps: Vec<Vec<usize>> = vec![Vec::new(); files.len()];
    for (index, file) in files.values().enumerate() {
        for root in &file.roots {
            if let Node::Decl(decl) = root
                && let DeclKind::Import(import) = &decl.kind
                && let ImportPath::Local(path) = &import.path
                && let Some(stem) = path.rsplit("::").next()
                && let Some(&target) = position.get(stem)
                && target != index
            {
                deps[index].push(target);
            }
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
    let mut entries: Vec<Option<(Source, crate::typed_ast::TypedFile)>> =
        files.into_iter().map(Some).collect();
    indexes
        .into_iter()
        .filter_map(|index| entries[index].take())
        .collect()
}
