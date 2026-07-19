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
#[derive(Clone)]
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
            files,
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
