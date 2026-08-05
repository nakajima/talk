use std::path::{Path, PathBuf};

use crate::analysis::occurrence::{document_id_for_path, occurrence_at};
use crate::analysis::workspace::Workspace;
use crate::analysis::{DocumentId, TextRange, span_contains};
use crate::compiling::{module::ModuleId, module_path::LocalModulePaths};
use crate::name_resolution::symbol::Symbol;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Location {
    pub document_id: DocumentId,
    pub range: TextRange,
}

pub fn goto_definition(
    module: &Workspace,
    core: Option<&Workspace>,
    document_id: &DocumentId,
    byte_offset: u32,
) -> Option<Location> {
    let file_id = *module.document_to_file_id.get(document_id)?;
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())?;

    // An import path denotes a file, not a symbol, so it stays here;
    // every other occurrence resolves through the shared resolver.
    for root in &ast.roots {
        let crate::node::Node::Decl(decl) = root else {
            continue;
        };
        if let Some(location) = goto_definition_from_import_path(module, ast, decl, byte_offset) {
            return Some(location);
        }
    }

    let occurrence = occurrence_at(module, document_id, byte_offset)?;
    definition_location_for_symbol(module, core, occurrence.symbol)
}

fn goto_definition_from_import_path(
    module: &Workspace,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    decl: &crate::node_kinds::decl::Decl,
    byte_offset: u32,
) -> Option<Location> {
    use crate::node_kinds::decl::DeclKind;

    let DeclKind::Import(import) = &decl.kind else {
        return None;
    };

    if !span_contains(import.path_span, byte_offset) {
        return None;
    }

    match &import.path {
        crate::node_kinds::decl::ImportPath::Local(_) => {
            let target_path = resolve_import_path(&module.source_root, &ast.path, &import.path)?;
            let document_id = document_id_for_path(module, &target_path)?;
            Some(Location {
                document_id,
                range: TextRange::new(0, 0),
            })
        }
        crate::node_kinds::decl::ImportPath::Package(package) => {
            let stdlib = module.stdlib_workspace_for_package(package)?;
            module_start_location(&stdlib)
        }
    }
}

fn module_start_location(module: &Workspace) -> Option<Location> {
    let document_id = module.file_id_to_document.first()?.clone();
    Some(Location {
        document_id,
        range: TextRange::new(0, 0),
    })
}

fn resolve_import_path(
    source_root: &Path,
    source_path: &str,
    import_path: &crate::node_kinds::decl::ImportPath,
) -> Option<PathBuf> {
    use crate::node_kinds::decl::ImportPath;

    match import_path {
        ImportPath::Local(module_path) => {
            LocalModulePaths::new(source_root).resolve(source_path, module_path)
        }
        ImportPath::Package(_) => None,
    }
}

pub(crate) fn definition_location_for_symbol(
    module: &Workspace,
    core: Option<&Workspace>,
    symbol: Symbol,
) -> Option<Location> {
    if symbol.module_id() == Some(ModuleId::Core) {
        let core = core?;
        return definition_location_in_module(core, symbol);
    }
    if let Some(module_id) = symbol.module_id()
        && let Some(stdlib) = module.stdlib_workspace_for_module_id(module_id)
    {
        return definition_location_in_module(&stdlib, symbol);
    }
    // Everything else — the workspace's own symbols included — carries
    // its module stamp (absolute identity, ADR 0038); look it up as
    // minted.
    definition_location_in_module(module, symbol)
}

fn definition_location_in_module(module: &Workspace, symbol: Symbol) -> Option<Location> {
    let def_node = *module.resolved_names.symbols_to_node.get(&symbol)?;
    let file_id = def_node.0;
    let document_id = module.file_id_to_document.get(file_id.0 as usize)?.clone();
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())?;

    let (start, end) = if let Some(span) = definition_name_span(ast, def_node) {
        span
    } else if let Some(meta) = ast.meta.get(&def_node) {
        match meta.identifiers.first() {
            Some(token) => (token.start, token.end),
            None => (meta.start.start, meta.end.end),
        }
    } else {
        node_span(ast, def_node)?
    };

    Some(Location {
        document_id,
        range: TextRange::new(start, end),
    })
}

fn definition_name_span(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    node_id: crate::node_id::NodeID,
) -> Option<(u32, u32)> {
    let node = ast.find(node_id)?;
    match node {
        crate::node::Node::Decl(decl) => definition_decl_name_span(&decl),
        crate::node::Node::Func(func) => Some((func.name_span.start, func.name_span.end)),
        crate::node::Node::Parameter(param) => Some((param.name_span.start, param.name_span.end)),
        crate::node::Node::GenericDecl(generic) => {
            Some((generic.name_span.start, generic.name_span.end))
        }
        _ => None,
    }
}

fn definition_decl_name_span(decl: &crate::node_kinds::decl::Decl) -> Option<(u32, u32)> {
    use crate::node_kinds::decl::DeclKind;

    match &decl.kind {
        DeclKind::Struct { name_span, .. }
        | DeclKind::Protocol { name_span, .. }
        | DeclKind::Enum { name_span, .. }
        | DeclKind::Property { name_span, .. }
        | DeclKind::Effect { name_span, .. }
        | DeclKind::EnumVariant { name_span, .. } => Some((name_span.start, name_span.end)),
        DeclKind::TypeAlias(_, name_span, _) => Some((name_span.start, name_span.end)),
        DeclKind::Init { .. } => Some((decl.span.start, decl.span.end)),
        _ => None,
    }
}

fn node_span(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    node_id: crate::node_id::NodeID,
) -> Option<(u32, u32)> {
    let node = ast.find(node_id)?;
    match node {
        crate::node::Node::Pattern(pattern) => Some((pattern.span.start, pattern.span.end)),
        crate::node::Node::Expr(expr) => Some((expr.span.start, expr.span.end)),
        crate::node::Node::Decl(decl) => Some((decl.span.start, decl.span.end)),
        crate::node::Node::Stmt(stmt) => Some((stmt.span.start, stmt.span.end)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::analysis::{DocumentId, DocumentInput, Workspace, goto_definition};

    fn workspace_for(docs: &[(&str, &str)]) -> Workspace {
        let inputs = docs
            .iter()
            .map(|(path, text)| DocumentInput {
                id: path.to_string(),
                path: path.to_string(),
                version: 0,
                text: (*text).into(),
            })
            .collect();
        Workspace::new(inputs).expect("workspace")
    }

    /// The source text under the definition of the last occurrence of
    /// `needle` in `code`.
    fn definition_text(code: &str, needle: &str) -> Option<(DocumentId, String)> {
        definition_text_at(code, code.rfind(needle).expect("needle in code") as u32)
    }

    fn definition_text_at(code: &str, offset: u32) -> Option<(DocumentId, String)> {
        let ws = workspace_for(&[("main.tlk", code)]);
        let location = goto_definition(&ws, None, &"main.tlk".to_string(), offset)?;
        let file_id = ws.document_to_file_id.get(&location.document_id)?;
        let text = ws.texts.get(file_id.0 as usize)?;
        Some((
            location.document_id.clone(),
            text.text()[location.range.start as usize..location.range.end as usize].to_string(),
        ))
    }

    #[test]
    fn definition_on_a_local_variable_use() {
        let code = "let greeting = 1\ngreeting\n";
        let (doc, text) = definition_text(code, "greeting").expect("definition");
        assert_eq!(doc, "main.tlk");
        assert_eq!(text, "greeting");
    }

    #[test]
    fn definition_on_a_function_call() {
        let code = "func double(x: Int) -> Int {\n\tx\n}\ndouble(1)\n";
        let (_, text) = definition_text(code, "double").expect("definition");
        // Top-level funcs declare a global whose node is not the `Func`
        // node, so the current location spans the whole declaration
        // rather than just the name.
        assert_eq!(text, "func double(x: Int) -> Int {\n\tx\n}");
    }

    #[test]
    fn definition_on_a_member_access() {
        let code = "struct Point {\n\tlet x: Int\n}\nlet p = Point(x: 1)\np.x\n";
        let offset = code.rfind(".x").expect("member") as u32 + 1;
        let (doc, text) = definition_text_at(code, offset).expect("definition");
        assert_eq!(doc, "main.tlk");
        assert_eq!(text, "x");
    }

    #[test]
    fn definition_on_a_nominal_type_annotation() {
        let code =
            "struct Box {\n\tlet value: Int\n}\nfunc f(b: Box) -> Int {\n\tb.value\n}\n";
        let (_, text) = definition_text(code, "Box)").expect("definition");
        assert_eq!(text, "Box");
    }

    #[test]
    fn definition_through_nested_generic_arguments() {
        let code = "struct Box<T> {\n\tlet value: T\n}\nfunc f(b: Box<Box<Int>>) -> Int {\n\t1\n}\n";
        // The inner `Box` resolves to the same declaration as the outer.
        let inner = code.rfind("Box<Int").expect("inner Box") as u32;
        let (_, text) = definition_text_at(code, inner).expect("definition");
        assert_eq!(text, "Box");
        let outer = code.find("Box<Box").expect("outer Box") as u32;
        let (_, text) = definition_text_at(code, outer).expect("definition");
        assert_eq!(text, "Box");
    }

    #[test]
    fn definition_through_tuple_type() {
        let code =
            "struct Box {\n\tlet value: Int\n}\nfunc f(b: (Int, Box)) -> Int {\n\t1\n}\n";
        let (_, text) = definition_text(code, "Box").expect("definition");
        assert_eq!(text, "Box");
    }

    #[test]
    fn definition_through_record_type() {
        let code =
            "struct Box {\n\tlet value: Int\n}\nfunc f(b: { value: Box }) -> Int {\n\t1\n}\n";
        let (_, text) = definition_text(code, "Box").expect("definition");
        assert_eq!(text, "Box");
    }

    #[test]
    fn definition_on_a_self_type_annotation() {
        let code = "struct Box {\n\tlet value: Int\n}\nextend Box {\n\tfunc get() -> Self {\n\t\tself\n\t}\n}\n";
        let (_, text) = definition_text(code, "Self").expect("definition");
        assert_eq!(text, "Box");
    }

    #[test]
    fn definition_on_effect_names() {
        let code = "effect 'bail(error) -> Never\nfunc build() 'bail -> Int {\n\t'bail(\"stop\")\n}\n#handle 'bail { err in\n\t0\n}\nbuild()\n";
        // The effect declaration's name span is the target for the call
        // site, the function's effect list, and the handler.
        for needle in ["'bail(\"", "'bail ->", "'bail {"] {
            let offset = code.find(needle).expect("needle in code") as u32;
            let (_, text) = definition_text_at(code, offset).expect("definition");
            assert_eq!(text, "bail", "needle {needle}");
        }
    }

    #[test]
    fn definition_on_a_named_import() {
        let main = "use package::other::{ answer }\nprint(answer)\n";
        let other = "pub let answer = 42\n";
        let ws = workspace_for(&[("src/main.tlk", main), ("src/other.tlk", other)]);

        // The use-site import entry jumps to the exported binding.
        let offset = main.find("answer }").expect("import entry") as u32;
        let location =
            goto_definition(&ws, None, &"src/main.tlk".to_string(), offset).expect("definition");
        assert_eq!(location.document_id, "src/other.tlk");
        assert_eq!(
            &other[location.range.start as usize..location.range.end as usize],
            "answer"
        );

        // A later use of the imported name jumps there too.
        let offset = main.rfind("answer").expect("use site") as u32;
        let location =
            goto_definition(&ws, None, &"src/main.tlk".to_string(), offset).expect("definition");
        assert_eq!(location.document_id, "src/other.tlk");
    }

    #[test]
    fn definition_on_an_import_path_lands_at_the_file_start() {
        let main = "use package::other::{ answer }\nprint(answer)\n";
        let other = "pub let answer = 42\n";
        let ws = workspace_for(&[("src/main.tlk", main), ("src/other.tlk", other)]);
        let offset = main.find("other").expect("import path") as u32;
        let location =
            goto_definition(&ws, None, &"src/main.tlk".to_string(), offset).expect("definition");
        assert_eq!(location.document_id, "src/other.tlk");
        assert_eq!((location.range.start, location.range.end), (0, 0));
    }
}
