//! Hover: the type of the thing under the cursor, rendered from the
//! checker's output tables (`TypeOutput.node_types` for expressions,
//! `schemes` for named binders). Serves the wasm `hover` entry point and
//! `talk hover`.

use crate::analysis::workspace::Workspace;
use crate::analysis::{DocumentId, TextRange, node_ids_at_offset};
use crate::node::Node;
use crate::node_kinds::{expr::ExprKind, pattern::PatternKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hover {
    /// The rendered type or signature.
    pub contents: String,
    /// The source range the contents describe.
    pub range: TextRange,
}

/// The hover for the smallest node containing `byte_offset`, walking
/// outward until a node has something to say.
pub fn hover_at(
    workspace: &Workspace,
    document_id: &DocumentId,
    byte_offset: u32,
) -> Option<Hover> {
    let idx = workspace.document_index(document_id)?;
    let ast = workspace.asts.get(idx)?.as_ref()?;
    let _names =
        crate::name_resolution::symbol::set_symbol_names(workspace.types.display_names.clone());

    for node_id in node_ids_at_offset(ast, byte_offset) {
        let Some(node) = ast.find(node_id) else {
            continue;
        };
        if let Some(hover) = hover_for_node(workspace, &node) {
            return Some(hover);
        }
    }
    None
}

/// The hover for an exact node, by id (editor integrations that already
/// hold a node id from a previous query).
pub fn hover_for_node_id(
    workspace: &Workspace,
    document_id: &DocumentId,
    node_id: crate::node_id::NodeID,
) -> Option<Hover> {
    let idx = workspace.document_index(document_id)?;
    let ast = workspace.asts.get(idx)?.as_ref()?;
    let _names =
        crate::name_resolution::symbol::set_symbol_names(workspace.types.display_names.clone());
    let node = ast.find(node_id)?;
    hover_for_node(workspace, &node)
}

/// "file:index" or a bare index ("0:42" / "42") — the node-id query
/// format shared by the playground and `talk hover --node-id`.
pub fn parse_node_id(input: &str) -> Option<crate::node_id::NodeID> {
    let (file_id, node_id) = match input.split_once(':') {
        Some((file_id, node_id)) => (file_id, node_id),
        None => ("0", input),
    };
    Some(crate::node_id::NodeID(
        crate::node_id::FileID(file_id.parse::<u32>().ok()?),
        node_id.parse::<u32>().ok()?,
    ))
}

fn hover_for_node(workspace: &Workspace, node: &Node) -> Option<Hover> {
    match node {
        // An expression statement shares its expression's NodeID, and
        // `find` returns the statement wrapper.
        Node::Stmt(crate::node_kinds::stmt::Stmt {
            kind: crate::node_kinds::stmt::StmtKind::Expr(expr),
            ..
        }) => hover_for_node(workspace, &Node::Expr(expr.clone())),
        Node::Expr(expr) => {
            // A reference to a named binder shows `name: scheme` (the
            // generic type, not the use site's instantiation); other
            // named references show `name: type`; any other expression
            // shows its checked type.
            if let ExprKind::Variable(name) | ExprKind::Constructor(name) = &expr.kind
                && let Ok(symbol) = name.symbol()
                && let Some(hover) = hover_for_symbol(
                    workspace,
                    expr.id,
                    symbol,
                    &name.name_str(),
                    TextRange::new(expr.span.start, expr.span.end),
                    workspace.types.node_types.get(&expr.id),
                )
            {
                return Some(hover);
            }
            let ty = workspace.types.node_types.get(&expr.id)?;
            Some(Hover {
                contents: with_ownership_details(workspace, expr.id, ty.render_mono(), Some(ty)),
                range: TextRange::new(expr.span.start, expr.span.end),
            })
        }
        Node::Func(func) => {
            let symbol = func.name.symbol().ok()?;
            let scheme = workspace.types.schemes.get(&symbol)?;
            Some(Hover {
                contents: with_ownership_details(
                    workspace,
                    func.id,
                    format!("{}: {}", func.name.name_str(), scheme.render()),
                    Some(&scheme.ty),
                ),
                range: TextRange::new(func.name_span.start, func.name_span.end),
            })
        }
        Node::Parameter(param) => hover_for_name(
            workspace,
            param.id,
            &param.name,
            TextRange::new(param.name_span.start, param.name_span.end),
            None,
        ),
        Node::Pattern(pattern) => match &pattern.kind {
            PatternKind::Bind(name) => hover_for_name(
                workspace,
                pattern.id,
                name,
                TextRange::new(pattern.span.start, pattern.span.end),
                None,
            ),
            PatternKind::Variant { .. } => {
                let resolution = workspace.types.member_resolutions.get(&pattern.id)?;
                let crate::types::output::MemberResolution::Direct(symbol) = resolution else {
                    return None;
                };
                let (enum_name, case, payloads) =
                    workspace
                        .types
                        .catalog
                        .enums
                        .iter()
                        .find_map(|(owner, info)| {
                            info.variants.iter().find_map(|(case, variant)| {
                                (variant.symbol == *symbol).then(|| {
                                    let owner = workspace
                                        .types
                                        .display_names
                                        .get(owner)
                                        .cloned()
                                        .unwrap_or_else(|| owner.to_string());
                                    (owner, case.clone(), variant.argument_types().to_vec())
                                })
                            })
                        })?;
                let contents = if payloads.is_empty() {
                    format!("{enum_name}.{case}")
                } else {
                    let payloads: Vec<String> =
                        payloads.iter().map(|ty| ty.render_mono()).collect();
                    format!("{enum_name}.{case}({})", payloads.join(", "))
                };
                Some(Hover {
                    contents: with_ownership_details(workspace, pattern.id, contents, None),
                    range: TextRange::new(pattern.span.start, pattern.span.end),
                })
            }
            _ => None,
        },
        _ => None,
    }
}

fn hover_for_name(
    workspace: &Workspace,
    node: crate::node_id::NodeID,
    name: &crate::name::Name,
    range: TextRange,
    fallback_ty: Option<&crate::types::ty::Ty>,
) -> Option<Hover> {
    let symbol = name.symbol().ok()?;
    let name = name.name_str();
    hover_for_symbol(workspace, node, symbol, &name, range, fallback_ty)
}

fn hover_for_symbol(
    workspace: &Workspace,
    node: crate::node_id::NodeID,
    symbol: crate::name_resolution::symbol::Symbol,
    name: &str,
    range: TextRange,
    fallback_ty: Option<&crate::types::ty::Ty>,
) -> Option<Hover> {
    if let Some(scheme) = workspace.types.schemes.get(&symbol) {
        return Some(Hover {
            contents: with_ownership_details(
                workspace,
                node,
                format!("{name}: {}", scheme.render()),
                Some(&scheme.ty),
            ),
            range,
        });
    }

    if let Some(ty) = workspace.types.local_tys.get(&symbol).or(fallback_ty) {
        return Some(Hover {
            contents: with_ownership_details(
                workspace,
                node,
                format!("{name}: {}", ty.render_mono()),
                Some(ty),
            ),
            range,
        });
    }

    None
}

fn with_ownership_details(
    workspace: &Workspace,
    node: crate::node_id::NodeID,
    contents: String,
    ty: Option<&crate::types::ty::Ty>,
) -> String {
    let details = crate::analysis::ownership::hover_details_for_node(workspace, node, ty);
    if details.is_empty() {
        return contents;
    }

    let mut lines = vec![contents, String::new(), "ownership:".to_string()];
    lines.extend(details.into_iter().map(|detail| format!("  {detail}")));
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::DocumentInput;

    fn workspace(source: &str) -> Workspace {
        let doc = DocumentInput {
            id: "<test>".to_string(),
            path: "test.tlk".to_string(),
            version: 0,
            text: source.to_string(),
        };
        Workspace::new(vec![doc]).expect("workspace")
    }

    fn hover(source: &str, at: &str) -> Option<Hover> {
        let offset = source.find(at).expect("hover target in source") as u32;
        hover_at(&workspace(source), &"<test>".to_string(), offset)
    }

    #[test]
    fn hover_resolves_by_node_id() {
        let source = "let a = 21\na";
        let ws = workspace(source);
        let doc = "<test>".to_string();
        // Find the literal's node id through the offset path first.
        let offset = source.find("21").expect("literal") as u32;
        let idx = ws.document_index(&doc).expect("doc");
        let ast = ws.asts[idx].as_ref().expect("ast");
        let node_id = crate::analysis::node_ids_at_offset(ast, offset)
            .into_iter()
            .find(|id| {
                hover_for_node_id(&ws, &doc, *id).is_some_and(|hover| hover.contents == "Int")
            })
            .expect("a node id that hovers as Int");
        let hover = hover_for_node_id(&ws, &doc, node_id).expect("hover");
        assert_eq!(hover.contents, "Int");
    }

    #[test]
    fn hover_on_a_variant_pattern_shows_the_case() {
        let source = "enum Opt<T> {\n\tcase some(T)\n\tcase none\n}\nlet r = match Opt.some(123) {\n\t.some(x) -> x,\n\t.none -> 0\n}";
        let hover = hover(source, ".some(x)").expect("hover");
        assert!(hover.contents.contains("Opt.some"), "{}", hover.contents);
    }

    #[test]
    fn hover_renders_imported_names_in_bounds() {
        // print's scheme is bounded by core's Showable; the bound must
        // render by name, not as a raw symbol.
        let source = "print(123)";
        let hover = hover(source, "print").expect("hover");
        assert!(hover.contents.contains("Showable"), "{}", hover.contents);
    }

    #[test]
    fn hover_on_a_call_to_a_named_function_shows_its_scheme() {
        let source = "func double(x: Int) -> Int {\n\tx * 2\n}\ndouble(21)";
        let hover = hover(source, "double(21)").expect("hover");
        assert!(
            hover.contents.contains("double") && hover.contents.contains("Int"),
            "{}",
            hover.contents
        );
    }

    #[test]
    fn hover_on_a_literal_shows_its_type() {
        let source = "let a = 21\na";
        let hover = hover(source, "21").expect("hover");
        assert_eq!(hover.contents, "Int");
    }

    #[test]
    fn hover_on_a_let_binding_target_shows_its_type() {
        let source = "let foo = 123\nfoo";
        let hover = hover(source, "foo").expect("hover");
        assert_eq!(hover.contents, "foo: Int");
    }

    #[test]
    fn hover_on_a_local_use_shows_its_type() {
        let source = "let greeting = \"hi\"\ngreeting";
        let offset = source.rfind("greeting").expect("use site") as u32;
        let hover = hover_at(&workspace(source), &"<test>".to_string(), offset).expect("hover");
        assert!(hover.contents.contains("String"), "{}", hover.contents);
    }
}
