//! Hover: the type of the thing under the cursor, rendered from the
//! checker's output tables (`TypeOutput.node_types` for expressions,
//! `schemes` for named binders), plus the doc comments the frontend's
//! documenting parse attached to the resolved declaration
//! (`Workspace.docs`). Every declaration kind has hover content:
//! callable signatures, nominal heads, properties, variants, and
//! initializers. Documentation resolves across workspaces for symbols
//! defined in core or a stdlib module (`hover_at_with`). Serves the
//! wasm `hover` entry point and `talk hover`.

use derive_visitor::{Drive, Visitor};

use crate::analysis::workspace::Workspace;
use crate::analysis::{DocumentId, TextRange, node_ids_at_offset};
use crate::node::Node;
use crate::node_kinds::{decl::Decl, expr::ExprKind, func::Func, pattern::PatternKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hover {
    /// The rendered type or signature.
    pub contents: String,
    /// Doc comments attached to the resolved declaration, rendered as
    /// markdown prose (comment markers stripped).
    pub documentation: Option<String>,
    /// The source range the contents describe.
    pub range: TextRange,
}

/// The workspaces doc comments can resolve through: the module under
/// edit, plus core and stdlib module workspaces for symbols defined
/// outside it (mirroring goto-definition's routing).
pub struct DocWorkspaces<'a> {
    pub module: &'a Workspace,
    pub core: Option<&'a Workspace>,
    pub stdlib: Option<
        &'a dyn Fn(
            crate::compiling::module::ModuleId,
        ) -> Option<std::borrow::Cow<'a, Workspace>>,
    >,
}

/// The hover for the smallest node containing `byte_offset`, walking
/// outward until a node has something to say.
pub fn hover_at(
    workspace: &Workspace,
    document_id: &DocumentId,
    byte_offset: u32,
) -> Option<Hover> {
    hover_at_with(workspace, None, None, document_id, byte_offset)
}

/// [`hover_at`] with cross-workspace doc resolution: symbols defined
/// in core or a stdlib module show that workspace's doc comments.
pub fn hover_at_with<'a>(
    workspace: &'a Workspace,
    core: Option<&'a Workspace>,
    stdlib: Option<
        &'a dyn Fn(
            crate::compiling::module::ModuleId,
        ) -> Option<std::borrow::Cow<'a, Workspace>>,
    >,
    document_id: &DocumentId,
    byte_offset: u32,
) -> Option<Hover> {
    let idx = workspace.document_index(document_id)?;
    let ast = workspace.asts.get(idx)?.as_ref()?;
    let _names =
        crate::name_resolution::symbol::set_symbol_names(workspace.types.display_names.clone());
    let ctx = DocWorkspaces {
        module: workspace,
        core,
        stdlib,
    };

    // The content and the documentation can come from different
    // levels: a member-access segment types the innermost expression
    // while the member resolution (and so the docs) sits on the
    // enclosing access. Documentation therefore walks outward across
    // expressions; any other content node's enclosing nodes are
    // enclosing SCOPES, whose docs are not the hovered thing's.
    let mut found: Option<Hover> = None;
    let mut content_was_expr = false;
    for node_id in node_ids_at_offset(ast, byte_offset) {
        let Some(node) = ast.find(node_id) else {
            continue;
        };
        let is_content_node = found.is_none();
        if is_content_node {
            found = hover_for_node(workspace, &node);
            content_was_expr = matches!(node, Node::Expr(_));
        }
        let Some(hover) = &mut found else {
            continue;
        };
        let may_document =
            is_content_node || (content_was_expr && matches!(node, Node::Expr(_)));
        if hover.documentation.is_none() && may_document {
            hover.documentation = documentation_for_node(&ctx, &node);
        }
        if hover.documentation.is_some() || !content_was_expr {
            return found;
        }
    }
    found
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
    let hover = hover_for_node(workspace, &node)?;
    let ctx = DocWorkspaces {
        module: workspace,
        core: None,
        stdlib: None,
    };
    Some(with_documentation(&ctx, &node, hover))
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
            if let ExprKind::Variable(name) | ExprKind::Constructor(name, ..) = &expr.kind
                && let Ok(symbol) = name.symbol()
                && let Some(hover) = hover_for_symbol(
                    workspace,
                    expr.id,
                    symbol,
                    &name.name_str(),
                    TextRange::new(expr.span.start, expr.span.end),
                    workspace.facts.node_types.get(&expr.id),
                )
            {
                return Some(hover);
            }
            let ty = workspace.facts.node_types.get(&expr.id)?;
            Some(Hover {
                contents: ty.render_mono(),
                documentation: None,
                range: TextRange::new(expr.span.start, expr.span.end),
            })
        }
        Node::Decl(decl) => {
            use crate::node_kinds::decl::DeclKind;
            match &decl.kind {
                DeclKind::Struct {
                    name, name_span, generics, ..
                }
                | DeclKind::Enum {
                    name, name_span, generics, ..
                }
                | DeclKind::Protocol {
                    name, name_span, generics, ..
                } => {
                    let symbol = name.symbol().ok()?;
                    // Heap nominals lead with their provenance; every
                    // other nominal shows its declaration head.
                    if matches!(
                        decl.kind,
                        DeclKind::Struct { .. } | DeclKind::Enum { .. }
                    ) && workspace.types.catalog.heap_origin(symbol).is_some()
                    {
                        return heap_hover(workspace, symbol, name.name_str(), *name_span);
                    }
                    let keyword = match &decl.kind {
                        DeclKind::Struct { .. } => "struct",
                        DeclKind::Enum { .. } => "enum",
                        _ => "protocol",
                    };
                    let contents = nominal_head(workspace, decl, keyword, &name.name_str(), generics);
                    Some(Hover {
                        contents,
                        documentation: None,
                        range: TextRange::new(name_span.start, name_span.end),
                    })
                }
                DeclKind::Property {
                    name, name_span, ..
                } => {
                    let symbol = name.symbol().ok()?;
                    // The declaring nominal's field table carries the
                    // declared type, keyed by the property's symbol.
                    let declared = workspace.types.catalog.structs.values().find_map(|info| {
                        info.fields.iter().find_map(|(field, (field_symbol, ty))| {
                            (*field_symbol == symbol).then(|| format!("{field}: {}", ty.render_mono()))
                        })
                    });
                    Some(Hover {
                        contents: declared.unwrap_or_else(|| name.name_str()),
                        documentation: None,
                        range: TextRange::new(name_span.start, name_span.end),
                    })
                }
                DeclKind::EnumVariant { name, name_span, .. } => {
                    let symbol = name.symbol().ok()?;
                    Some(Hover {
                        contents: variant_contents(workspace, symbol)?,
                        documentation: None,
                        range: TextRange::new(name_span.start, name_span.end),
                    })
                }
                DeclKind::Init { params, .. } => {
                    let file_idx = decl.id.0.0 as usize;
                    let ast = workspace.asts.get(file_idx)?.as_ref()?;
                    let source = workspace.texts.get(file_idx)?.text();
                    let owner = innermost_nominal_covering(ast, decl.span.start, decl.span.end)?;
                    let params_text = params_text(params, source);
                    Some(Hover {
                        contents: format!("init({params_text}) -> {owner}"),
                        documentation: None,
                        // The `init` keyword opens the decl's own span.
                        range: TextRange::new(decl.span.start, decl.span.start + 4),
                    })
                }
                _ => None,
            }
        }
        Node::TypeAnnotation(annotation) => {
            use crate::node_kinds::type_annotation::TypeAnnotationKind;
            let (symbol, name, range) = match &annotation.kind {
                TypeAnnotationKind::Nominal {
                    name, name_span, ..
                } => (
                    name.symbol().ok()?,
                    name.name_str(),
                    TextRange::new(name_span.start, name_span.end),
                ),
                TypeAnnotationKind::SelfType(name) => (
                    name.symbol().ok()?,
                    name.name_str(),
                    TextRange::new(annotation.span.start, annotation.span.end),
                ),
                _ => return None,
            };
            // Heap nominals lead with their provenance; every other
            // nominal shows its declaration head.
            if let Some(hover) = heap_hover_for_range(workspace, symbol, name.clone(), range) {
                return Some(hover);
            }
            Some(Hover {
                contents: catalog_head(workspace, symbol).unwrap_or(name),
                documentation: None,
                range,
            })
        }
        Node::Func(func) => {
            let symbol = func.name.symbol().ok()?;
            let scheme = workspace.types.schemes.get(&symbol)?;
            Some(Hover {
                contents: describe_callable(
                    workspace,
                    func.id,
                    symbol,
                    &func.name.name_str(),
                    scheme,
                    Some(func),
                ),
                documentation: None,
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
                let resolution = workspace.facts.member_resolutions.get(&pattern.id)?;
                let crate::types::output::MemberResolution::Direct(symbol) = resolution else {
                    return None;
                };
                let contents = variant_contents(workspace, *symbol)?;
                Some(Hover {
                    contents,
                    documentation: None,
                    range: TextRange::new(pattern.span.start, pattern.span.end),
                })
            }
            _ => None,
        },
        _ => None,
    }
}

fn heap_hover(
    workspace: &Workspace,
    symbol: crate::name_resolution::symbol::Symbol,
    name: String,
    span: crate::span::Span,
) -> Option<Hover> {
    heap_hover_for_range(
        workspace,
        symbol,
        name,
        TextRange::new(span.start, span.end),
    )
}

/// Attach the resolved declaration's doc comments to a hover, when the
/// workspace parsed the defining document with doc collection.
fn with_documentation(ctx: &DocWorkspaces, node: &Node, hover: Hover) -> Hover {
    match documentation_for_node(ctx, node) {
        Some(documentation) => Hover {
            documentation: Some(documentation),
            ..hover
        },
        None => hover,
    }
}

/// The documentation for a hovered node: declaration nodes look their
/// own span up in the workspace's doc table; references resolve their
/// symbol to its defining declaration first.
fn documentation_for_node(ctx: &DocWorkspaces, node: &Node) -> Option<String> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;
    let workspace = ctx.module;
    match node {
        Node::Decl(decl) => docs_for_decl_span(workspace, decl.id.0.0 as usize, decl.span),
        // A Func node is always the head of a declaration; the doc
        // table keys on the enclosing Decl's span.
        Node::Func(func) => {
            let file_idx = func.id.0.0 as usize;
            let ast = workspace.asts.get(file_idx)?.as_ref()?;
            let (start, end) = node_extent(ast, func.id)?;
            let span = innermost_decl_covering(ast, start, end)?.span;
            docs_for_decl_span(workspace, file_idx, span)
        }
        Node::Expr(expr) => {
            if let ExprKind::Variable(name) | ExprKind::Constructor(name, ..) = &expr.kind {
                return documentation_cross(ctx, name.symbol().ok()?);
            }
            // Member accesses (fields, method calls) resolve through
            // the checker's member table rather than a name.
            match workspace.facts.member_resolutions.get(&expr.id) {
                Some(crate::types::output::MemberResolution::Direct(symbol)) => {
                    documentation_cross(ctx, *symbol)
                }
                Some(crate::types::output::MemberResolution::ViaRequirement {
                    requirement, ..
                }) => documentation_cross(ctx, *requirement),
                Some(crate::types::output::MemberResolution::ViaConformance {
                    witness, ..
                }) => documentation_cross(ctx, *witness),
                _ => None,
            }
        }
        Node::TypeAnnotation(annotation) => {
            let name = match &annotation.kind {
                TypeAnnotationKind::Nominal { name, .. } => name,
                TypeAnnotationKind::SelfType(name) => name,
                _ => return None,
            };
            documentation_cross(ctx, name.symbol().ok()?)
        }
        Node::Pattern(pattern) => match &pattern.kind {
            PatternKind::Bind(name) => documentation_cross(ctx, name.symbol().ok()?),
            PatternKind::Variant { .. } => {
                let resolution = workspace.facts.member_resolutions.get(&pattern.id)?;
                let crate::types::output::MemberResolution::Direct(symbol) = resolution else {
                    return None;
                };
                documentation_cross(ctx, *symbol)
            }
            _ => None,
        },
        _ => None,
    }
}

/// The documentation for a symbol, resolving across workspaces: the
/// module under edit first, then core or the defining stdlib module's
/// workspace (goto-definition's routing; an unbuilt stdlib workspace
/// simply yields no docs this hover).
fn documentation_cross(
    ctx: &DocWorkspaces,
    symbol: crate::name_resolution::symbol::Symbol,
) -> Option<String> {
    if let Some(docs) = docs_for_symbol(ctx.module, symbol) {
        return Some(docs);
    }
    if symbol.module_id() == Some(crate::compiling::module::ModuleId::Core) {
        return ctx.core.and_then(|core| docs_for_symbol(core, symbol));
    }
    if let Some(module_id) = symbol.module_id()
        && ctx.module.stdlib_module_ids.contains_key(&module_id)
        && let Some(stdlib) = ctx.stdlib
        && let Some(workspace) = stdlib(module_id)
    {
        return docs_for_symbol(&workspace, symbol);
    }
    None
}

/// The documentation for a symbol's defining declaration. Parameters
/// and generic parameters are not documentable; patterns resolve to
/// their innermost enclosing declaration, which self-selects against
/// locals: only file-level and nominal-member declarations carry doc
/// entries.
fn docs_for_symbol(
    workspace: &Workspace,
    symbol: crate::name_resolution::symbol::Symbol,
) -> Option<String> {
    let Some(def_node) = workspace.resolved_names.symbols_to_node.get(&symbol).copied() else {
        // Requirement symbols never enter symbols_to_node; find the
        // requirement's declaration by scanning for its signature.
        return docs_for_requirement(workspace, symbol);
    };
    let file_idx = def_node.0.0 as usize;
    let ast = workspace.asts.get(file_idx)?.as_ref()?;
    // Node kinds without a dedicated path below — requirements and
    // other declarations `find` does not walk — still key the doc
    // table by their own span from the meta table.
    let meta_span = || {
        ast.meta.get(&def_node).map(|meta| crate::span::Span {
            file_id: def_node.0,
            start: meta.start.start,
            end: meta.end.end,
        })
    };
    let span = match ast.find(def_node) {
        Some(Node::Decl(decl)) => decl.span,
        Some(Node::Func(func)) => {
            let (start, end) = node_extent(ast, func.id)?;
            innermost_decl_covering(ast, start, end)?.span
        }
        Some(Node::Pattern(pattern)) => {
            // The pattern must head the declaration being documented:
            // a covering `let`. A local bind's innermost covering
            // decl is the enclosing function, whose docs are not the
            // binding's.
            let decl = innermost_decl_covering(ast, pattern.span.start, pattern.span.end)?;
            if !matches!(decl.kind, crate::node_kinds::decl::DeclKind::Let { .. }) {
                return None;
            }
            decl.span
        }
        // A requirement's definition node is its FuncSignature; the
        // doc table keys on the enclosing requirement declaration.
        Some(Node::FuncSignature(signature)) => {
            innermost_decl_covering(ast, signature.span.start, signature.span.end)?.span
        }
        Some(_) => meta_span()?,
        None => meta_span()?,
    };
    docs_for_decl_span(workspace, file_idx, span)
}

/// A node's full byte extent from the AST's meta table (Func nodes
/// carry no span of their own).
fn node_extent(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    node_id: crate::node_id::NodeID,
) -> Option<(u32, u32)> {
    let meta = ast.meta.get(&node_id)?;
    Some((meta.start.start, meta.end.end))
}

/// Requirement symbols are not in `symbols_to_node`; the
/// documentation for a protocol requirement resolves by scanning for
/// the requirement declaration whose signature names the symbol.
fn docs_for_requirement(
    workspace: &Workspace,
    symbol: crate::name_resolution::symbol::Symbol,
) -> Option<String> {
    for (file_idx, ast) in workspace.asts.iter().enumerate() {
        let Some(ast) = ast else { continue };
        let mut finder = RequirementDeclFinder {
            symbol,
            found: None,
        };
        for root in &ast.roots {
            root.drive(&mut finder);
            if finder.found.is_some() {
                break;
            }
        }
        if let Some(span) = finder.found {
            return docs_for_decl_span(workspace, file_idx, span);
        }
    }
    None
}

#[derive(Visitor)]
#[visitor(Decl(enter))]
struct RequirementDeclFinder {
    symbol: crate::name_resolution::symbol::Symbol,
    found: Option<crate::span::Span>,
}

impl RequirementDeclFinder {
    fn enter_decl(&mut self, decl: &Decl) {
        use crate::node_kinds::decl::DeclKind;
        if self.found.is_some() {
            return;
        }
        let matches = match &decl.kind {
            DeclKind::MethodRequirement { signature, .. } => {
                signature.name.symbol().ok() == Some(self.symbol)
            }
            DeclKind::InitRequirement { signature, .. } => {
                signature.name.symbol().ok() == Some(self.symbol)
            }
            _ => false,
        };
        if matches {
            self.found = Some(decl.span);
        }
    }
}

/// The doc comment group attached to the declaration with this exact
/// byte span, rendered as markdown text: the `//` marker and one
/// leading space or tab stripped from each line.
fn docs_for_decl_span(
    workspace: &Workspace,
    file_idx: usize,
    span: crate::span::Span,
) -> Option<String> {
    let entry = workspace
        .docs
        .get(file_idx)?
        .iter()
        .find(|doc| doc.decl_start == span.start && doc.decl_end == span.end)?;
    let source = workspace.texts.get(file_idx)?.text();
    let mut lines = Vec::new();
    for &(comment_start, comment_end) in &entry.comments {
        let raw = source.get(comment_start as usize..comment_end as usize)?;
        let body = raw.strip_prefix("//").unwrap_or(raw);
        let body = body
            .strip_prefix(' ')
            .or_else(|| body.strip_prefix('\t'))
            .unwrap_or(body);
        lines.push(body);
    }
    let documentation = lines.join("\n");
    (!documentation.trim().is_empty()).then_some(documentation)
}

#[derive(Visitor)]
#[visitor(Decl(enter))]
struct InnermostDeclCovering {
    start: u32,
    end: u32,
    found: Option<Decl>,
}

impl InnermostDeclCovering {
    fn enter_decl(&mut self, decl: &Decl) {
        if decl.span.start <= self.start && self.end <= decl.span.end {
            // Pre-order enters outer decls first; each nested hit is
            // smaller, so the last one standing is the innermost.
            self.found = Some(decl.clone());
        }
    }
}

fn innermost_decl_covering(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    start: u32,
    end: u32,
) -> Option<Decl> {
    let mut finder = InnermostDeclCovering {
        start,
        end,
        found: None,
    };
    for root in &ast.roots {
        root.drive(&mut finder);
    }
    finder.found
}

/// `StructName<T>` / `EnumName` / `ProtocolName` for a nominal
/// symbol, rendered from the catalog (no source text needed).
fn catalog_head(
    workspace: &Workspace,
    symbol: crate::name_resolution::symbol::Symbol,
) -> Option<String> {
    use crate::types::ty::ParamKind;
    let catalog = &workspace.types.catalog;
    let (keyword, name, params) = if let Some(info) = catalog.structs.get(&symbol) {
        ("struct", display_name(workspace, &symbol)?, &info.params)
    } else if let Some(info) = catalog.enums.get(&symbol) {
        ("enum", display_name(workspace, &symbol)?, &info.params)
    } else {
        let info = catalog.protocols.get(&symbol)?;
        ("protocol", display_name(workspace, &symbol)?, &info.params)
    };
    if params.is_empty() {
        return Some(format!("{keyword} {name}"));
    }
    let rendered: Vec<String> = params
        .iter()
        .map(|param| {
            let param_name = workspace
                .types
                .display_names
                .get(&param.symbol)
                .cloned()
                .unwrap_or_else(|| "T".to_string());
            match &param.kind {
                ParamKind::Type => param_name,
                ParamKind::Static(ty) => format!("static {param_name}: {}", ty.render_mono()),
            }
        })
        .collect();
    Some(format!("{keyword} {name}<{}>", rendered.join(", ")))
}

fn display_name(
    workspace: &Workspace,
    symbol: &crate::name_resolution::symbol::Symbol,
) -> Option<String> {
    workspace
        .types
        .display_names
        .get(symbol)
        .cloned()
        .or_else(|| Some(symbol.to_string()))
}

/// The declaration head: `struct Greeter`, `enum Opt<T>`,
/// `protocol Showable<T>`. Generics render from the source text so
/// static value parameters keep their declared types.
fn nominal_head(
    workspace: &Workspace,
    decl: &Decl,
    keyword: &str,
    name: &str,
    generics: &[crate::node_kinds::generic_decl::GenericDecl],
) -> String {
    let file_idx = decl.id.0.0 as usize;
    let source = workspace
        .texts
        .get(file_idx)
        .map(|text| text.text())
        .unwrap_or("");
    format!(
        "{keyword} {name}{}",
        generic_params_text(generics, source)
    )
}

fn generic_params_text(
    generics: &[crate::node_kinds::generic_decl::GenericDecl],
    source: &str,
) -> String {
    if generics.is_empty() {
        return String::new();
    }
    let rendered: Vec<String> = generics
        .iter()
        .map(|generic| {
            let name = generic.name.name_str();
            match &generic.static_ty {
                Some(annotation) => {
                    let ty = source
                        .get(annotation.span.start as usize..annotation.span.end as usize)
                        .unwrap_or("");
                    format!("static {name}: {ty}")
                }
                None => name,
            }
        })
        .collect();
    format!("<{}>", rendered.join(", "))
}

/// `Enum.case` or `Enum.case(Payload, ...)` for a variant symbol.
fn variant_contents(
    workspace: &Workspace,
    symbol: crate::name_resolution::symbol::Symbol,
) -> Option<String> {
    let (enum_name, case, payloads) =
        workspace
            .types
            .catalog
            .enums
            .iter()
            .find_map(|(owner, info)| {
                info.variants.iter().find_map(|(case, variant)| {
                    (variant.symbol == symbol).then(|| {
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
    if payloads.is_empty() {
        Some(format!("{enum_name}.{case}"))
    } else {
        let payloads: Vec<String> = payloads.iter().map(|ty| ty.render_mono()).collect();
        Some(format!("{enum_name}.{case}({})", payloads.join(", ")))
    }
}

/// `x: Int, y: String` — a parameter list rendered from the source
/// text (used where no scheme exists, e.g. initializers). The
/// initializer's implicit leading `self` is not a source parameter.
fn params_text(params: &[crate::node_kinds::parameter::Parameter], source: &str) -> String {
    params
        .iter()
        .filter(|param| param.name.name_str() != "self")
        .map(|param| match &param.type_annotation {
            Some(annotation) => {
                let ty = source
                    .get(annotation.span.start as usize..annotation.span.end as usize)
                    .unwrap_or("");
                format!("{}: {ty}", param.name.name_str())
            }
            None => param.name.name_str(),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

#[derive(Visitor)]
#[visitor(Decl(enter))]
struct InnermostNominalCovering {
    start: u32,
    end: u32,
    found: Option<String>,
}

impl InnermostNominalCovering {
    fn enter_decl(&mut self, decl: &Decl) {
        use crate::node_kinds::decl::DeclKind;
        let name = match &decl.kind {
            DeclKind::Struct { name, .. } | DeclKind::Enum { name, .. } => name,
            _ => return,
        };
        if decl.span.start <= self.start && self.end <= decl.span.end {
            // Pre-order enters outer decls first; the last nominal
            // standing is the innermost.
            self.found = Some(name.name_str());
        }
    }
}

/// The name of the innermost struct or enum whose body contains the
/// span (the owning nominal of a member declaration).
fn innermost_nominal_covering(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    start: u32,
    end: u32,
) -> Option<String> {
    let mut finder = InnermostNominalCovering {
        start,
        end,
        found: None,
    };
    for root in &ast.roots {
        root.drive(&mut finder);
    }
    finder.found
}

fn heap_hover_for_range(
    workspace: &Workspace,
    symbol: crate::name_resolution::symbol::Symbol,
    name: String,
    range: TextRange,
) -> Option<Hover> {
    let origin = workspace.types.catalog.heap_origin(symbol)?;
    let qualifier = match origin {
        crate::types::catalog::HeapOrigin::Explicit => "'heap",
        crate::types::catalog::HeapOrigin::RecursiveLayout => {
            "'heap (inferred from recursive layout)"
        }
    };
    Some(Hover {
        contents: format!("{name} {qualifier}\n\nreference semantics, region-allocated"),
        documentation: None,
        range,
    })
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
            contents: describe_callable(workspace, node, symbol, name, scheme, None),
            documentation: None,
            range,
        });
    }

    if let Some(ty) = workspace.types.local_tys.get(&symbol).or(fallback_ty) {
        return Some(Hover {
            contents: format!("{name}: {}", ty.render_mono()),
            documentation: None,
            range,
        });
    }

    None
}

fn describe_callable(
    workspace: &Workspace,
    node: crate::node_id::NodeID,
    symbol: crate::name_resolution::symbol::Symbol,
    name: &str,
    scheme: &crate::types::ty::Scheme,
    source: Option<&crate::node_kinds::func::Func>,
) -> String {
    let resolved_source = source_func(workspace, symbol);
    let source = source.or(resolved_source.as_ref());
    let signature = source.map_or_else(
        || format!("{name}: {}", scheme.render()),
        |func| {
            let params: Vec<(String, String)> = func
                .params
                .iter()
                .map(|param| {
                    let mode = param
                        .mode
                        .unwrap_or(crate::node_kinds::parameter::ParamMode::Borrow);
                    (param.name.name_str(), mode.keyword().to_string())
                })
                .collect();
            scheme.render_callable(name, &params)
        },
    );
    let display_names = scheme.display_param_names();
    let mut details = vec![];
    for param in &scheme.params {
        let Some(origin) = workspace.types.inferred_param_origins.get(&param.symbol) else {
            continue;
        };
        let display = display_names
            .get(&param.symbol)
            .cloned()
            .unwrap_or_else(|| "T".to_string());
        let source = workspace
            .asts
            .get(origin.0.0 as usize)
            .and_then(Option::as_ref)
            .and_then(|ast| ast.find(*origin))
            .and_then(|node| match node {
                Node::Parameter(param) => Some(param.name.name_str()),
                _ => None,
            });
        match source {
            Some(source) => details.push(format!(
                "{display} is an inferred generic parameter introduced by {source}."
            )),
            None => details.push(format!("{display} is an inferred generic parameter.")),
        }
        let constrained = scheme.predicates.iter().any(|predicate| {
            let mut found = false;
            let _ = predicate.try_visit::<()>(&mut |ty| {
                if matches!(ty, crate::types::ty::Ty::Param(symbol) if *symbol == param.symbol) {
                    found = true;
                    std::ops::ControlFlow::Break(())
                } else {
                    std::ops::ControlFlow::Continue(())
                }
            });
            found
        });
        if !constrained {
            details.push(format!("{display} has no constraints."));
        }
    }

    if let Some(instantiation) = workspace.facts.instantiations.get(&node) {
        let substitutions: Vec<_> = instantiation
            .iter()
            .filter(|(param, ty)| {
                scheme
                    .params
                    .iter()
                    .any(|scheme_param| scheme_param.symbol == *param)
                    && !matches!(
                        ty,
                        crate::types::ty::Ty::Var(_) | crate::types::ty::Ty::Error
                    )
            })
            .collect();
        if !substitutions.is_empty() {
            details.push("This call:".to_string());
            for (param, ty) in &substitutions {
                let display = display_names
                    .get(param)
                    .cloned()
                    .unwrap_or_else(|| "T".to_string());
                details.push(format!("  {display} = {}", ty.render_mono()));
            }
            let tys = substitutions
                .iter()
                .map(|entry| (entry.0, entry.1.clone()))
                .collect();
            let instantiated = scheme
                .ty
                .substitute(&tys, &Default::default(), &Default::default());
            if let crate::types::ty::Ty::Func(_, ret, _) = instantiated {
                details.push(format!("  returns {}", ret.render_mono()));
            }
        }
    }

    if details.is_empty() {
        signature
    } else {
        format!("{signature}\n\n{}", details.join("\n"))
    }
}

fn source_func(
    workspace: &Workspace,
    symbol: crate::name_resolution::symbol::Symbol,
) -> Option<crate::node_kinds::func::Func> {
    for ast in workspace.asts.iter().flatten() {
        let mut finder = SourceFuncFinder {
            symbol,
            found: None,
        };
        for root in &ast.roots {
            root.drive(&mut finder);
            if finder.found.is_some() {
                return finder.found;
            }
        }
    }
    None
}

#[derive(Visitor)]
#[visitor(Func(enter))]
struct SourceFuncFinder {
    symbol: crate::name_resolution::symbol::Symbol,
    found: Option<crate::node_kinds::func::Func>,
}

impl SourceFuncFinder {
    fn enter_func(&mut self, func: &crate::node_kinds::func::Func) {
        if self.found.is_none() && func.name.symbol().ok() == Some(self.symbol) {
            self.found = Some(func.clone());
        }
    }
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
            text: source.into(),
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
    fn hover_shows_inferred_recursive_heap_provenance() {
        let source = "// no-core\nenum Tree {\n\tcase leaf(Int)\n\tcase branch(Tree, Tree)\n}";
        let declaration = hover(source, "Tree {").expect("declaration hover");
        assert!(
            declaration
                .contents
                .contains("'heap (inferred from recursive layout)"),
            "{}",
            declaration.contents
        );
        assert!(
            declaration
                .contents
                .contains("reference semantics, region-allocated"),
            "{}",
            declaration.contents
        );

        let occurrence = hover(source, "Tree, Tree").expect("type occurrence hover");
        assert!(
            occurrence
                .contents
                .contains("'heap (inferred from recursive layout)"),
            "{}",
            occurrence.contents
        );
    }

    #[test]
    fn hover_shows_explicit_heap_provenance() {
        let source = "// no-core\nstruct Box 'heap {\n\tlet value: Int\n}";
        let declaration = hover(source, "Box 'heap").expect("declaration hover");
        assert!(declaration.contents.contains("Box 'heap"), "{}", declaration.contents);
        assert!(
            !declaration.contents.contains("inferred"),
            "{}",
            declaration.contents
        );
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
    fn hover_marks_static_parameters() {
        let source = "func width<static N: Int>() -> Int {\n\tN\n}\nwidth<4>()";
        let hover = hover(source, "width<4>").expect("hover");
        assert!(
            hover.contents.contains("static N: Int"),
            "{}",
            hover.contents
        );
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
    fn hover_explains_inferred_generics_and_call_instantiations() {
        let source = "// no-core\nfunc id(x) { x }\nlet value = id(42)";
        let declaration = hover(source, "id(x)").expect("declaration hover");
        assert!(
            declaration
                .contents
                .contains("func id<X>(borrow x: X) -> &X")
                && declaration
                    .contents
                    .contains("X is an inferred generic parameter introduced by x."),
            "{}",
            declaration.contents
        );

        let call = hover(source, "id(42)").expect("call hover");
        assert!(
            call.contents.contains("X = Int") && call.contents.contains("returns &Int"),
            "{}",
            call.contents
        );
    }

    #[test]
    fn hover_uses_talk_effect_syntax_without_internal_effect_indices() {
        let source = "// no-core\neffect 'ping() -> ()\nstruct Wrapper { let f: () -> Int }\nfunc make() { Wrapper(f: func() { 'ping(); 1 }) }";
        let wrapper = hover(source, "Wrapper(f:").expect("wrapper hover");
        assert!(wrapper.contents.contains("'ping"), "{}", wrapper.contents);
        assert!(!wrapper.contents.contains("! <"), "{}", wrapper.contents);
        assert!(
            !wrapper.contents.contains("TypeParameter("),
            "{}",
            wrapper.contents
        );
    }

    #[test]
    fn hover_on_a_documented_function_declaration_shows_its_docs() {
        let source = "// Doubles its input.\n// Pure.\nfunc double(x: Int) -> Int {\n\tx * 2\n}\ndouble(21)";
        let declaration = hover(source, "double(x: Int").expect("declaration hover");
        assert_eq!(
            declaration.documentation.as_deref(),
            Some("Doubles its input.\nPure.")
        );

        let call = hover(source, "double(21)").expect("call hover");
        assert_eq!(
            call.documentation.as_deref(),
            Some("Doubles its input.\nPure."),
            "use sites resolve to the same declaration"
        );
    }

    #[test]
    fn hover_on_a_documented_member_shows_its_docs() {
        let source = "struct Greeter {\n\t// The greeting to offer.\n\tlet greeting: String\n\n\t// Says hello.\n\tfunc greet() {\n\t\tprint(greeting)\n\t}\n}\nlet g = Greeter(greeting: \"hi\")\ng.greeting";
        let property = hover(source, ".greeting").expect("property use hover");
        assert_eq!(
            property.documentation.as_deref(),
            Some("The greeting to offer.")
        );
    }

    #[test]
    fn hover_on_a_documented_type_shows_its_docs_at_the_use_site() {
        let source = "// A tree of ints.\nenum Tree {\n\tcase leaf(Int)\n\tcase branch(Tree, Tree)\n}\nlet t: Tree = Tree.leaf(1)";
        let declaration = hover(source, "Tree {").expect("declaration hover");
        assert_eq!(declaration.documentation.as_deref(), Some("A tree of ints."));
        let use_site = hover(source, "Tree =").expect("annotation hover");
        assert_eq!(use_site.documentation.as_deref(), Some("A tree of ints."));
    }

    #[test]
    fn hover_on_a_local_does_not_leak_the_enclosing_functions_docs() {
        let source = "// Documented.\nfunc f() -> Int {\n\tlet local = 21\n\tlocal\n}";
        let hover = hover(source, "local\n}").expect("local use hover");
        assert_eq!(hover.documentation, None, "{hover:?}");
    }

    #[test]
    fn hover_on_an_undocumented_declaration_has_no_docs() {
        let source = "func double(x: Int) -> Int {\n\tx * 2\n}\ndouble(21)";
        let declaration = hover(source, "double(x: Int").expect("declaration hover");
        assert_eq!(declaration.documentation, None);
    }

    #[test]
    fn hover_on_a_plain_struct_declaration_shows_the_head_and_docs() {
        let source = "// A greeter.\nstruct Greeter {\n\tlet greeting: String\n}";
        let hover = hover(source, "Greeter {").expect("declaration hover");
        assert_eq!(hover.contents, "struct Greeter");
        assert_eq!(hover.documentation.as_deref(), Some("A greeter."));
    }

    #[test]
    fn hover_on_a_generic_enum_declaration_shows_the_head() {
        let source = "enum Opt<T> {\n\tcase some(T)\n\tcase none\n}";
        let hover = hover(source, "Opt<T> {").expect("declaration hover");
        assert_eq!(hover.contents, "enum Opt<T>");
    }

    #[test]
    fn hover_on_a_protocol_declaration_shows_the_head_and_docs() {
        let source = "// Describes values.\nprotocol Describable {\n\tfunc describe() -> String\n}";
        let hover = hover(source, "Describable {").expect("declaration hover");
        assert_eq!(hover.contents, "protocol Describable");
        assert_eq!(hover.documentation.as_deref(), Some("Describes values."));
    }

    #[test]
    fn hover_on_a_property_declaration_shows_its_type_and_docs() {
        let source = "struct Greeter {\n\t// The greeting to offer.\n\tlet greeting: String\n}";
        let hover = hover(source, "greeting: String").expect("declaration hover");
        assert_eq!(hover.contents, "greeting: String");
        assert_eq!(
            hover.documentation.as_deref(),
            Some("The greeting to offer.")
        );
    }

    #[test]
    fn hover_on_a_variant_declaration_shows_the_case_and_docs() {
        let source = "enum Opt<T> {\n\t// A present value.\n\tcase some(T)\n\tcase none\n}";
        let hover = hover(source, "some(T)").expect("declaration hover");
        assert_eq!(hover.contents, "Opt.some(T)");
        assert_eq!(hover.documentation.as_deref(), Some("A present value."));
    }

    #[test]
    fn hover_on_an_init_declaration_shows_the_signature_and_docs() {
        let source = "struct Dog {\n\tlet age: Int\n\n\t// Makes a dog of an age.\n\tinit(age: Int) {\n\t\tself.age = age\n\t\tself\n\t}\n}";
        let hover = hover(source, "init(age: Int)").expect("declaration hover");
        assert_eq!(hover.contents, "init(age: Int) -> Dog");
        assert_eq!(
            hover.documentation.as_deref(),
            Some("Makes a dog of an age.")
        );
    }

    #[test]
    fn hover_on_a_protocol_method_call_shows_the_requirements_docs() {
        let source = "protocol Describable {\n\t// Describes the value.\n\tfunc describe() -> String\n}\nfunc show_it<T: Describable>(x: T) -> String {\n\tx.describe()\n}";
        let hover = hover(source, ".describe()").expect("requirement call hover");
        assert_eq!(
            hover.documentation.as_deref(),
            Some("Describes the value."),
            "{hover:?}"
        );
    }

    #[test]
    fn hover_on_an_extension_method_call_shows_the_witnesss_docs() {
        let source = "protocol Describable {\n\tfunc describe() -> String\n}\nstruct Thing {\n\tlet n: Int\n}\nextend Thing: Describable {\n\t// The thing's own description.\n\tfunc describe() -> String {\n\t\t\"thing\"\n\t}\n}\nfunc f(t: Thing) -> String {\n\tt.describe()\n}";
        let hover = hover(source, ".describe()").expect("witness call hover");
        assert_eq!(
            hover.documentation.as_deref(),
            Some("The thing's own description."),
            "{hover:?}"
        );
    }

    #[test]
    fn hover_on_a_core_type_shows_core_docs() {
        let source = "func f<T: Copy>(x: T) -> T { x }";
        let ws = workspace(source);
        let core = Workspace::core().expect("core workspace");
        let offset = source.find("Copy").expect("conformance") as u32;
        let hover = hover_at_with(
            &ws,
            Some(&core),
            None,
            &"<test>".to_string(),
            offset,
        )
        .expect("hover");
        assert_eq!(hover.contents, "protocol Copy");
        assert!(
            hover
                .documentation
                .as_deref()
                .is_some_and(|docs| docs.contains("duplicates freely")),
            "{hover:?}"
        );
    }

    #[test]
    fn hover_on_a_stdlib_function_shows_the_modules_docs() {
        let source = "use task::{ run_blocking }\nlet f = run_blocking";
        let ws = workspace(source);
        let (module_id, _) = ws
            .stdlib_module_ids
            .iter()
            .find(|(_, name)| name.as_str() == "task")
            .expect("task module activated by the import");
        let task = ws
            .stdlib_workspace_for_module_id(*module_id)
            .expect("task workspace");
        let offset = source.rfind("run_blocking").expect("use site") as u32;
        let stdlib = |_: crate::compiling::module::ModuleId| {
            Some(std::borrow::Cow::Borrowed(&task))
        };
        let hover = hover_at_with(&ws, None, Some(&stdlib), &"<test>".to_string(), offset)
            .expect("hover");
        assert!(
            hover
                .documentation
                .as_deref()
                .is_some_and(|docs| docs.contains("root fallbacks")),
            "{hover:?}"
        );
    }

    #[test]
    fn hover_on_a_literal_shows_its_type() {
        let source = "let a = 21\na";
        let hover = hover(source, "21").expect("hover");
        assert_eq!(hover.contents, "Int");
    }

    #[test]
    fn hover_on_string_add_shows_the_concrete_alloc_effect() {
        let source = "let value = \"a\".add(\"b\")\nvalue";
        let hover = hover(source, "add").expect("hover");
        assert!(hover.contents.contains("'alloc"), "{}", hover.contents);
    }

    #[test]
    fn string_add_cannot_flow_into_a_pure_function() {
        let source = "func concatenate() '[] -> String {\n\t\"a\".add(\"b\")\n}";
        let workspace = workspace(source);
        let diagnostics = workspace
            .diagnostics
            .get("<test>")
            .cloned()
            .unwrap_or_default();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("'alloc")),
            "{diagnostics:?}"
        );
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
