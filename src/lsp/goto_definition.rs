use async_lsp::lsp_types::{Location, Position, Range, Url};

use crate::analysis::workspace::Workspace as AnalysisWorkspace;
use crate::analysis::{node_ids_at_offset, span_contains};
use crate::compiling::{module::ModuleId, module_path::LocalModulePaths};
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
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|a| a.as_ref())?;

    // Handle imports specially (need AST to get import path for file navigation)
    for (node_id, meta) in ast.meta.iter() {
        if meta.start.start <= byte_offset
            && byte_offset <= meta.end.end
            && let Some(crate::node::Node::Decl(ref decl)) = ast.find(*node_id)
            && let Some(location) = goto_definition_from_import(module, uri, decl, byte_offset)
        {
            return Some(location);
        }
    }

    // Use AST-based lookup
    let candidate_ids = node_ids_at_offset(ast, byte_offset);

    for node_id in candidate_ids {
        let Some(node) = ast.find(node_id) else {
            continue;
        };

        let symbol = match node {
            crate::node::Node::Expr(expr) => {
                goto_definition_symbol_from_expr(module, &expr, byte_offset)
            }
            crate::node::Node::Stmt(stmt) => {
                goto_definition_symbol_from_stmt(module, &stmt, byte_offset)
            }
            crate::node::Node::TypeAnnotation(ty) => {
                goto_definition_symbol_from_type_annotation(&ty, byte_offset)
            }
            crate::node::Node::Decl(decl) => goto_definition_symbol_from_decl(&decl, byte_offset),
            crate::node::Node::Parameter(param) => {
                if span_contains(param.name_span, byte_offset) {
                    param.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::Func(func) => {
                if span_contains(func.name_span, byte_offset) {
                    func.name.symbol().ok()
                } else {
                    effect_symbol_at_offset(&func.effects, byte_offset)
                }
            }
            crate::node::Node::FuncSignature(sig) => {
                let meta = ast.meta.get(&sig.id)?;
                let (start, end) = meta.identifiers.first().map(|t| (t.start, t.end))?;
                if start <= byte_offset && byte_offset <= end {
                    sig.name.symbol().ok()
                } else {
                    effect_symbol_at_offset(&sig.effects, byte_offset)
                }
            }
            crate::node::Node::GenericDecl(generic) => {
                if span_contains(generic.name_span, byte_offset) {
                    generic.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::Pattern(pattern) => match &pattern.kind {
                crate::node_kinds::pattern::PatternKind::Bind(name) => {
                    let meta = ast.meta.get(&pattern.id)?;
                    let (start, end) = identifier_span_at_offset(meta, byte_offset)?;
                    if start <= byte_offset && byte_offset <= end {
                        name.symbol().ok()
                    } else {
                        None
                    }
                }
                // The checker records each variant pattern's resolution
                // (member_resolutions, keyed by the pattern node).
                crate::node_kinds::pattern::PatternKind::Variant { .. } => {
                    match module.types.member_resolutions.get(&pattern.id) {
                        Some(crate::types::output::MemberResolution::Direct(symbol)) => {
                            Some(*symbol)
                        }
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        };

        if let Some(symbol) = symbol
            && let Some(target) = definition_location_for_symbol(module, core, symbol)
        {
            return Some(target);
        }
    }

    // Log a miss so we can identify remaining gaps
    let candidate_ids = node_ids_at_offset(ast, byte_offset);
    let node_descriptions: Vec<String> = candidate_ids
        .iter()
        .filter_map(|id| ast.find(*id))
        .map(|n| describe_node(&n))
        .collect();
    log_miss("goto-def", uri, byte_offset, &node_descriptions);

    None
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
        return match &import.path {
            crate::node_kinds::decl::ImportPath::Local(_) => {
                let target_path = resolve_import_path(&module.source_root, uri, &import.path)?;
                let target_uri = Url::from_file_path(&target_path).ok()?;
                Some(Location {
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
                })
            }
            crate::node_kinds::decl::ImportPath::Package(package) => {
                let stdlib = module.stdlib_workspace_for_package(package)?;
                module_start_location(&stdlib)
            }
        };
    }

    // Check if cursor is on an imported symbol - navigate to its definition
    if let ImportedSymbols::Named(symbols) = &import.symbols {
        for imported in symbols {
            if span_contains(imported.span, byte_offset) {
                match &import.path {
                    crate::node_kinds::decl::ImportPath::Local(_) => {
                        // Find the target file and look up the symbol there
                        let target_path =
                            resolve_import_path(&module.source_root, uri, &import.path)?;
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
                    crate::node_kinds::decl::ImportPath::Package(package) => {
                        let stdlib = module.stdlib_workspace_for_package(package)?;
                        let target_scope_id = crate::node_id::NodeID(crate::node_id::FileID(0), 0);
                        let target_scope = stdlib.resolved_names.scopes.get(&target_scope_id)?;
                        let symbol = target_scope
                            .types
                            .get(&imported.name)
                            .or_else(|| target_scope.values.get(&imported.name))?;

                        return definition_location_in_module(&stdlib, *symbol);
                    }
                }
            }
        }
    }

    None
}

fn module_start_location(module: &AnalysisWorkspace) -> Option<Location> {
    let doc_id = module.file_id_to_document.first()?;
    let uri = url_from_document_id(doc_id)?;
    Some(Location {
        uri,
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
    })
}

/// Resolve an import path relative to the importing file's URI.
fn resolve_import_path(
    source_root: &std::path::Path,
    uri: &Url,
    import_path: &crate::node_kinds::decl::ImportPath,
) -> Option<std::path::PathBuf> {
    use crate::node_kinds::decl::ImportPath;

    match import_path {
        ImportPath::Local(module_path) => {
            let source_path = uri.to_file_path().ok()?;
            LocalModulePaths::new(source_root).resolve(&source_path.to_string_lossy(), module_path)
        }
        ImportPath::Package(_) => {
            // Package imports not yet supported for go-to-definition
            None
        }
    }
}

fn goto_definition_symbol_from_expr(
    module: &AnalysisWorkspace,
    expr: &crate::node_kinds::expr::Expr,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::expr::ExprKind;

    match &expr.kind {
        ExprKind::Variable(name) | ExprKind::Constructor(name) => name.symbol().ok(),
        ExprKind::Call { callee, .. } => {
            goto_definition_symbol_from_expr(module, callee, byte_offset)
        }
        ExprKind::Member(_, _, label_span) => {
            if !span_contains(*label_span, byte_offset) {
                return None;
            }
            symbol_for_member_resolution(module.types.member_resolutions.get(&expr.id))
        }
        ExprKind::CallEffect {
            effect_name,
            effect_name_span,
            ..
        } => {
            if !effect_span_contains(*effect_name_span, byte_offset) {
                return None;
            }
            effect_name.symbol().ok()
        }
        _ => None,
    }
}

fn symbol_for_member_resolution(
    resolution: Option<&crate::types::output::MemberResolution>,
) -> Option<Symbol> {
    match resolution? {
        crate::types::output::MemberResolution::Direct(symbol) => Some(*symbol),
        crate::types::output::MemberResolution::ViaConformance { witness, .. } => Some(*witness),
    }
}

fn goto_definition_symbol_from_stmt(
    module: &AnalysisWorkspace,
    stmt: &crate::node_kinds::stmt::Stmt,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::stmt::StmtKind;

    match &stmt.kind {
        StmtKind::Expr(expr) => goto_definition_symbol_from_expr(module, expr, byte_offset),
        StmtKind::Return(Some(expr)) => goto_definition_symbol_from_expr(module, expr, byte_offset),
        StmtKind::If(cond, ..) => goto_definition_symbol_from_expr(module, cond, byte_offset),
        StmtKind::Loop(Some(cond), ..) => {
            goto_definition_symbol_from_expr(module, cond, byte_offset)
        }
        StmtKind::Assignment(lhs, rhs) => {
            goto_definition_symbol_from_expr(module, lhs, byte_offset)
                .or_else(|| goto_definition_symbol_from_expr(module, rhs, byte_offset))
        }
        StmtKind::Handling {
            effect_name,
            effect_name_span,
            ..
        } => {
            if !effect_span_contains(*effect_name_span, byte_offset) {
                return None;
            }
            effect_name.symbol().ok()
        }
        StmtKind::Continue(Some(expr)) => {
            goto_definition_symbol_from_expr(module, expr, byte_offset)
        }
        _ => None,
    }
}

fn goto_definition_symbol_from_type_annotation(
    ty: &crate::node_kinds::type_annotation::TypeAnnotation,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    match &ty.kind {
        TypeAnnotationKind::Borrow { inner, .. } | TypeAnnotationKind::Unique { inner } => {
            goto_definition_symbol_from_type_annotation(inner, byte_offset)
        }
        TypeAnnotationKind::Nominal {
            name,
            name_span,
            generics,
        } => generics
            .iter()
            .flat_map(|generic| generic.annotations())
            .find_map(|generic| goto_definition_symbol_from_type_annotation(generic, byte_offset))
            .or_else(|| {
                nominal_name_span_contains(name, *name_span, byte_offset)
                    .then(|| name.symbol().ok())
                    .flatten()
            }),
        TypeAnnotationKind::SelfType(name) => name.symbol().ok(),
        TypeAnnotationKind::Any {
            protocol,
            assoc_bindings,
        } => goto_definition_symbol_from_type_annotation(protocol, byte_offset).or_else(|| {
            assoc_bindings.iter().find_map(|binding| {
                goto_definition_symbol_from_type_annotation(&binding.value, byte_offset)
            })
        }),
        TypeAnnotationKind::Func {
            params,
            effects,
            returns,
        } => params
            .iter()
            .find_map(|param| goto_definition_symbol_from_type_annotation(param, byte_offset))
            .or_else(|| effect_symbol_at_offset(effects, byte_offset))
            .or_else(|| goto_definition_symbol_from_type_annotation(returns, byte_offset)),
        TypeAnnotationKind::NominalPath { base, .. } => {
            goto_definition_symbol_from_type_annotation(base, byte_offset)
        }
        TypeAnnotationKind::Tuple(items) => items
            .iter()
            .find_map(|item| goto_definition_symbol_from_type_annotation(item, byte_offset)),
        TypeAnnotationKind::Record { fields } => fields.iter().find_map(|field| {
            goto_definition_symbol_from_type_annotation(&field.value, byte_offset)
        }),
    }
}

fn goto_definition_symbol_from_decl(
    decl: &crate::node_kinds::decl::Decl,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::decl::DeclKind;

    match &decl.kind {
        DeclKind::Struct {
            name, name_span, ..
        }
        | DeclKind::Protocol {
            name, name_span, ..
        }
        | DeclKind::Extend {
            name, name_span, ..
        }
        | DeclKind::Enum {
            name, name_span, ..
        }
        | DeclKind::Property {
            name, name_span, ..
        }
        | DeclKind::Effect {
            name, name_span, ..
        } => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        DeclKind::TypeAlias(name, name_span, ..) => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        DeclKind::EnumVariant {
            name, name_span, ..
        } => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        _ => None,
    }
}

fn nominal_name_span_contains(
    name: &crate::name::Name,
    name_span: crate::span::Span,
    byte_offset: u32,
) -> bool {
    if span_contains(name_span, byte_offset) {
        return true;
    }

    let name = name.name_str();
    if !name.contains("::") || name.starts_with('.') {
        return false;
    }

    let qualified_end = name_span.start.saturating_add(name.len() as u32);
    name_span.start <= byte_offset && byte_offset <= qualified_end
}

fn effect_symbol_at_offset(
    effects: &crate::node_kinds::func::EffectSet,
    byte_offset: u32,
) -> Option<Symbol> {
    for (name, span) in effects.names.iter().zip(effects.spans.iter()) {
        if effect_span_contains(*span, byte_offset) {
            return name.symbol().ok();
        }
    }
    None
}

/// Like `span_contains` but also accepts the tick mark position one byte before
/// the effect name span (the lexer excludes the `'` prefix from the name span).
fn effect_span_contains(span: crate::span::Span, byte_offset: u32) -> bool {
    span_contains(span, byte_offset) || (span.start > 0 && byte_offset == span.start - 1)
}

fn identifier_span_at_offset(
    meta: &crate::node_meta::NodeMeta,
    byte_offset: u32,
) -> Option<(u32, u32)> {
    meta.identifiers
        .iter()
        .find(|tok| tok.start <= byte_offset && byte_offset <= tok.end)
        .map(|tok| (tok.start, tok.end))
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
        if let Some(stdlib) = module.stdlib_workspace_for_module_id(module_id) {
            return definition_location_in_module(&stdlib, symbol);
        }
        // Cross-file import within the same workspace: normalize to Current
        return definition_location_in_module(module, symbol.current());
    }

    definition_location_in_module(module, symbol)
}

pub(crate) fn log_miss(kind: &str, uri: &Url, byte_offset: u32, node_descriptions: &[String]) {
    use std::io::Write;
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open("lsp_misses.log")
    {
        let _ = writeln!(
            f,
            "{} miss at {}:{} nodes=[{}]",
            kind,
            uri.path(),
            byte_offset,
            node_descriptions.join(", ")
        );
    }
}

pub(crate) fn describe_node(node: &crate::node::Node) -> String {
    match node {
        crate::node::Node::Expr(e) => format!("Expr({:?})", std::mem::discriminant(&e.kind)),
        crate::node::Node::Stmt(s) => format!("Stmt({:?})", std::mem::discriminant(&s.kind)),
        crate::node::Node::Decl(d) => format!("Decl({:?})", std::mem::discriminant(&d.kind)),
        crate::node::Node::Pattern(p) => {
            format!("Pattern({:?})", std::mem::discriminant(&p.kind))
        }
        crate::node::Node::TypeAnnotation(t) => {
            format!("TypeAnnotation({:?})", std::mem::discriminant(&t.kind))
        }
        other => format!("{:?}", std::mem::discriminant(other)),
    }
}

pub(crate) fn definition_location_in_module(
    module: &AnalysisWorkspace,
    symbol: Symbol,
) -> Option<Location> {
    let def_node = *module.resolved_names.symbols_to_node.get(&symbol)?;
    let file_id = def_node.0;
    let doc_id = module.file_id_to_document.get(file_id.0 as usize)?;
    let uri = url_from_document_id(doc_id)?;
    let text = module.texts.get(file_id.0 as usize)?;
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|a| a.as_ref())?;

    let (start, end) = if let Some(span) = definition_name_span(ast, def_node) {
        span
    } else if let Some(meta) = ast.meta.get(&def_node) {
        match meta.identifiers.first() {
            Some(tok) => (tok.start, tok.end),
            None => (meta.start.start, meta.end.end),
        }
    } else {
        // Synthetic nodes (e.g. from lower_funcs_to_lets) lack meta - use node span
        node_span(ast, def_node)?
    };
    let range = byte_span_to_range_utf16(text, start, end)?;

    Some(Location { uri, range })
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
        | DeclKind::Extend { name_span, .. }
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
        crate::node::Node::Pattern(p) => Some((p.span.start, p.span.end)),
        crate::node::Node::Expr(e) => Some((e.span.start, e.span.end)),
        crate::node::Node::Decl(d) => Some((d.span.start, d.span.end)),
        crate::node::Node::Stmt(s) => Some((s.span.start, s.span.end)),
        _ => None,
    }
}
