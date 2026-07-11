use std::path::{Path, PathBuf};

use crate::analysis::workspace::Workspace;
use crate::analysis::{DocumentId, TextRange, node_ids_at_offset, span_contains};
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

    for (node_id, meta) in ast.meta.iter() {
        if meta.start.start <= byte_offset
            && byte_offset <= meta.end.end
            && let Some(crate::node::Node::Decl(ref decl)) = ast.find(*node_id)
            && let Some(location) = goto_definition_from_import(module, ast, decl, byte_offset)
        {
            return Some(location);
        }
    }

    let candidate_ids = node_ids_at_offset(ast, byte_offset);
    for node_id in candidate_ids {
        let Some(node) = ast.find(node_id) else {
            continue;
        };

        let symbol = match node {
            crate::node::Node::Expr(expr) => symbol_from_expr(module, &expr, byte_offset),
            crate::node::Node::Stmt(stmt) => symbol_from_stmt(module, &stmt, byte_offset),
            crate::node::Node::TypeAnnotation(ty) => symbol_from_type_annotation(&ty, byte_offset),
            crate::node::Node::Decl(decl) => symbol_from_decl(&decl, byte_offset),
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
                let (start, end) = meta
                    .identifiers
                    .first()
                    .map(|token| (token.start, token.end))?;
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
                crate::node_kinds::pattern::PatternKind::Variant { .. } => {
                    match module.types.member_resolutions.get(&pattern.id) {
                        Some(crate::types::output::MemberResolution::Direct(symbol)) => {
                            Some(*symbol)
                        }
                        Some(crate::types::output::MemberResolution::ViaConformance {
                            witness,
                            ..
                        }) => Some(*witness),
                        None => None,
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

    None
}

fn goto_definition_from_import(
    module: &Workspace,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    decl: &crate::node_kinds::decl::Decl,
    byte_offset: u32,
) -> Option<Location> {
    use crate::node_kinds::decl::{DeclKind, ImportedSymbols};

    let DeclKind::Import(import) = &decl.kind else {
        return None;
    };

    if span_contains(import.path_span, byte_offset) {
        return match &import.path {
            crate::node_kinds::decl::ImportPath::Local(_) => {
                let target_path =
                    resolve_import_path(&module.source_root, &ast.path, &import.path)?;
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
        };
    }

    if let ImportedSymbols::Named(symbols) = &import.symbols {
        for imported in symbols {
            if !span_contains(imported.span, byte_offset) {
                continue;
            }
            match &import.path {
                crate::node_kinds::decl::ImportPath::Local(_) => {
                    let target_path =
                        resolve_import_path(&module.source_root, &ast.path, &import.path)?;
                    let target_doc_id = document_id_for_path(module, &target_path)?;
                    let target_file_id = *module.document_to_file_id.get(&target_doc_id)?;
                    let target_scope_id = crate::node_id::NodeID(target_file_id, 0);
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

    None
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

fn document_id_for_path(module: &Workspace, path: &Path) -> Option<DocumentId> {
    let target = normalize_path(path);
    for (idx, ast) in module.asts.iter().enumerate() {
        let Some(ast) = ast else {
            continue;
        };
        if normalize_path(Path::new(&ast.path)) == target {
            return module.file_id_to_document.get(idx).cloned();
        }
    }
    None
}

fn normalize_path(path: &Path) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

fn symbol_from_expr(
    module: &Workspace,
    expr: &crate::node_kinds::expr::Expr,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::expr::ExprKind;

    match &expr.kind {
        ExprKind::Variable(name) | ExprKind::Constructor(name) => name.symbol().ok(),
        ExprKind::Call { callee, .. } => symbol_from_expr(module, callee, byte_offset),
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

fn symbol_from_stmt(
    module: &Workspace,
    stmt: &crate::node_kinds::stmt::Stmt,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::stmt::StmtKind;

    match &stmt.kind {
        StmtKind::Expr(expr) => symbol_from_expr(module, expr, byte_offset),
        StmtKind::Return(Some(expr)) => symbol_from_expr(module, expr, byte_offset),
        StmtKind::If(cond, ..) => symbol_from_expr(module, cond, byte_offset),
        StmtKind::Loop(Some(cond), ..) => symbol_from_expr(module, cond, byte_offset),
        StmtKind::Assignment(lhs, rhs) => symbol_from_expr(module, lhs, byte_offset)
            .or_else(|| symbol_from_expr(module, rhs, byte_offset)),
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
        StmtKind::Continue(Some(expr)) => symbol_from_expr(module, expr, byte_offset),
        _ => None,
    }
}

fn symbol_from_type_annotation(
    ty: &crate::node_kinds::type_annotation::TypeAnnotation,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    match &ty.kind {
        TypeAnnotationKind::Borrow { inner, .. } | TypeAnnotationKind::Unique { inner } => {
            symbol_from_type_annotation(inner, byte_offset)
        }
        TypeAnnotationKind::Nominal {
            name,
            name_span,
            generics,
        } => generics
            .iter()
            .find_map(|generic| symbol_from_type_annotation(generic, byte_offset))
            .or_else(|| {
                nominal_name_span_contains(name, *name_span, byte_offset)
                    .then(|| name.symbol().ok())
                    .flatten()
            }),
        TypeAnnotationKind::SelfType(name) => name.symbol().ok(),
        TypeAnnotationKind::Any {
            protocol,
            assoc_bindings,
        } => symbol_from_type_annotation(protocol, byte_offset).or_else(|| {
            assoc_bindings
                .iter()
                .find_map(|binding| symbol_from_type_annotation(&binding.value, byte_offset))
        }),
        TypeAnnotationKind::NominalPath { base, .. } => {
            symbol_from_type_annotation(base, byte_offset)
        }
        TypeAnnotationKind::Func {
            params,
            effects,
            returns,
        } => params
            .iter()
            .find_map(|param| symbol_from_type_annotation(param, byte_offset))
            .or_else(|| effect_symbol_at_offset(effects, byte_offset))
            .or_else(|| symbol_from_type_annotation(returns, byte_offset)),
        TypeAnnotationKind::Tuple(items) => items
            .iter()
            .find_map(|item| symbol_from_type_annotation(item, byte_offset)),
        TypeAnnotationKind::Record { fields } => fields
            .iter()
            .find_map(|field| symbol_from_type_annotation(&field.value, byte_offset)),
    }
}

fn symbol_from_decl(decl: &crate::node_kinds::decl::Decl, byte_offset: u32) -> Option<Symbol> {
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
    module: &Workspace,
    core: Option<&Workspace>,
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
        return definition_location_in_module(module, symbol.current());
    }

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
        crate::node::Node::Pattern(pattern) => Some((pattern.span.start, pattern.span.end)),
        crate::node::Node::Expr(expr) => Some((expr.span.start, expr.span.end)),
        crate::node::Node::Decl(decl) => Some((decl.span.start, decl.span.end)),
        crate::node::Node::Stmt(stmt) => Some((stmt.span.start, stmt.span.end)),
        _ => None,
    }
}
