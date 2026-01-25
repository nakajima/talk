use async_lsp::lsp_types::{Location, Position, Range, Url};
use derive_visitor::Drive;

use crate::analysis::{node_ids_at_offset, resolve_member_symbol, span_contains};
use crate::analysis::workspace::Workspace as AnalysisWorkspace;
use crate::compiling::module::ModuleId;
use crate::name_resolution::symbol::Symbol;
use crate::node_kinds::expr::Expr;

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
    let candidate_ids = node_ids_at_offset(ast, byte_offset);

    for node_id in candidate_ids {
        let Some(node) = ast.find(node_id) else {
            continue;
        };

        // Special handling for import declarations
        if let crate::node::Node::Decl(ref decl) = node {
            if let Some(location) = goto_definition_from_import(module, uri, decl, byte_offset) {
                return Some(location);
            }
        }

        let symbol = match node {
            crate::node::Node::Expr(expr) => {
                goto_definition_symbol_from_expr(module.types.as_ref(), &expr, byte_offset)
            }
            crate::node::Node::Stmt(stmt) => {
                goto_definition_symbol_from_stmt(module.types.as_ref(), &stmt, byte_offset)
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
                    None
                }
            }
            crate::node::Node::FuncSignature(sig) => {
                let meta = ast.meta.get(&sig.id)?;
                let (start, end) = meta.identifiers.first().map(|t| (t.start, t.end))?;
                if start <= byte_offset && byte_offset <= end {
                    sig.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::GenericDecl(generic) => {
                if span_contains(generic.name_span, byte_offset) {
                    generic.name.symbol().ok()
                } else {
                    None
                }
            }
            crate::node::Node::Pattern(pattern) => {
                goto_definition_symbol_from_pattern(module.types.as_ref(), ast, &pattern, byte_offset)
            }
            crate::node::Node::CallArg(call_arg) => {
                goto_definition_symbol_from_call_arg(module.types.as_ref(), ast, &call_arg, byte_offset)
            }
            _ => None,
        };

        if let Some(symbol) = symbol
            && let Some(target) = definition_location_for_symbol(module, core, symbol)
        {
            return Some(target);
        }
    }

    // Fallback: search for CallArg nodes where label_span contains the offset
    // (since CallArg's span may not include the label)
    if let Some(result) = find_call_arg_by_label_span(module, core, ast, byte_offset) {
        return Some(result);
    }

    None
}

/// Search all CallArg nodes for one where label_span contains the offset
fn find_call_arg_by_label_span(
    module: &AnalysisWorkspace,
    core: Option<&AnalysisWorkspace>,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    byte_offset: u32,
) -> Option<Location> {
    use crate::node_kinds::call_arg::CallArg;
    use derive_visitor::Visitor;

    #[derive(Visitor)]
    #[visitor(CallArg(enter))]
    struct CallArgFinder {
        byte_offset: u32,
        found: Option<CallArg>,
    }

    impl CallArgFinder {
        fn enter_call_arg(&mut self, call_arg: &CallArg) {
            if span_contains(call_arg.label_span, self.byte_offset) {
                self.found = Some(call_arg.clone());
            }
        }
    }

    let mut finder = CallArgFinder {
        byte_offset,
        found: None,
    };

    for root in &ast.roots {
        root.drive(&mut finder);
        if finder.found.is_some() {
            break;
        }
    }

    if let Some(call_arg) = finder.found {
        if let Some(symbol) = goto_definition_symbol_from_call_arg(module.types.as_ref(), ast, &call_arg, byte_offset) {
            return definition_location_for_symbol(module, core, symbol);
        }
    }

    None
}

pub(crate) fn goto_definition_symbol_from_expr(
    types: Option<&crate::types::types::Types>,
    expr: &crate::node_kinds::expr::Expr,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::expr::ExprKind;

    match &expr.kind {
        ExprKind::Variable(name) | ExprKind::Constructor(name) => name.symbol().ok(),
        ExprKind::Member(receiver, label, name_span) => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }

            let receiver = receiver.as_ref()?;

            resolve_member_symbol(types, receiver, label)
        }
        ExprKind::CallEffect {
            effect_name,
            effect_name_span,
            ..
        } => {
            if !span_contains(*effect_name_span, byte_offset) {
                return None;
            }
            effect_name.symbol().ok()
        }
        ExprKind::Call { callee, args, .. } => {
            // Check if cursor is on a call argument label
            for arg in args {
                if span_contains(arg.label_span, byte_offset) {
                    if let crate::label::Label::Named(name) = &arg.label {
                        // Try to get the callee's type to find the struct
                        if let ExprKind::Constructor(constructor_name) = &callee.kind {
                            if let Ok(struct_symbol) = constructor_name.symbol() {
                                let label = crate::label::Label::Named(name.clone());
                                return types?.catalog.properties.get(&struct_symbol)?.get(&label).copied();
                            }
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

pub(crate) fn goto_definition_symbol_from_stmt(
    types: Option<&crate::types::types::Types>,
    stmt: &crate::node_kinds::stmt::Stmt,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::stmt::StmtKind;

    match &stmt.kind {
        StmtKind::Expr(expr) => goto_definition_symbol_from_expr(types, expr, byte_offset),
        StmtKind::Return(Some(expr)) => goto_definition_symbol_from_expr(types, expr, byte_offset),
        StmtKind::If(cond, ..) => goto_definition_symbol_from_expr(types, cond, byte_offset),
        StmtKind::Loop(Some(cond), ..) => {
            goto_definition_symbol_from_expr(types, cond, byte_offset)
        }
        StmtKind::Assignment(lhs, rhs) => goto_definition_symbol_from_expr(types, lhs, byte_offset)
            .or_else(|| goto_definition_symbol_from_expr(types, rhs, byte_offset)),
        StmtKind::Handling {
            effect_name,
            effect_name_span,
            ..
        } => {
            if !span_contains(*effect_name_span, byte_offset) {
                return None;
            }
            effect_name.symbol().ok()
        }
        _ => None,
    }
}

pub(crate) fn goto_definition_symbol_from_type_annotation(
    ty: &crate::node_kinds::type_annotation::TypeAnnotation,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    match &ty.kind {
        TypeAnnotationKind::Nominal {
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

fn goto_definition_symbol_from_pattern(
    types: Option<&crate::types::types::Types>,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    pattern: &crate::node_kinds::pattern::Pattern,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::label::Label;
    use crate::node_kinds::pattern::PatternKind;
    use crate::types::ty::Ty;

    match &pattern.kind {
        PatternKind::Bind(name) => {
            let meta = ast.meta.get(&pattern.id)?;
            let (start, end) = identifier_span_at_offset(meta, byte_offset)?;
            if start <= byte_offset && byte_offset <= end {
                name.symbol().ok()
            } else {
                None
            }
        }
        PatternKind::Variant {
            enum_name,
            variant_name,
            variant_name_span,
            ..
        } => {
            if !span_contains(*variant_name_span, byte_offset) {
                return None;
            }

            let types = types?;
            let label: Label = variant_name.clone().into();

            // First try: if enum_name is explicitly provided (e.g., Option.Some)
            if let Some(enum_name) = enum_name {
                let enum_symbol = enum_name.symbol().ok()?;
                return types.catalog.variants.get(&enum_symbol)?.get(&label).copied();
            }

            // Second try: infer enum from the pattern's type (if stored)
            if let Some(entry) = types.get(&pattern.id) {
                let ty = entry.as_mono_ty();
                if let Ty::Nominal { symbol, .. } = ty {
                    return types.catalog.variants.get(symbol)?.get(&label).copied();
                }
            }

            // Third try: Find parent match expression and use scrutinee type
            for (node_id, meta) in ast.meta.iter() {
                if meta.start.start <= pattern.span.start && pattern.span.end <= meta.end.end {
                    if let Some(node) = ast.find(*node_id) {
                        // Check if this is a Stmt containing a match expression
                        if let crate::node::Node::Stmt(stmt) = &node {
                            if let crate::node_kinds::stmt::StmtKind::Expr(expr) = &stmt.kind {
                                if let crate::node_kinds::expr::ExprKind::Match(scrutinee, _) = &expr.kind {
                                    if let Some(entry) = types.get(&scrutinee.id) {
                                        let ty = entry.as_mono_ty();
                                        if let Ty::Nominal { symbol, .. } = ty {
                                            return types.catalog.variants.get(symbol)?.get(&label).copied();
                                        }
                                    }
                                }
                            }
                        }
                        // Also check direct Expr nodes (for match expressions in expression position)
                        if let crate::node::Node::Expr(expr) = node {
                            if let crate::node_kinds::expr::ExprKind::Match(scrutinee, _) = &expr.kind {
                                if let Some(entry) = types.get(&scrutinee.id) {
                                    let ty = entry.as_mono_ty();
                                    if let Ty::Nominal { symbol, .. } = ty {
                                        return types.catalog.variants.get(symbol)?.get(&label).copied();
                                    }
                                }
                            }
                        }
                    }
                }
            }

            None
        }
        _ => None,
    }
}

fn goto_definition_symbol_from_call_arg(
    types: Option<&crate::types::types::Types>,
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    call_arg: &crate::node_kinds::call_arg::CallArg,
    byte_offset: u32,
) -> Option<Symbol> {
    use crate::label::Label;
    use crate::node_kinds::expr::ExprKind;
    use derive_visitor::Visitor;

    // Only handle if cursor is on the label
    if !span_contains(call_arg.label_span, byte_offset) {
        return None;
    }

    // Get the label name
    let label = match &call_arg.label {
        Label::Named(name) => Label::Named(name.clone()),
        _ => return None, // Positional args don't have field definitions
    };

    let types = types?;

    // Visitor to find the Call expression containing this arg
    #[derive(Visitor)]
    #[visitor(Expr(enter))]
    struct CallFinder {
        call_arg_id: crate::node_id::NodeID,
        result: Option<Symbol>,
        types: *const crate::types::types::Types,
        label: Label,
    }

    impl CallFinder {
        fn enter_expr(&mut self, expr: &crate::node_kinds::expr::Expr) {
            if let ExprKind::Call { callee, args, .. } = &expr.kind {
                // Check if this Call contains our arg
                if args.iter().any(|a| a.id == self.call_arg_id) {
                    // Found the parent Call - look up the field
                    if let ExprKind::Constructor(name) = &callee.kind {
                        if let Ok(struct_symbol) = name.symbol() {
                            // Safety: we only use this within the same function call
                            let types = unsafe { &*self.types };
                            if let Some(props) = types.catalog.properties.get(&struct_symbol) {
                                self.result = props.get(&self.label).copied();
                            }
                        }
                    }
                }
            }
        }
    }

    let mut finder = CallFinder {
        call_arg_id: call_arg.id,
        result: None,
        types,
        label,
    };

    for root in &ast.roots {
        root.drive(&mut finder);
        if finder.result.is_some() {
            break;
        }
    }

    finder.result
}

pub(crate) fn goto_definition_symbol_from_decl(
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
        DeclKind::EnumVariant(name, name_span, ..) => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol().ok()
        }
        DeclKind::Effect {
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
        let target_path = resolve_import_path(uri, &import.path)?;
        let target_uri = Url::from_file_path(&target_path).ok()?;
        return Some(Location {
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
        });
    }

    // Check if cursor is on an imported symbol - navigate to its definition
    if let ImportedSymbols::Named(symbols) = &import.symbols {
        for imported in symbols {
            if span_contains(imported.span, byte_offset) {
                // Find the target file and look up the symbol there
                let target_path = resolve_import_path(uri, &import.path)?;
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
        }
    }

    None
}

/// Resolve an import path relative to the importing file's URI.
fn resolve_import_path(uri: &Url, import_path: &crate::node_kinds::decl::ImportPath) -> Option<std::path::PathBuf> {
    use crate::node_kinds::decl::ImportPath;

    match import_path {
        ImportPath::Relative(rel_path) => {
            let source_path = uri.to_file_path().ok()?;
            let source_dir = source_path.parent()?;
            // Strip leading "./" if present
            let clean_rel = rel_path.strip_prefix("./").unwrap_or(rel_path);
            Some(source_dir.join(clean_rel))
        }
        ImportPath::Package(_) => {
            // Package imports not yet supported for go-to-definition
            None
        }
    }
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
        return None;
    }

    definition_location_in_module(module, symbol)
}

pub(crate) fn definition_location_in_module(module: &AnalysisWorkspace, symbol: Symbol) -> Option<Location> {
    let def_node = *module.resolved_names.symbols_to_node.get(&symbol)?;
    let file_id = def_node.0;
    let doc_id = module.file_id_to_document.get(file_id.0 as usize)?;
    let uri = url_from_document_id(doc_id)?;
    let text = module.texts.get(file_id.0 as usize)?;
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|a| a.as_ref())?;

    let meta = ast.meta.get(&def_node)?;
    let (start, end) = match meta.identifiers.first() {
        Some(tok) => (tok.start, tok.end),
        None => (meta.start.start, meta.end.end),
    };
    let range = byte_span_to_range_utf16(text, start, end)?;

    Some(Location { uri, range })
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
