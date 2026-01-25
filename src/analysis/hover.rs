use crate::analysis::{Hover, TextRange, span_contains};
use crate::name_resolution::symbol::Symbol;
use crate::node::Node;
use crate::node_id::FileID;
use crate::node_kinds::{
    decl::Decl, func::Func, func_signature::FuncSignature, parameter::Parameter, pattern::Pattern,
    type_annotation::TypeAnnotation,
};

use crate::analysis::workspace::Workspace;
use crate::types::format::{SymbolNames, TypeFormatter};
use crate::types::types::TypeEntry;

pub fn hover_at(
    module: &Workspace,
    core: Option<&Workspace>,
    document_id: &crate::analysis::DocumentId,
    byte_offset: u32,
) -> Option<Hover> {
    let idx = module.document_index(document_id)?;
    let file_id = FileID(idx as u32);
    let ast = module.asts.get(idx).and_then(|a| a.as_ref())?;
    let types = module.types.as_ref();
    let formatter = TypeFormatter::new(SymbolNames::new(
        Some(&module.resolved_names.symbol_names),
        core.map(|core| &core.resolved_names.symbol_names),
    ));

    let ctx = HoverCtx {
        ast,
        types,
        byte_offset,
        formatter,
    };

    // Try the symbol index first - fast path for most symbols
    if let Some((symbol, start, end, node_id)) =
        module.resolved_names.symbol_at_offset(file_id, byte_offset)
    {
        let range = TextRange::new(start, end);
        let symbol_name = module
            .resolved_names
            .symbol_names
            .get(&symbol)
            .cloned()
            .unwrap_or_else(|| format!("{:?}", symbol));

        // For Property symbols with a NodeID, get the expression type for specialized generics
        let node_ty = if matches!(symbol, Symbol::Property(..)) {
            node_id
                .and_then(|id| types.and_then(|t| t.get(&id)))
                .map(|e| e.as_mono_ty())
                .or_else(|| types.and_then(|t| t.get_symbol(&symbol)).map(|e| e.as_mono_ty()))
        } else {
            types.and_then(|t| t.get_symbol(&symbol)).map(|e| e.as_mono_ty())
        };

        if let Some(line) =
            hover_line_for_name_and_type(&ctx.formatter, symbol_name, Some(symbol), ctx.types, node_ty)
        {
            return Some(Hover {
                contents: line,
                range: Some(range),
            });
        }
    }

    // Fall back to AST-based lookup for expressions without symbols (e.g., 1 + 2)
    let candidate_ids = node_ids_at_offset(ctx.ast, ctx.byte_offset);

    for node_id in candidate_ids {
        let Some(node) = ctx.ast.find(node_id) else {
            continue;
        };

        if let crate::node::Node::Expr(expr) = node {
            if let Some(hover) = hover_for_expr(&ctx, &expr) {
                return Some(hover);
            }
        }
    }

    None
}

pub fn hover_for_node_id(
    module: &Workspace,
    core: Option<&Workspace>,
    document_id: &crate::analysis::DocumentId,
    node_id: crate::node_id::NodeID,
) -> Option<Hover> {
    let idx = module.document_index(document_id)?;
    let ast = module.asts.get(idx).and_then(|a| a.as_ref())?;
    let types = module.types.as_ref();
    let formatter = TypeFormatter::new(SymbolNames::new(
        Some(&module.resolved_names.symbol_names),
        core.map(|core| &core.resolved_names.symbol_names),
    ));

    let node = ast.find(node_id)?;
    let byte_offset = preferred_offset_for_node(ast, &node)?;
    let ctx = HoverCtx {
        ast,
        types,
        byte_offset,
        formatter,
    };

    hover_for_node(&ctx, &node)
}

/// Find node IDs at a given byte offset, sorted by span size (smallest first).
fn node_ids_at_offset(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    byte_offset: u32,
) -> Vec<crate::node_id::NodeID> {
    let mut candidates: Vec<(crate::node_id::NodeID, u32)> = ast
        .meta
        .iter()
        .filter_map(|(id, meta)| {
            let start = meta.start.start;
            let end = meta.end.end;
            if start <= byte_offset && byte_offset <= end {
                Some((*id, end.saturating_sub(start)))
            } else {
                None
            }
        })
        .collect();

    candidates.sort_by_key(|(_, len)| *len);
    candidates.into_iter().map(|(id, _)| id).collect()
}

struct HoverCtx<'a> {
    ast: &'a crate::ast::AST<crate::ast::NameResolved>,
    types: Option<&'a crate::types::types::Types>,
    byte_offset: u32,
    formatter: TypeFormatter<'a>,
}

fn hover_for_node(ctx: &HoverCtx<'_>, node: &Node) -> Option<Hover> {
    match node {
        Node::Expr(expr) => hover_for_expr(ctx, expr),
        Node::Stmt(stmt) => hover_for_stmt(ctx, stmt),
        Node::Pattern(pattern) => hover_for_pattern(ctx, pattern),
        Node::TypeAnnotation(ty) => hover_for_type_annotation(ctx, ty),
        Node::Parameter(param) => hover_for_parameter(ctx, param),
        Node::Func(func) => hover_for_func(ctx, func),
        Node::FuncSignature(sig) => hover_for_func_signature(ctx, sig),
        Node::Decl(decl) => hover_for_decl(ctx, decl),
        _ => None,
    }
}

fn preferred_offset_for_node(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    node: &Node,
) -> Option<u32> {
    use crate::node_kinds::decl::DeclKind;
    use crate::node_kinds::expr::ExprKind;
    use crate::node_kinds::pattern::PatternKind;
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    let meta = ast.meta.get(&node.node_id());
    let meta_start = meta.map(|meta| meta.start.start);
    let identifier_start = meta
        .and_then(|meta| meta.identifiers.first().map(|tok| tok.start))
        .or(meta_start);

    match node {
        Node::Expr(expr) => match &expr.kind {
            ExprKind::Member(_, _, name_span) => Some(name_span.start),
            ExprKind::Variable(..) | ExprKind::Constructor(..) => {
                identifier_start.or(Some(expr.span.start))
            }
            _ => meta_start.or(Some(expr.span.start)),
        },
        Node::Pattern(pattern) => match &pattern.kind {
            PatternKind::Bind(..) => identifier_start.or(Some(pattern.span.start)),
            _ => meta_start.or(Some(pattern.span.start)),
        },
        Node::TypeAnnotation(ty) => match &ty.kind {
            TypeAnnotationKind::Nominal { name_span, .. } => Some(name_span.start),
            TypeAnnotationKind::NominalPath { member_span, .. } => Some(member_span.start),
            TypeAnnotationKind::SelfType(..) => identifier_start.or(Some(ty.span.start)),
            _ => meta_start.or(Some(ty.span.start)),
        },
        Node::Parameter(param) => Some(param.name_span.start),
        Node::Func(func) => Some(func.name_span.start),
        Node::FuncSignature(sig) => identifier_start.or(Some(sig.span.start)),
        Node::Decl(decl) => match &decl.kind {
            DeclKind::Struct { name_span, .. }
            | DeclKind::Protocol { name_span, .. }
            | DeclKind::Extend { name_span, .. }
            | DeclKind::Enum { name_span, .. }
            | DeclKind::Property { name_span, .. }
            | DeclKind::TypeAlias(_, name_span, ..)
            | DeclKind::EnumVariant(_, name_span, ..) => Some(name_span.start),
            DeclKind::Init { .. } => identifier_start.or(Some(decl.span.start)),
            _ => meta_start.or(Some(decl.span.start)),
        },
        _ => meta_start.or(Some(node.span().start)),
    }
}

fn hover_for_stmt(ctx: &HoverCtx<'_>, stmt: &crate::node_kinds::stmt::Stmt) -> Option<Hover> {
    use crate::node_kinds::stmt::StmtKind;

    match &stmt.kind {
        StmtKind::Expr(expr) => hover_for_expr(ctx, expr),
        StmtKind::Return(Some(expr)) => hover_for_expr(ctx, expr),
        StmtKind::If(cond, ..) => hover_for_expr(ctx, cond),
        StmtKind::Loop(Some(cond), ..) => hover_for_expr(ctx, cond),
        StmtKind::Assignment(lhs, rhs) => {
            hover_for_expr(ctx, lhs).or_else(|| hover_for_expr(ctx, rhs))
        }
        _ => None,
    }
}

fn hover_for_expr(ctx: &HoverCtx<'_>, expr: &crate::node_kinds::expr::Expr) -> Option<Hover> {
    // For expressions without symbols (literals, operations, etc.), show just the type
    let types = ctx.types?;
    let entry = types.get(&expr.id)?;
    let meta = ctx.ast.meta.get(&expr.id)?;
    let range = range_from_meta_at_offset(meta, ctx.byte_offset)?;

    Some(Hover {
        contents: ctx.formatter.format_ty(entry.as_mono_ty()),
        range: Some(range),
    })
}

fn hover_for_pattern(ctx: &HoverCtx<'_>, pattern: &Pattern) -> Option<Hover> {
    use crate::node_kinds::pattern::PatternKind;

    let PatternKind::Bind(name) = &pattern.kind else {
        return None;
    };

    let meta = ctx.ast.meta.get(&pattern.id)?;
    let (start, end) = identifier_span_at_offset(meta, ctx.byte_offset)?;
    let range = TextRange::new(start, end);

    let symbol = name.symbol().ok();
    let node_ty = ctx
        .types
        .and_then(|types| types.get(&pattern.id))
        .map(|entry| entry.as_mono_ty());
    let line =
        hover_line_for_name_and_type(&ctx.formatter, name.name_str(), symbol, ctx.types, node_ty)?;

    Some(Hover {
        contents: line,
        range: Some(range),
    })
}

fn hover_for_type_annotation(ctx: &HoverCtx<'_>, ty: &TypeAnnotation) -> Option<Hover> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    let (start, end, name, symbol) = match &ty.kind {
        TypeAnnotationKind::Nominal { name, name_span, .. } => {
            if !span_contains(*name_span, ctx.byte_offset) {
                return None;
            }
            (name_span.start, name_span.end, name.name_str(), name.symbol().ok())
        }
        TypeAnnotationKind::NominalPath { member_span, .. } => {
            if !span_contains(*member_span, ctx.byte_offset) {
                return None;
            }
            (member_span.start, member_span.end, String::new(), None)
        }
        TypeAnnotationKind::SelfType(name) => {
            let meta = ctx.ast.meta.get(&ty.id)?;
            let (start, end) = identifier_span_at_offset(meta, ctx.byte_offset)?;
            (start, end, name.name_str(), name.symbol().ok())
        }
        _ => return None,
    };

    let range = TextRange::new(start, end);

    // Try to get type info for this annotation
    if let Some(types) = ctx.types
        && let Some(entry) = types.get(&ty.id) {
            return Some(Hover {
                contents: ctx.formatter.format_ty(entry.as_mono_ty()),
                range: Some(range),
            });
        }

    // Fall back to symbol-based hover if no type entry
    let line = hover_line_for_name_and_type(&ctx.formatter, name, symbol, ctx.types, None)?;
    Some(Hover {
        contents: line,
        range: Some(range),
    })
}

fn hover_for_parameter(ctx: &HoverCtx<'_>, param: &Parameter) -> Option<Hover> {
    if !span_contains(param.name_span, ctx.byte_offset) {
        return None;
    }

    let range = TextRange::new(param.name_span.start, param.name_span.end);
    let symbol = param.name.symbol().ok();
    let node_ty = ctx
        .types
        .and_then(|types| types.get(&param.id))
        .map(|entry| entry.as_mono_ty());
    let line = hover_line_for_name_and_type(
        &ctx.formatter,
        param.name.name_str(),
        symbol,
        ctx.types,
        node_ty,
    )?;

    Some(Hover {
        contents: line,
        range: Some(range),
    })
}

fn hover_for_func(ctx: &HoverCtx<'_>, func: &Func) -> Option<Hover> {
    if !span_contains(func.name_span, ctx.byte_offset) {
        return None;
    }

    let range = TextRange::new(func.name_span.start, func.name_span.end);
    let symbol = func.name.symbol().ok();
    let node_ty = ctx
        .types
        .and_then(|types| types.get(&func.id))
        .map(|entry| entry.as_mono_ty());
    let line = hover_line_for_name_and_type(
        &ctx.formatter,
        func.name.name_str(),
        symbol,
        ctx.types,
        node_ty,
    )?;

    Some(Hover {
        contents: line,
        range: Some(range),
    })
}

fn hover_for_func_signature(ctx: &HoverCtx<'_>, sig: &FuncSignature) -> Option<Hover> {
    let meta = ctx.ast.meta.get(&sig.id)?;
    let (start, end) = identifier_span_at_offset(meta, ctx.byte_offset)?;
    let range = TextRange::new(start, end);

    let symbol = sig.name.symbol().ok();
    let node_ty = ctx
        .types
        .and_then(|types| types.get(&sig.id))
        .map(|entry| entry.as_mono_ty());
    let line = hover_line_for_name_and_type(
        &ctx.formatter,
        sig.name.name_str(),
        symbol,
        ctx.types,
        node_ty,
    )?;

    Some(Hover {
        contents: line,
        range: Some(range),
    })
}

fn hover_for_decl(ctx: &HoverCtx<'_>, decl: &Decl) -> Option<Hover> {
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
            if !span_contains(*name_span, ctx.byte_offset) {
                return None;
            }

            let symbol = name.symbol().ok();
            let node_ty = ctx
                .types
                .and_then(|types| types.get(&decl.id))
                .map(|entry| entry.as_mono_ty());
            let line = hover_line_for_name_and_type(
                &ctx.formatter,
                name.name_str(),
                symbol,
                ctx.types,
                node_ty,
            )?;
            let range = TextRange::new(name_span.start, name_span.end);

            Some(Hover {
                contents: line,
                range: Some(range),
            })
        }
        DeclKind::TypeAlias(name, name_span, ..) | DeclKind::EnumVariant(name, name_span, ..) => {
            if !span_contains(*name_span, ctx.byte_offset) {
                return None;
            }

            let symbol = name.symbol().ok();
            let node_ty = ctx
                .types
                .and_then(|types| types.get(&decl.id))
                .map(|entry| entry.as_mono_ty());
            let line = hover_line_for_name_and_type(
                &ctx.formatter,
                name.name_str(),
                symbol,
                ctx.types,
                node_ty,
            )?;
            let range = TextRange::new(name_span.start, name_span.end);

            Some(Hover {
                contents: line,
                range: Some(range),
            })
        }
        DeclKind::Init { name, .. } => {
            let meta = ctx.ast.meta.get(&decl.id)?;
            let (start, end) = identifier_span_at_offset(meta, ctx.byte_offset)?;
            let range = TextRange::new(start, end);

            let symbol = name.symbol().ok();
            let node_ty = ctx
                .types
                .and_then(|types| types.get(&decl.id))
                .map(|entry| entry.as_mono_ty());
            let line = hover_line_for_name_and_type(
                &ctx.formatter,
                name.name_str(),
                symbol,
                ctx.types,
                node_ty,
            )?;

            Some(Hover {
                contents: line,
                range: Some(range),
            })
        }
        DeclKind::Method { func, .. } => hover_for_func(ctx, func),
        DeclKind::Func(func) => hover_for_func(ctx, func),
        _ => None,
    }
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

fn range_from_meta_at_offset(
    meta: &crate::node_meta::NodeMeta,
    byte_offset: u32,
) -> Option<TextRange> {
    if let Some((start, end)) = identifier_span_at_offset(meta, byte_offset) {
        return Some(TextRange::new(start, end));
    }
    Some(TextRange::new(meta.start.start, meta.end.end))
}

fn hover_line_for_name_and_type(
    formatter: &TypeFormatter,
    name: String,
    symbol: Option<Symbol>,
    types: Option<&crate::types::types::Types>,
    node_ty: Option<&crate::types::ty::Ty>,
) -> Option<String> {
    let symbol_entry = symbol.and_then(|sym| types.and_then(|types| types.get_symbol(&sym)));

    let Some(symbol) = symbol else {
        let type_str = match symbol_entry {
            Some(entry) => Some(formatter.format_type_entry(entry)),
            None => node_ty.map(|ty| formatter.format_ty(ty)),
        };
        return type_str.map(|t| format!("{name}: {t}"));
    };

    let is_builtin_type = matches!(
        symbol,
        Symbol::Int | Symbol::Float | Symbol::Bool | Symbol::Void | Symbol::RawPtr | Symbol::Byte
    );

    // For instance methods, use special formatting that omits self and uncurries
    let is_instance_method = matches!(symbol, Symbol::InstanceMethod(..));

    // Check if the type is a function type
    let is_func_type = symbol_entry
        .map(|entry| matches!(entry.as_mono_ty(), crate::types::ty::Ty::Func(..)))
        .unwrap_or(false);

    let type_str = if is_instance_method {
        symbol_entry.map(|entry| formatter.format_method_type_entry(entry))
    } else if is_func_type {
        symbol_entry.map(|entry| formatter.format_func_type_entry(entry))
    } else {
        match symbol_entry {
            Some(entry @ TypeEntry::Poly(..)) => Some(formatter.format_type_entry(entry)),
            Some(entry) => node_ty
                .map(|ty| formatter.format_ty(ty))
                .or_else(|| Some(formatter.format_type_entry(entry))),
            None => node_ty.map(|ty| formatter.format_ty(ty)),
        }
    };

    Some(match symbol {
        Symbol::Struct(..) => format!("struct {name}"),
        Symbol::Enum(..) => format!("enum {name}"),
        Symbol::Protocol(..) => format!("protocol {name}"),
        Symbol::TypeAlias(..) => format!("typealias {name}"),
        Symbol::TypeParameter(..) => format!("type {name}"),
        Symbol::AssociatedType(..) => format!("associated {name}"),
        Symbol::Property(..) => type_str
            .map(|t| format!("let {name}: {t}"))
            .unwrap_or_else(|| format!("let {name}")),
        Symbol::InstanceMethod(..) | Symbol::StaticMethod(..) | Symbol::MethodRequirement(..) => {
            type_str
                .map(|t| format!("func {name}{t}"))
                .unwrap_or_else(|| format!("func {name}"))
        }
        Symbol::Initializer(..) => type_str
            .map(|t| format!("init {name}: {t}"))
            .unwrap_or_else(|| format!("init {name}")),
        Symbol::Variant(..) => type_str
            .map(|t| format!("case {name}: {t}"))
            .unwrap_or_else(|| format!("case {name}")),
        Symbol::Builtin(..) if is_builtin_type => name,
        _ => type_str.map(|t| format!("{name}: {t}"))?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::{DocumentInput, Workspace};

    fn analyze(code: &str) -> Workspace {
        let doc = DocumentInput {
            id: "test.tlk".to_string(),
            path: "test.tlk".to_string(),
            version: 0,
            text: code.to_string(),
        };

        Workspace::new(vec![doc]).expect("workspace")
    }

    fn byte_offset_for(code: &str, needle: &str, nth: usize) -> u32 {
        code.match_indices(needle)
            .nth(nth)
            .map(|(i, _)| i as u32)
            .expect("needle")
    }

    #[test]
    fn hover_on_method_in_struct() {
        let code = r#"
struct Foo {
    func bar() -> Int { 1 }
}
"#;
        let workspace = analyze(code);
        let doc_id = "test.tlk".to_string();
        let byte_offset = byte_offset_for(code, "bar", 0);
        let hover = hover_at(&workspace, None, &doc_id, byte_offset);
        assert!(hover.is_some(), "expected hover info for method");
        let hover = hover.expect("hover");
        assert_eq!(hover.contents, "func bar() -> Int");
    }

    #[test]
    fn hover_on_method_with_params() {
        let code = r#"
struct Foo {
    func add(a: Int, b: Int) -> Int { a }
}
"#;
        let workspace = analyze(code);
        let doc_id = "test.tlk".to_string();
        let byte_offset = byte_offset_for(code, "add", 0);
        let hover = hover_at(&workspace, None, &doc_id, byte_offset);
        assert!(hover.is_some(), "expected hover info for method");
        let hover = hover.expect("hover");
        assert_eq!(hover.contents, "func add(Int, Int) -> Int");
    }

    #[test]
    fn hover_on_return_type_in_method() {
        let code = r#"
struct Foo<T> {
    let value: T

    func get() -> T {
        self.value
    }
}
"#;
        let workspace = analyze(code);
        let doc_id = "test.tlk".to_string();
        // Find "T" in "-> T"
        let byte_offset = byte_offset_for(code, "-> T", 0) + 3; // point to T after ->
        let hover = hover_at(&workspace, None, &doc_id, byte_offset);
        assert!(hover.is_some(), "expected hover info for return type T, offset: {byte_offset}");
        let hover = hover.expect("hover");
        assert!(hover.contents.contains("T"), "expected 'T' in hover: {}", hover.contents);
    }

    #[test]
    fn hover_on_top_level_func_shows_uncurried() {
        let code = r#"
func add(a: Int, b: Int) -> Int { a }
"#;
        let workspace = analyze(code);
        let doc_id = "test.tlk".to_string();
        let byte_offset = byte_offset_for(code, "add", 0);
        let hover = hover_at(&workspace, None, &doc_id, byte_offset);
        assert!(hover.is_some(), "expected hover info for top-level func");
        let hover = hover.expect("hover");
        // Should show uncurried: (Int, Int) -> Int, not curried: (Int) -> (Int) -> Int
        assert_eq!(hover.contents, "add: (Int, Int) -> Int");
    }

    #[test]
    fn hover_on_property_access_shows_specialized_type() {
        let code = r#"
struct Box<T> {
    let value: T
}

func test() {
    let box = Box(value: 42)
    box.value
}
"#;
        let workspace = analyze(code);
        let doc_id = "test.tlk".to_string();
        // Find "value" in "box.value" (second occurrence)
        let byte_offset = byte_offset_for(code, "value", 2);
        let hover = hover_at(&workspace, None, &doc_id, byte_offset);
        assert!(hover.is_some(), "expected hover info for property access");
        let hover = hover.expect("hover");
        // Should show specialized type Int, not generic type T
        assert_eq!(hover.contents, "let value: Int");
    }
}
