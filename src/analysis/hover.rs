use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::{node_ids_at_offset, resolve_member_symbol, span_contains, Hover, TextRange};
use crate::name_resolution::symbol::Symbol;
use crate::node_kinds::{
    decl::Decl,
    func::Func,
    func_signature::FuncSignature,
    parameter::Parameter,
    pattern::Pattern,
    type_annotation::TypeAnnotation,
};

use crate::analysis::workspace::Workspace;

pub fn hover_at(
    module: &Workspace,
    core: Option<&Workspace>,
    document_id: &crate::analysis::DocumentId,
    byte_offset: u32,
) -> Option<Hover> {
    let idx = module.document_index(document_id)?;
    let ast = module.asts.get(idx).and_then(|a| a.as_ref())?;
    let types = module.types.as_ref();

    let ctx = HoverCtx {
        module,
        core,
        ast,
        types,
        byte_offset,
    };

    let candidate_ids = node_ids_at_offset(ctx.ast, ctx.byte_offset);

    for node_id in candidate_ids {
        let Some(node) = ctx.ast.find(node_id) else {
            continue;
        };

        let hover = match node {
            crate::node::Node::Expr(expr) => hover_for_expr(&ctx, &expr),
            crate::node::Node::Stmt(stmt) => hover_for_stmt(&ctx, &stmt),
            crate::node::Node::Pattern(pattern) => hover_for_pattern(&ctx, &pattern),
            crate::node::Node::TypeAnnotation(ty) => hover_for_type_annotation(&ctx, &ty),
            crate::node::Node::Parameter(param) => hover_for_parameter(&ctx, &param),
            crate::node::Node::Func(func) => hover_for_func(&ctx, &func),
            crate::node::Node::FuncSignature(sig) => hover_for_func_signature(&ctx, &sig),
            crate::node::Node::Decl(decl) => hover_for_decl(&ctx, &decl),
            _ => None,
        };

        if hover.is_some() {
            return hover;
        }
    }

    None
}

struct HoverCtx<'a> {
    module: &'a Workspace,
    core: Option<&'a Workspace>,
    ast: &'a crate::ast::AST<crate::ast::NameResolved>,
    types: Option<&'a crate::types::type_session::Types>,
    byte_offset: u32,
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
    use crate::node_kinds::expr::ExprKind;

    match &expr.kind {
        ExprKind::Member(receiver, label, name_span) => {
            if !span_contains(*name_span, ctx.byte_offset) {
                return None;
            }

            let receiver = receiver.as_ref()?;
            let member_symbol = resolve_member_symbol(ctx.types, receiver, label);
            let node_ty = ctx
                .types
                .and_then(|types| types.get(&expr.id))
                .map(|entry| entry.as_mono_ty());

            let line = hover_line_for_name_and_type(
                ctx.module,
                ctx.core,
                label.to_string(),
                member_symbol,
                ctx.types,
                node_ty,
            )?;
            let range = TextRange::new(name_span.start, name_span.end);

            Some(Hover {
                contents: line,
                range: Some(range),
            })
        }
        ExprKind::Variable(name) | ExprKind::Constructor(name) => {
            let meta = ctx.ast.meta.get(&expr.id)?;
            let (start, end) = identifier_span_at_offset(meta, ctx.byte_offset)?;
            let range = TextRange::new(start, end);

            let symbol = name.symbol().ok();
            let node_ty = ctx
                .types
                .and_then(|types| types.get(&expr.id))
                .map(|entry| entry.as_mono_ty());

            let line = hover_line_for_name_and_type(
                ctx.module,
                ctx.core,
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
        _ => {
            let types = ctx.types?;
            let entry = types.get(&expr.id)?;
            let meta = ctx.ast.meta.get(&expr.id)?;
            let range = range_from_meta_at_offset(meta, ctx.byte_offset)?;

            Some(Hover {
                contents: format_ty(ctx.module, ctx.core, entry.as_mono_ty()),
                range: Some(range),
            })
        }
    }
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
    let line = hover_line_for_name_and_type(
        ctx.module,
        ctx.core,
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

fn hover_for_type_annotation(ctx: &HoverCtx<'_>, ty: &TypeAnnotation) -> Option<Hover> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    let types = ctx.types?;
    let entry = types.get(&ty.id)?;
    let (start, end) = match &ty.kind {
        TypeAnnotationKind::Nominal { name_span, .. } => {
            if !span_contains(*name_span, ctx.byte_offset) {
                return None;
            }
            (name_span.start, name_span.end)
        }
        TypeAnnotationKind::NominalPath { member_span, .. } => {
            if !span_contains(*member_span, ctx.byte_offset) {
                return None;
            }
            (member_span.start, member_span.end)
        }
        TypeAnnotationKind::SelfType(..) => {
            let meta = ctx.ast.meta.get(&ty.id)?;
            identifier_span_at_offset(meta, ctx.byte_offset)?
        }
        _ => return None,
    };

    let range = TextRange::new(start, end);

    Some(Hover {
        contents: format_ty(ctx.module, ctx.core, entry.as_mono_ty()),
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
        ctx.module,
        ctx.core,
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
        ctx.module,
        ctx.core,
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
        ctx.module,
        ctx.core,
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
                ctx.module,
                ctx.core,
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
                ctx.module,
                ctx.core,
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
                ctx.module,
                ctx.core,
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
    module: &Workspace,
    core: Option<&Workspace>,
    name: String,
    symbol: Option<Symbol>,
    types: Option<&crate::types::type_session::Types>,
    node_ty: Option<&crate::types::ty::Ty>,
) -> Option<String> {
    let symbol_entry = symbol.and_then(|sym| types.and_then(|types| types.get_symbol(&sym)));
    let type_str = match symbol_entry {
        Some(crate::types::type_session::TypeEntry::Poly(..)) => {
            Some(format_type_entry(module, core, symbol_entry?))
        }
        Some(entry) => node_ty
            .map(|ty| format_ty(module, core, ty))
            .or_else(|| Some(format_type_entry(module, core, entry))),
        None => node_ty.map(|ty| format_ty(module, core, ty)),
    };

    let Some(symbol) = symbol else {
        return type_str.map(|t| format!("{name}: {t}"));
    };

    let is_builtin_type = matches!(
        symbol,
        Symbol::Int | Symbol::Float | Symbol::Bool | Symbol::Void | Symbol::RawPtr | Symbol::Byte
    );

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
                .map(|t| format!("func {name}: {t}"))
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

fn format_type_entry(
    module: &Workspace,
    core: Option<&Workspace>,
    entry: &crate::types::type_session::TypeEntry,
) -> String {
    match entry {
        crate::types::type_session::TypeEntry::Mono(ty) => format_ty(module, core, ty),
        crate::types::type_session::TypeEntry::Poly(scheme) => format_scheme(module, core, scheme),
    }
}

#[derive(Default)]
struct TyFormatContext {
    type_param_order: Vec<crate::types::infer_ty::TypeParamId>,
    row_param_order: Vec<crate::types::infer_row::RowParamId>,
    type_param_names: FxHashMap<crate::types::infer_ty::TypeParamId, String>,
    row_param_names: FxHashMap<crate::types::infer_row::RowParamId, String>,
}

impl TyFormatContext {
    fn from_scheme(scheme: &crate::types::scheme::Scheme<crate::types::ty::Ty>) -> Self {
        use crate::types::scheme::ForAll;

        let mut type_params: Vec<crate::types::infer_ty::TypeParamId> = vec![];
        let mut row_params: Vec<crate::types::infer_row::RowParamId> = vec![];
        for forall in &scheme.foralls {
            match forall {
                ForAll::Ty(id) => type_params.push(*id),
                ForAll::Row(id) => row_params.push(*id),
            }
        }

        type_params.sort();
        row_params.sort();

        let mut ctx = Self {
            type_param_order: type_params.clone(),
            row_param_order: row_params.clone(),
            type_param_names: FxHashMap::default(),
            row_param_names: FxHashMap::default(),
        };

        for (idx, id) in type_params.into_iter().enumerate() {
            ctx.type_param_names
                .insert(id, type_param_display_name(idx));
        }
        for (idx, id) in row_params.into_iter().enumerate() {
            ctx.row_param_names.insert(id, row_param_display_name(idx));
        }

        ctx
    }

    fn from_ty(ty: &crate::types::ty::Ty) -> Self {
        let mut ty_params: FxHashSet<crate::types::infer_ty::TypeParamId> = FxHashSet::default();
        let mut row_params: FxHashSet<crate::types::infer_row::RowParamId> = FxHashSet::default();
        collect_params_in_ty(ty, &mut ty_params, &mut row_params);

        let mut type_param_order: Vec<_> = ty_params.into_iter().collect();
        type_param_order.sort();
        let mut row_param_order: Vec<_> = row_params.into_iter().collect();
        row_param_order.sort();

        let mut ctx = Self {
            type_param_order: type_param_order.clone(),
            row_param_order: row_param_order.clone(),
            type_param_names: FxHashMap::default(),
            row_param_names: FxHashMap::default(),
        };

        for (idx, id) in type_param_order.into_iter().enumerate() {
            ctx.type_param_names
                .insert(id, type_param_display_name(idx));
        }
        for (idx, id) in row_param_order.into_iter().enumerate() {
            ctx.row_param_names.insert(id, row_param_display_name(idx));
        }

        ctx
    }

    fn forall_names(&self) -> Vec<String> {
        let mut names: Vec<String> = vec![];
        names.extend(
            self.type_param_order
                .iter()
                .filter_map(|id| self.type_param_names.get(id).cloned()),
        );
        names.extend(
            self.row_param_order
                .iter()
                .filter_map(|id| self.row_param_names.get(id).cloned()),
        );

        names
    }
}

fn type_param_display_name(idx: usize) -> String {
    const NAMES: &[&str] = &["T", "U", "V", "W", "X", "Y", "Z"];
    if let Some(name) = NAMES.get(idx) {
        (*name).to_string()
    } else {
        format!("T{idx}")
    }
}

fn row_param_display_name(idx: usize) -> String {
    if idx == 0 {
        "R".to_string()
    } else {
        format!("R{idx}")
    }
}

fn collect_params_in_ty(
    ty: &crate::types::ty::Ty,
    type_params: &mut FxHashSet<crate::types::infer_ty::TypeParamId>,
    row_params: &mut FxHashSet<crate::types::infer_row::RowParamId>,
) {
    use crate::types::ty::Ty;

    match ty {
        Ty::Primitive(..) => {}
        Ty::Param(id) => {
            type_params.insert(*id);
        }
        Ty::Constructor { params, ret, .. } => {
            for param in params {
                collect_params_in_ty(param, type_params, row_params);
            }
            collect_params_in_ty(ret, type_params, row_params);
        }
        Ty::Func(param, ret) => {
            collect_params_in_ty(param, type_params, row_params);
            collect_params_in_ty(ret, type_params, row_params);
        }
        Ty::Tuple(items) => {
            for item in items {
                collect_params_in_ty(item, type_params, row_params);
            }
        }
        Ty::Record(.., row) => collect_params_in_row(row, type_params, row_params),
        Ty::Nominal { type_args, .. } => {
            for arg in type_args {
                collect_params_in_ty(arg, type_params, row_params);
            }
        }
    }
}

fn collect_params_in_row(
    row: &crate::types::row::Row,
    type_params: &mut FxHashSet<crate::types::infer_ty::TypeParamId>,
    row_params: &mut FxHashSet<crate::types::infer_row::RowParamId>,
) {
    use crate::types::row::Row;

    match row {
        Row::Empty(..) => {}
        Row::Param(id) => {
            row_params.insert(*id);
        }
        Row::Extend { row, ty, .. } => {
            collect_params_in_row(row, type_params, row_params);
            collect_params_in_ty(ty, type_params, row_params);
        }
    }
}

fn format_scheme(
    module: &Workspace,
    core: Option<&Workspace>,
    scheme: &crate::types::scheme::Scheme<crate::types::ty::Ty>,
) -> String {
    let ctx = TyFormatContext::from_scheme(scheme);
    let body = format_ty_in_context(module, core, &scheme.ty, &ctx);

    let foralls = ctx.forall_names();
    if foralls.is_empty() {
        body
    } else {
        format!("<{}>{body}", foralls.join(", "))
    }
}

fn format_ty(
    module: &Workspace,
    core: Option<&Workspace>,
    ty: &crate::types::ty::Ty,
) -> String {
    let ctx = TyFormatContext::from_ty(ty);
    format_ty_in_context(module, core, ty, &ctx)
}

fn format_ty_in_context(
    module: &Workspace,
    core: Option<&Workspace>,
    ty: &crate::types::ty::Ty,
    ctx: &TyFormatContext,
) -> String {
    use crate::types::ty::Ty;

    match ty {
        Ty::Primitive(symbol) => match *symbol {
            Symbol::Int => "Int".to_string(),
            Symbol::Float => "Float".to_string(),
            Symbol::Bool => "Bool".to_string(),
            Symbol::Void => "Void".to_string(),
            Symbol::RawPtr => "RawPtr".to_string(),
            Symbol::Byte => "Byte".to_string(),
            _ => symbol.to_string(),
        },
        Ty::Param(id) => ctx
            .type_param_names
            .get(id)
            .cloned()
            .unwrap_or_else(|| format!("{id:?}")),
        Ty::Constructor { name, params, ret } => {
            if params.is_empty() {
                name.name_str()
            } else {
                let params = params
                    .iter()
                    .map(|p| format_ty_in_context(module, core, p, ctx))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "({params}) -> {}",
                    format_ty_in_context(module, core, ret, ctx)
                )
            }
        }
        Ty::Func(param, ret) => {
            let params = param
                .clone()
                .uncurry_params()
                .iter()
                .map(|p| format_ty_in_context(module, core, p, ctx))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "({params}) -> {}",
                format_ty_in_context(module, core, ret, ctx)
            )
        }
        Ty::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(|t| format_ty_in_context(module, core, t, ctx))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Ty::Record(.., row) => format!("{{ {} }}", format_row_in_context(module, core, row, ctx)),
        Ty::Nominal { symbol, type_args } => {
            let base = module
                .resolved_names
                .symbol_names
                .get(symbol)
                .or_else(|| core.and_then(|core| core.resolved_names.symbol_names.get(symbol)))
                .cloned()
                .or_else(|| {
                    if *symbol == Symbol::String {
                        Some("String".to_string())
                    } else if *symbol == Symbol::Array {
                        Some("Array".to_string())
                    } else {
                        None
                    }
                })
                .unwrap_or_else(|| symbol.to_string());

            if type_args.is_empty() {
                base
            } else {
                let args = type_args
                    .iter()
                    .map(|t| format_ty_in_context(module, core, t, ctx))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{base}<{args}>")
            }
        }
    }
}

fn format_row_in_context(
    module: &Workspace,
    core: Option<&Workspace>,
    row: &crate::types::row::Row,
    ctx: &TyFormatContext,
) -> String {
    use crate::types::row::Row;

    let mut fields = vec![];
    let mut cursor = row;
    loop {
        match cursor {
            Row::Empty(..) | Row::Param(..) => break,
            Row::Extend { row, label, ty } => {
                fields.push((label.clone(), ty.clone()));
                cursor = row;
            }
        }
    }
    fields.reverse();

    let mut rendered = fields
        .into_iter()
        .map(|(label, ty)| format!("{label}: {}", format_ty_in_context(module, core, &ty, ctx)))
        .collect::<Vec<_>>();

    if let Row::Param(param) = cursor {
        let name = ctx
            .row_param_names
            .get(param)
            .cloned()
            .unwrap_or_else(|| format!("{param:?}"));
        rendered.push(format!("..{name}"));
    }

    rendered.join(", ")
}
