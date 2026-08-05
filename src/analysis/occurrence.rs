//! Shared semantic position resolution (CLEAN-02): which symbol a byte
//! offset denotes, the span of that occurrence, and what kind of
//! occurrence it is. Definition, rename, and future refactors consume
//! this one result; each keeps only its own follow-up (location
//! mapping, collision detection, edit construction).
//!
//! The resolver preserves the union of the behaviors definition and
//! rename grew independently: it descends through nominal generic
//! arguments, `Self`, tuples, and records (definition's coverage) and
//! resolves associated-type binding names, nominal-path members,
//! construction-argument labels, and named imports (rename's coverage).

use crate::analysis::workspace::Workspace;
use crate::analysis::{DocumentId, TextRange, node_ids_at_offset, span_contains};
use crate::name_resolution::symbol::Symbol;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OccurrenceKind {
    /// The symbol's own declaration site.
    Declaration,
    /// A name or type reference.
    Reference,
    /// A named import entry; the symbol is the target module's export.
    ImportAlias,
    /// A member access: property, method, variant, or associated type.
    Member,
    /// An associated-type binding name in an `any P<A = T>` annotation.
    AssociatedTypeBinding,
    /// An effect name in a call, handler, or effect set.
    Effect,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Occurrence {
    pub symbol: Symbol,
    pub range: TextRange,
    pub kind: OccurrenceKind,
}

impl Occurrence {
    fn new(symbol: Symbol, start: u32, end: u32, kind: OccurrenceKind) -> Self {
        Self {
            symbol,
            range: TextRange::new(start, end),
            kind,
        }
    }

    fn span(symbol: Symbol, span: crate::span::Span, kind: OccurrenceKind) -> Self {
        Self::new(symbol, span.start, span.end, kind)
    }
}

/// The semantic occurrence at `byte_offset`, or `None` when the offset
/// denotes nothing nameable. Import entries are considered before
/// interior nodes so an import decl's own spans win.
pub fn occurrence_at(
    module: &Workspace,
    document_id: &DocumentId,
    byte_offset: u32,
) -> Option<Occurrence> {
    let file_id = *module.document_to_file_id.get(document_id)?;
    let ast = module
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())?;

    for root in &ast.roots {
        let crate::node::Node::Decl(decl) = root else {
            continue;
        };
        if let Some(occurrence) = import_occurrence_at(module, &ast.path, decl, byte_offset) {
            return Some(occurrence);
        }
    }

    for node_id in node_ids_at_offset(ast, byte_offset) {
        let Some(node) = ast.find(node_id) else {
            continue;
        };

        let occurrence = match node {
            crate::node::Node::Expr(expr) => occurrence_from_expr(module, &expr, byte_offset),
            crate::node::Node::Stmt(stmt) => occurrence_from_stmt(module, &stmt, byte_offset),
            crate::node::Node::TypeAnnotation(ty) => {
                occurrence_from_type_annotation(module, &ty, byte_offset)
            }
            crate::node::Node::Decl(decl) => occurrence_from_decl(module, &decl, byte_offset),
            crate::node::Node::Parameter(param) => {
                if span_contains(param.name_span, byte_offset) {
                    param.name.symbol().ok().map(|symbol| {
                        Occurrence::span(symbol, param.name_span, OccurrenceKind::Declaration)
                    })
                } else {
                    None
                }
            }
            crate::node::Node::Func(func) => {
                if span_contains(func.name_span, byte_offset) {
                    func.name.symbol().ok().map(|symbol| {
                        Occurrence::span(symbol, func.name_span, OccurrenceKind::Declaration)
                    })
                } else {
                    effect_occurrence_at_offset(&func.effects, byte_offset)
                }
            }
            crate::node::Node::FuncSignature(sig) => {
                let meta = ast.meta.get(&sig.id)?;
                let (start, end) = meta
                    .identifiers
                    .first()
                    .map(|token| (token.start, token.end))?;
                if start <= byte_offset && byte_offset <= end {
                    sig.name.symbol().ok().map(|symbol| {
                        Occurrence::new(symbol, start, end, OccurrenceKind::Declaration)
                    })
                } else {
                    effect_occurrence_at_offset(&sig.effects, byte_offset)
                }
            }
            crate::node::Node::GenericDecl(generic) => {
                if span_contains(generic.name_span, byte_offset) {
                    generic.name.symbol().ok().map(|symbol| {
                        Occurrence::span(symbol, generic.name_span, OccurrenceKind::Declaration)
                    })
                } else {
                    None
                }
            }
            crate::node::Node::Pattern(pattern) => match &pattern.kind {
                crate::node_kinds::pattern::PatternKind::Bind(name) => {
                    let meta = ast.meta.get(&pattern.id)?;
                    let (start, end) = identifier_span_at_offset(meta, byte_offset)?;
                    if start <= byte_offset && byte_offset <= end {
                        name.symbol().ok().map(|symbol| {
                            Occurrence::new(symbol, start, end, OccurrenceKind::Declaration)
                        })
                    } else {
                        None
                    }
                }
                crate::node_kinds::pattern::PatternKind::Variant {
                    variant_name_span, ..
                } => {
                    if !span_contains(*variant_name_span, byte_offset) {
                        None
                    } else {
                        member_resolution_symbol(module.types.member_resolutions.get(&pattern.id))
                            .map(|symbol| {
                                Occurrence::span(symbol, *variant_name_span, OccurrenceKind::Member)
                            })
                    }
                }
                _ => None,
            },
            _ => None,
        };

        if occurrence.is_some() {
            return occurrence;
        }
    }

    None
}

fn occurrence_from_expr(
    module: &Workspace,
    expr: &crate::node_kinds::expr::Expr,
    byte_offset: u32,
) -> Option<Occurrence> {
    use crate::node_kinds::expr::ExprKind;

    match &expr.kind {
        ExprKind::Variable(name) | ExprKind::Constructor(name, ..) => name
            .symbol()
            .ok()
            .map(|symbol| Occurrence::span(symbol, expr.span, OccurrenceKind::Reference)),
        ExprKind::Call { callee, args, .. } => {
            if span_contains(callee.span, byte_offset) {
                occurrence_from_expr(module, callee, byte_offset)
            } else {
                construction_arg_occurrence_at_offset(module, callee, args, byte_offset)
            }
        }
        ExprKind::Member(_, _, label_span) => {
            if !span_contains(*label_span, byte_offset) {
                return None;
            }
            member_resolution_symbol(module.types.member_resolutions.get(&expr.id))
                .map(|symbol| Occurrence::span(symbol, *label_span, OccurrenceKind::Member))
        }
        ExprKind::CallEffect {
            effect_name,
            effect_name_span,
            ..
        } => {
            if !effect_span_contains(*effect_name_span, byte_offset) {
                return None;
            }
            effect_name
                .symbol()
                .ok()
                .map(|symbol| Occurrence::span(symbol, *effect_name_span, OccurrenceKind::Effect))
        }
        _ => None,
    }
}

/// A construction argument label (`Point(x: 1)`, cursor on `x`) denotes
/// the property it initializes.
fn construction_arg_occurrence_at_offset(
    module: &Workspace,
    callee: &crate::node_kinds::expr::Expr,
    args: &[crate::node_kinds::call_arg::CallArg],
    byte_offset: u32,
) -> Option<Occurrence> {
    let struct_info = module
        .types
        .catalog
        .structs
        .get(&construction_callee_symbol(callee)?)?;
    args.iter().find_map(|arg| {
        if !span_contains(arg.label_span, byte_offset) {
            return None;
        }
        struct_info
            .fields
            .get(&arg.label.to_string())
            .map(|(symbol, _)| Occurrence::span(*symbol, arg.label_span, OccurrenceKind::Member))
    })
}

pub(crate) fn construction_callee_symbol(callee: &crate::node_kinds::expr::Expr) -> Option<Symbol> {
    use crate::node_kinds::expr::ExprKind;

    match &callee.kind {
        ExprKind::Constructor(name, ..) | ExprKind::Variable(name) => name.symbol().ok(),
        _ => None,
    }
}

pub(crate) fn member_resolution_symbol(
    resolution: Option<&crate::types::output::MemberResolution>,
) -> Option<Symbol> {
    match resolution? {
        crate::types::output::MemberResolution::Direct(symbol) => Some(*symbol),
        crate::types::output::MemberResolution::ViaConformance { witness, .. } => Some(*witness),
        crate::types::output::MemberResolution::ViaRequirement { requirement, .. } => {
            Some(*requirement)
        }
    }
}

fn occurrence_from_stmt(
    module: &Workspace,
    stmt: &crate::node_kinds::stmt::Stmt,
    byte_offset: u32,
) -> Option<Occurrence> {
    use crate::node_kinds::stmt::StmtKind;

    match &stmt.kind {
        StmtKind::Expr(expr) => span_contains(expr.span, byte_offset)
            .then(|| occurrence_from_expr(module, expr, byte_offset))?,
        StmtKind::Return(Some(expr)) => span_contains(expr.span, byte_offset)
            .then(|| occurrence_from_expr(module, expr, byte_offset))?,
        StmtKind::If(cond, ..) => span_contains(cond.span, byte_offset)
            .then(|| occurrence_from_expr(module, cond, byte_offset))?,
        StmtKind::Loop(Some(cond), ..) => span_contains(cond.span, byte_offset)
            .then(|| occurrence_from_expr(module, cond, byte_offset))?,
        StmtKind::Assignment(lhs, rhs) => {
            if span_contains(lhs.span, byte_offset) {
                occurrence_from_expr(module, lhs, byte_offset)
            } else if span_contains(rhs.span, byte_offset) {
                occurrence_from_expr(module, rhs, byte_offset)
            } else {
                None
            }
        }
        StmtKind::For { iterable, .. } => span_contains(iterable.span, byte_offset)
            .then(|| occurrence_from_expr(module, iterable, byte_offset))?,
        StmtKind::Resume(Some(expr)) => span_contains(expr.span, byte_offset)
            .then(|| occurrence_from_expr(module, expr, byte_offset))?,
        StmtKind::Handling {
            effect_name,
            effect_name_span,
            ..
        } => {
            if !effect_span_contains(*effect_name_span, byte_offset) {
                return None;
            }
            effect_name
                .symbol()
                .ok()
                .map(|symbol| Occurrence::span(symbol, *effect_name_span, OccurrenceKind::Effect))
        }
        _ => None,
    }
}

fn occurrence_from_type_application(
    module: &Workspace,
    head: &crate::node_kinds::type_application::TypeApplication,
    byte_offset: u32,
) -> Option<Occurrence> {
    head.args
        .iter()
        .flat_map(|arg| arg.annotations())
        .find_map(|annotation| occurrence_from_type_annotation(module, annotation, byte_offset))
        .or_else(|| {
            if !nominal_name_span_contains(&head.name, head.name_span, byte_offset) {
                return None;
            }
            head.name
                .symbol()
                .ok()
                .map(|symbol| Occurrence::span(symbol, head.name_span, OccurrenceKind::Reference))
        })
}

fn occurrence_from_type_annotation(
    module: &Workspace,
    ty: &crate::node_kinds::type_annotation::TypeAnnotation,
    byte_offset: u32,
) -> Option<Occurrence> {
    use crate::node_kinds::type_annotation::TypeAnnotationKind;

    match &ty.kind {
        TypeAnnotationKind::Borrow { inner, .. }
        | TypeAnnotationKind::Unique { inner }
        | TypeAnnotationKind::Quantified { inner, .. } => {
            occurrence_from_type_annotation(module, inner, byte_offset)
        }
        TypeAnnotationKind::Nominal {
            name,
            name_span,
            generics,
        } => generics
            .iter()
            .flat_map(|generic| generic.annotations())
            .find_map(|generic| occurrence_from_type_annotation(module, generic, byte_offset))
            .or_else(|| {
                if !nominal_name_span_contains(name, *name_span, byte_offset) {
                    return None;
                }
                name.symbol()
                    .ok()
                    .map(|symbol| Occurrence::span(symbol, *name_span, OccurrenceKind::Reference))
            }),
        TypeAnnotationKind::SelfType(name) => name
            .symbol()
            .ok()
            .map(|symbol| Occurrence::span(symbol, ty.span, OccurrenceKind::Reference)),
        TypeAnnotationKind::Any {
            protocol,
            assoc_bindings,
        } => occurrence_from_type_annotation(module, protocol, byte_offset).or_else(|| {
            assoc_bindings.iter().find_map(|binding| {
                if span_contains(binding.name_span, byte_offset) {
                    symbol_for_any_assoc_binding(module, protocol, binding).map(|symbol| {
                        Occurrence::span(
                            symbol,
                            binding.name_span,
                            OccurrenceKind::AssociatedTypeBinding,
                        )
                    })
                } else {
                    occurrence_from_type_annotation(module, &binding.value, byte_offset)
                }
            })
        }),
        TypeAnnotationKind::NominalPath {
            base,
            member,
            member_span,
            ..
        } => {
            if span_contains(*member_span, byte_offset) {
                symbol_for_associated_type_member(module, base, member)
                    .map(|symbol| Occurrence::span(symbol, *member_span, OccurrenceKind::Member))
            } else {
                occurrence_from_type_annotation(module, base, byte_offset)
            }
        }
        TypeAnnotationKind::Func {
            params,
            effects,
            returns,
        } => params
            .iter()
            .find_map(|param| occurrence_from_type_annotation(module, param, byte_offset))
            .or_else(|| effect_occurrence_at_offset(effects, byte_offset))
            .or_else(|| occurrence_from_type_annotation(module, returns, byte_offset)),
        TypeAnnotationKind::Tuple(items) => items
            .iter()
            .find_map(|item| occurrence_from_type_annotation(module, item, byte_offset)),
        TypeAnnotationKind::Record { fields } => fields
            .iter()
            .find_map(|field| occurrence_from_type_annotation(module, &field.value, byte_offset)),
    }
}

fn occurrence_from_decl(
    module: &Workspace,
    decl: &crate::node_kinds::decl::Decl,
    byte_offset: u32,
) -> Option<Occurrence> {
    use crate::node_kinds::decl::DeclKind;

    match &decl.kind {
        DeclKind::Struct {
            name, name_span, ..
        }
        | DeclKind::Protocol {
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
            name.symbol()
                .ok()
                .map(|symbol| Occurrence::span(symbol, *name_span, OccurrenceKind::Declaration))
        }
        DeclKind::TypeAlias(name, name_span, ..) => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol()
                .ok()
                .map(|symbol| Occurrence::span(symbol, *name_span, OccurrenceKind::Declaration))
        }
        DeclKind::EnumVariant {
            name, name_span, ..
        } => {
            if !span_contains(*name_span, byte_offset) {
                return None;
            }
            name.symbol()
                .ok()
                .map(|symbol| Occurrence::span(symbol, *name_span, OccurrenceKind::Declaration))
        }
        DeclKind::Extend { head, .. } => {
            occurrence_from_type_application(module, head, byte_offset)
        }
        _ => None,
    }
}

/// A named import entry (`use package::other::{ answer }`) denotes the
/// symbol the target module exports under that name.
fn import_occurrence_at(
    module: &Workspace,
    source_path: &str,
    decl: &crate::node_kinds::decl::Decl,
    byte_offset: u32,
) -> Option<Occurrence> {
    use crate::node_kinds::decl::{DeclKind, ImportedSymbols};

    let DeclKind::Import(import) = &decl.kind else {
        return None;
    };
    let ImportedSymbols::Named(imported_symbols) = &import.symbols else {
        return None;
    };

    let imported = imported_symbols
        .iter()
        .find(|imported| span_contains(imported.span, byte_offset))?;

    let symbol = match &import.path {
        crate::node_kinds::decl::ImportPath::Local(_) => {
            symbol_exported_by_import(module, source_path, import, &imported.name)?
        }
        crate::node_kinds::decl::ImportPath::Package(package) => module
            .stdlib_workspace_for_package(package)?
            .exported_symbol(&imported.name)?,
    };

    Some(Occurrence::span(
        symbol,
        imported.span,
        OccurrenceKind::ImportAlias,
    ))
}

/// The symbol `name` refers to in the target of a local import.
pub(crate) fn symbol_exported_by_import(
    module: &Workspace,
    source_path: &str,
    import: &crate::node_kinds::decl::Import,
    name: &str,
) -> Option<Symbol> {
    let target_file_id = target_file_id_for_import(module, source_path, &import.path)?;
    let target_scope_id = crate::node_id::NodeID(target_file_id, 0);
    let target_scope = module.resolved_names.scopes.get(&target_scope_id)?;

    target_scope
        .types
        .get(name)
        .or_else(|| target_scope.values.get(name))
        .copied()
}

fn target_file_id_for_import(
    module: &Workspace,
    source_path: &str,
    import_path: &crate::node_kinds::decl::ImportPath,
) -> Option<crate::node_id::FileID> {
    use crate::compiling::module_path::LocalModulePaths;
    use crate::node_kinds::decl::ImportPath;

    let target_path = match import_path {
        ImportPath::Local(module_path) => {
            LocalModulePaths::new(&module.source_root).resolve(source_path, module_path)?
        }
        ImportPath::Package(_) => return None,
    };

    document_id_for_path(module, &target_path)
        .and_then(|document_id| module.document_to_file_id.get(&document_id).copied())
}

pub(crate) fn document_id_for_path(
    module: &Workspace,
    path: &std::path::Path,
) -> Option<DocumentId> {
    let target = normalize_path(path);
    for (idx, ast) in module.asts.iter().enumerate() {
        let Some(ast) = ast else {
            continue;
        };
        if normalize_path(std::path::Path::new(&ast.path)) == target {
            return module.file_id_to_document.get(idx).cloned();
        }
    }
    None
}

pub(crate) fn normalize_path(path: &std::path::Path) -> std::path::PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

pub(crate) fn symbol_for_any_assoc_binding(
    module: &Workspace,
    protocol: &crate::node_kinds::type_annotation::TypeAnnotation,
    binding: &crate::node_kinds::type_annotation::AnyAssocBinding,
) -> Option<Symbol> {
    let crate::node_kinds::type_annotation::TypeAnnotationKind::Nominal { name, .. } =
        &protocol.kind
    else {
        return None;
    };
    let protocol = name.symbol().ok()?;
    module
        .types
        .catalog
        .associated_type_in(protocol, &binding.name.name_str())
        .map(|(_, assoc)| assoc)
}

pub(crate) fn symbol_for_associated_type_member(
    module: &Workspace,
    base: &crate::node_kinds::type_annotation::TypeAnnotation,
    member: &crate::label::Label,
) -> Option<Symbol> {
    let label = member.to_string();
    let base_symbol = match &base.kind {
        crate::node_kinds::type_annotation::TypeAnnotationKind::Nominal { name, .. }
        | crate::node_kinds::type_annotation::TypeAnnotationKind::SelfType(name) => {
            name.symbol().ok()?
        }
        _ => return None,
    };

    if let Some(info) = module.types.catalog.protocols.get(&base_symbol) {
        return info.assoc.get(&label).copied().or_else(|| {
            module
                .types
                .catalog
                .associated_type_in(base_symbol, &label)
                .map(|(_, assoc)| assoc)
        });
    }

    module
        .types
        .catalog
        .param_bounds
        .get(&base_symbol)?
        .iter()
        .find_map(|protocol| {
            module
                .types
                .catalog
                .associated_type_in_ref(protocol, &label)
                .map(|(_, assoc)| assoc)
        })
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

/// A qualified nominal name (`a::b::Name`) lexes as one name; the
/// recorded span may only cover the last component, so the qualified
/// prefix counts as part of the occurrence too.
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

fn effect_occurrence_at_offset(
    effects: &crate::node_kinds::func::EffectSet,
    byte_offset: u32,
) -> Option<Occurrence> {
    for (name, span) in effects.names.iter().zip(effects.spans.iter()) {
        if effect_span_contains(*span, byte_offset) {
            return name
                .symbol()
                .ok()
                .map(|symbol| Occurrence::span(symbol, *span, OccurrenceKind::Effect));
        }
    }
    None
}

/// Effect name spans exclude the leading tick; accept it too.
fn effect_span_contains(span: crate::span::Span, byte_offset: u32) -> bool {
    span_contains(span, byte_offset) || (span.start > 0 && byte_offset == span.start - 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::{DocumentInput, rename_at};

    fn workspace(code: &str) -> Workspace {
        let doc = DocumentInput {
            id: "main.tlk".to_string(),
            path: "main.tlk".to_string(),
            version: 0,
            text: code.into(),
        };
        Workspace::new(vec![doc]).expect("workspace")
    }

    fn occurrence(code: &str, needle: &str) -> Occurrence {
        let offset = code.rfind(needle).expect("needle in code") as u32;
        occurrence_at(&workspace(code), &"main.tlk".to_string(), offset)
            .expect("occurrence at needle")
    }

    #[test]
    fn occurrence_reports_declaration_kind() {
        let code = "struct Box {\n\tlet value: Int\n}\n";
        let found = occurrence(code, "Box");
        assert_eq!(found.kind, OccurrenceKind::Declaration);
        assert_eq!(
            &code[found.range.start as usize..found.range.end as usize],
            "Box"
        );
    }

    #[test]
    fn occurrence_reports_reference_kind() {
        let code = "let greeting = 1\ngreeting\n";
        let found = occurrence(code, "greeting");
        assert_eq!(found.kind, OccurrenceKind::Reference);
    }

    #[test]
    fn occurrence_reports_member_kind() {
        let code = "struct Point {\n\tlet x: Int\n}\nlet p = Point(x: 1)\np.x\n";
        let offset = code.rfind(".x").expect("member") as u32 + 1;
        let found =
            occurrence_at(&workspace(code), &"main.tlk".to_string(), offset).expect("occurrence");
        assert_eq!(found.kind, OccurrenceKind::Member);
    }

    #[test]
    fn occurrence_reports_effect_kind() {
        let code = "effect 'bail(error) -> Never\nfunc build() 'bail -> Int {\n\t'bail(\"stop\")\n}\nbuild()\n";
        let found = occurrence(code, "'bail(\"");
        assert_eq!(found.kind, OccurrenceKind::Effect);
        assert_eq!(
            &code[found.range.start as usize..found.range.end as usize],
            "bail"
        );
    }

    #[test]
    fn occurrence_reports_nominal_path_member() {
        let code = "protocol Producer {\n\tassociated Element\n\tfunc get() -> Element\n}\nfunc first<T: Producer>(x: T) -> T.Element {\n\tx.get()\n}\n";
        let found = occurrence(code, "Element");
        assert_eq!(found.kind, OccurrenceKind::Member);
        assert_eq!(
            &code[found.range.start as usize..found.range.end as usize],
            "Element"
        );
    }

    #[test]
    fn occurrence_reports_any_assoc_binding() {
        let code = "protocol Producer {\n\tassociated Element\n\tfunc get() -> Element\n}\nstruct IntProducer {\n\tlet value: Int\n}\nextend IntProducer: Producer {\n\tfunc get() -> Int {\n\t\tself.value\n\t}\n}\nfunc make() -> any Producer<Element = Int> {\n\tIntProducer(value: 1)\n}\n";
        let found = occurrence(code, "Element =");
        assert_eq!(found.kind, OccurrenceKind::AssociatedTypeBinding);
    }

    #[test]
    fn occurrence_reports_construction_arg_labels() {
        let code = "struct Point {\n\tlet x: Int\n}\nlet p = Point(x: 1)\n";
        let found = occurrence(code, "x: 1");
        assert_eq!(found.kind, OccurrenceKind::Member);
        assert_eq!(
            &code[found.range.start as usize..found.range.end as usize],
            "x"
        );
    }

    #[test]
    fn occurrence_resolves_through_nested_generic_arguments() {
        let code =
            "struct Box<T> {\n\tlet value: T\n}\nfunc f(b: Box<Box<Int>>) -> Int {\n\t1\n}\n";
        let inner = code.rfind("Box<Int").expect("inner Box") as u32;
        let found =
            occurrence_at(&workspace(code), &"main.tlk".to_string(), inner).expect("occurrence");
        assert_eq!(found.kind, OccurrenceKind::Reference);
    }

    // Union behavior: rename previously fell through to `None` inside
    // nominal generic arguments, tuples, records, and `Self`; the shared
    // resolver covers them.
    #[test]
    fn rename_resolves_inside_generic_arguments_tuples_records_and_self() {
        let code = "struct Box<T> {\n\tlet value: T\n}\nextend Box {\n\tfunc get() -> Self {\n\t\tself\n\t}\n}\nfunc f(a: Box<Int>, b: (Int, Box<Int>), c: { value: Box<Int> }) -> Int {\n\t1\n}\n";
        let ws = workspace(code);
        let doc = "main.tlk".to_string();
        for needle in ["Box<Int>,", "Box<Int>)", "Box<Int> }", "Self"] {
            let offset = code.find(needle).expect("needle in code") as u32;
            assert!(
                rename_at(&ws, &doc, offset, "Crate").is_some(),
                "rename resolves at {needle}"
            );
        }
    }
}
