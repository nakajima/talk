use super::*;

pub(super) fn generic_symbols(
    generics: &[crate::node_kinds::generic_decl::GenericDecl],
) -> Vec<Symbol> {
    generics
        .iter()
        .filter_map(|g| g.name.symbol().ok())
        .collect()
}

pub(super) fn param_subst(params: &[Symbol], args: &[Ty]) -> FxHashMap<Symbol, Ty> {
    params.iter().copied().zip(args.iter().cloned()).collect()
}

/// A nominal's declared type parameters (struct or enum). Catalog-only, so
/// both the elaborator and the collector can call it.
pub(super) fn nominal_params(catalog: &TypeCatalog, symbol: Symbol) -> Vec<Symbol> {
    catalog
        .structs
        .get(&symbol)
        .map(|info| info.params.clone())
        .or_else(|| catalog.enums.get(&symbol).map(|info| info.params.clone()))
        .unwrap_or_default()
}

/// The `where` predicates a nominal use must satisfy, instantiated at its
/// type arguments — its well-formedness obligation (THIH §11.6: a type
/// application carries its declared context). Catalog-only.
pub(super) fn nominal_predicates_for(catalog: &TypeCatalog, ty: &Ty) -> Vec<Predicate> {
    let Ty::Nominal(symbol, args) = ty else {
        return vec![];
    };
    let (params, predicates) = catalog
        .structs
        .get(symbol)
        .map(|info| (info.params.clone(), info.predicates.clone()))
        .or_else(|| {
            catalog
                .enums
                .get(symbol)
                .map(|info| (info.params.clone(), info.predicates.clone()))
        })
        .unwrap_or_default();
    let substitution = param_subst(&params, args);
    predicates
        .into_iter()
        .map(|predicate| {
            predicate.substitute(&substitution, &Default::default(), &Default::default())
        })
        .collect()
}

/// Dependency analysis for binding groups (THIH §11.6.2): collect each
/// binder's references to other top-level binders (including from struct
/// member bodies), condense with kosaraju SCC, and return groups in
/// dependencies-first order.
pub(super) fn binding_groups(decls: &IndexMap<Symbol, TopEntry<'_>>) -> Vec<Vec<Symbol>> {
    use derive_visitor::{Drive, Visitor};
    use petgraph::algo::kosaraju_scc;
    use petgraph::graph::DiGraph;

    #[derive(Visitor)]
    #[visitor(Expr(enter))]
    struct RefCollector {
        refs: rustc_hash::FxHashSet<Symbol>,
    }
    impl RefCollector {
        fn enter_expr(&mut self, expr: &Expr) {
            match &expr.kind {
                ExprKind::Variable(name) | ExprKind::Constructor(name) => {
                    if let Ok(symbol) = name.symbol() {
                        self.refs.insert(symbol);
                    }
                }
                _ => {}
            }
        }
    }

    let mut graph = DiGraph::<Symbol, ()>::new();
    let mut index = FxHashMap::default();
    for symbol in decls.keys() {
        index.insert(*symbol, graph.add_node(*symbol));
    }
    for (symbol, entry) in decls {
        let mut collector = RefCollector {
            refs: Default::default(),
        };
        match entry {
            TopEntry::Let { rhs: Some(rhs), .. } => rhs.drive(&mut collector),
            TopEntry::Struct { decl } => {
                if let DeclKind::Struct { body, .. } = &decl.kind {
                    for member in &body.decls {
                        match &member.kind {
                            DeclKind::Method { func, .. } => func.drive(&mut collector),
                            DeclKind::Init { body, .. } => body.drive(&mut collector),
                            _ => {}
                        }
                    }
                }
            }
            _ => {}
        }
        for reference in collector.refs {
            if reference != *symbol
                && let Some(&target) = index.get(&reference)
            {
                graph.add_edge(index[symbol], target, ());
            }
        }
    }

    kosaraju_scc(&graph)
        .iter()
        .map(|scc| scc.iter().map(|i| graph[*i]).collect())
        .collect()
}

pub(super) fn head_symbol(ty: &Ty) -> Symbol {
    match ty {
        Ty::Nominal(symbol, _) => *symbol,
        _ => Symbol::Main,
    }
}

/// One-way structural match: wherever `pattern` mentions an associated-type
/// parameter and `witness` is concrete, record the binding (Chakravarty,
/// Keller & Peyton Jones, ICFP 2005 — instances determine their synonyms).
pub(super) fn collect_assoc_bindings(
    pattern: &Ty,
    witness: &Ty,
    bindings: &mut FxHashMap<Symbol, Ty>,
) {
    // The shared matcher binds every param; keep only associated-type params,
    // since `conformance.assoc` holds associated-type bindings exclusively.
    let mut all = FxHashMap::default();
    crate::types::ty::match_pattern(pattern, witness, &mut all);
    for (symbol, ty) in all {
        if matches!(symbol, Symbol::AssociatedType(_)) {
            bindings.entry(symbol).or_insert(ty);
        }
    }
}

pub(super) fn self_context_param(ty: &Ty) -> Option<Symbol> {
    match ty {
        Ty::Param(param) => Some(*param),
        _ => None,
    }
}

pub(super) fn predicate_mentions_context(
    predicate: &Predicate,
    universe: &FxHashSet<Symbol>,
    self_ty: Option<&Ty>,
) -> bool {
    let mut found = FxHashSet::default();
    collect_predicate_params(predicate, Some(universe), &mut found);
    !found.is_empty()
        || self_ty.is_some_and(|self_ty| match predicate {
            Predicate::TypeEq(lhs, rhs) => {
                ty_mentions_self(lhs, self_ty) || ty_mentions_self(rhs, self_ty)
            }
            Predicate::Conforms { ty, .. } => ty_mentions_self(ty, self_ty),
            Predicate::HasMember {
                receiver, member, ..
            } => ty_mentions_self(receiver, self_ty) || ty_mentions_self(member, self_ty),
            Predicate::RowEq(lhs, rhs) => {
                row_mentions_self(lhs, self_ty) || row_mentions_self(rhs, self_ty)
            }
            Predicate::EffectEq(..) => false,
        })
}

pub(super) fn row_mentions_self(row: &Row, self_ty: &Ty) -> bool {
    matches!(
        row.try_visit(&mut |visited| {
            if visited == self_ty {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        }),
        ControlFlow::Break(())
    )
}

pub(super) fn ty_mentions_self(ty: &Ty, self_ty: &Ty) -> bool {
    matches!(
        ty.try_visit(&mut |visited| {
            if visited == self_ty {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        }),
        ControlFlow::Break(())
    )
}

/// Collect the type parameters a predicate mentions. `universe` of `None`
/// accepts every parameter; `Some(set)` keeps only those in the set.
pub(super) fn collect_predicate_params(
    predicate: &Predicate,
    universe: Option<&FxHashSet<Symbol>>,
    out: &mut FxHashSet<Symbol>,
) {
    let _ = predicate.try_visit(&mut |visited| {
        collect_params_from_visited_ty(visited, universe, out);
        ControlFlow::<()>::Continue(())
    });
    if let Predicate::RowEq(lhs, rhs) = predicate {
        collect_row_tail_param(lhs, universe, out);
        collect_row_tail_param(rhs, universe, out);
    }
}

pub(super) fn collect_ty_params(
    ty: &Ty,
    universe: Option<&FxHashSet<Symbol>>,
    out: &mut FxHashSet<Symbol>,
) {
    let _ = ty.try_visit(&mut |visited| {
        collect_params_from_visited_ty(visited, universe, out);
        ControlFlow::<()>::Continue(())
    });
}

pub(super) fn collect_params_from_visited_ty(
    ty: &Ty,
    universe: Option<&FxHashSet<Symbol>>,
    out: &mut FxHashSet<Symbol>,
) {
    match ty {
        Ty::Param(param) if universe.is_none_or(|u| u.contains(param)) => {
            out.insert(*param);
        }
        Ty::Record(row) => collect_row_tail_param(row, universe, out),
        _ => {}
    }
}

pub(super) fn collect_row_tail_param(
    row: &Row,
    universe: Option<&FxHashSet<Symbol>>,
    out: &mut FxHashSet<Symbol>,
) {
    if let Some(RowTail::Param(param)) = &row.tail
        && universe.is_none_or(|u| u.contains(param))
    {
        out.insert(*param);
    }
}

/// Does the type mention the rigid parameter anywhere (including row
/// tails)? Used to attach held member constraints to the schemes that
/// quantify their receivers.
pub(super) fn predicate_mentions_param(predicate: &Predicate, param: Symbol) -> bool {
    if let Predicate::RowEq(lhs, rhs) = predicate
        && (row_tail_mentions_param(lhs, param) || row_tail_mentions_param(rhs, param))
    {
        return true;
    }
    matches!(
        predicate.try_visit(&mut |visited| {
            if visited_ty_mentions_param(visited, param) {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        }),
        ControlFlow::Break(())
    )
}

pub(super) fn ty_mentions_param(ty: &Ty, param: Symbol) -> bool {
    matches!(
        ty.try_visit(&mut |visited| {
            if visited_ty_mentions_param(visited, param) {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        }),
        ControlFlow::Break(())
    )
}

pub(super) fn visited_ty_mentions_param(ty: &Ty, param: Symbol) -> bool {
    match ty {
        Ty::Param(sym) => *sym == param,
        Ty::Record(row) => row_tail_mentions_param(row, param),
        _ => false,
    }
}

pub(super) fn row_tail_mentions_param(row: &Row, param: Symbol) -> bool {
    matches!(&row.tail, Some(RowTail::Param(sym)) if *sym == param)
}

pub(super) fn decl_kind_name(kind: &DeclKind) -> &'static str {
    match kind {
        DeclKind::Import(_) => "imports",
        DeclKind::Effect { .. } => "effect declarations",
        DeclKind::Struct { .. } => "struct declarations",
        DeclKind::Let { .. } => "destructuring let bindings",
        DeclKind::Protocol { .. } => "protocol declarations",
        DeclKind::Init { .. } => "initializers",
        DeclKind::Property { .. } => "properties",
        DeclKind::Method { .. } => "methods",
        DeclKind::Extend { .. } => "extend declarations",
        DeclKind::Enum { .. } => "enum declarations",
        DeclKind::EnumVariant { .. } => "enum variants",
        DeclKind::Associated { .. } => "associated type declarations",
        DeclKind::Func(_) => "function declarations",
        DeclKind::FuncSignature(_) => "function signatures",
        DeclKind::MethodRequirement(_) => "method requirements",
        DeclKind::TypeAlias(..) => "type aliases",
    }
}
