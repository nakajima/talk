use std::collections::HashMap;

use crate::Definition;
use crate::NameResolved;
use crate::SymbolID;
use crate::SymbolInfo;
use crate::SymbolKind;
use crate::SymbolTable;
use crate::compiling::compilation_session::SharedCompilationSession;
use crate::diagnostic::Diagnostic;
use crate::expr::Expr;
use crate::expr::Expr::*;
use crate::expr::IncompleteExpr;
use crate::expr::Pattern;
use crate::name::Name;
use crate::parser::ExprID;
use crate::scope_tree::ScopeId;
use crate::source_file::SourceFile;
use crate::span::Span;

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum NameResolverError {
    InvalidSelf,
    MissingMethodName,
    Unknown(String),
    UnresolvedName(String),
    Redeclaration(String, SymbolInfo),
}

impl NameResolverError {
    pub fn message(&self) -> String {
        match self {
            Self::InvalidSelf => "`self` can't be used outside type".to_string(),
            Self::UnresolvedName(string) => format!("Unknown identifier: {string}"),
            Self::MissingMethodName => "Missing method name".to_string(),
            Self::Unknown(string) => string.to_string(),
            Self::Redeclaration(name, _info) => format!("{name} already defined"),
        }
    }
}

pub struct NameResolver {
    scopes: Vec<HashMap<String, SymbolID>>,

    // For resolving `self` references
    type_symbol_stack: Vec<SymbolID>,

    // For resolving captures
    func_stack: Vec<(ExprID /* func expr id */, usize /* scope depth */)>,

    scope_tree_ids: Vec<ScopeId>,

    session: SharedCompilationSession,
}

impl NameResolver {
    pub fn new(symbol_table: &mut SymbolTable, session: SharedCompilationSession) -> Self {
        let initial_scope = symbol_table.build_name_scope();

        NameResolver {
            scopes: vec![initial_scope],
            type_symbol_stack: vec![],
            func_stack: vec![],
            scope_tree_ids: vec![],
            session,
        }
    }

    pub fn resolve(
        mut self,
        mut source_file: SourceFile,
        symbol_table: &mut SymbolTable,
    ) -> SourceFile<NameResolved> {
        // Create the root scope for the file
        #[allow(clippy::unwrap_used)]
        if !source_file.roots().is_empty()
            && let Some(first_root) = &source_file
                .meta
                .get(source_file.root_ids().first().unwrap())
            && let Some(last_root) = &source_file.meta.get(source_file.root_ids().last().unwrap())
        {
            let root_scope_id = source_file.scope_tree.new_scope(
                None,
                Span {
                    path: source_file.path.clone(),
                    start: first_root.start.start,
                    start_line: first_root.start.line,
                    start_col: first_root.start.col,
                    end: last_root.end.end,
                    end_line: last_root.end.line,
                    end_col: last_root.end.col,
                },
            );
            self.scope_tree_ids.push(root_scope_id);
        }
        self.resolve_nodes(&source_file.root_ids(), &mut source_file, symbol_table);
        source_file.to_resolved()
    }

    fn resolve_nodes(
        &mut self,
        node_ids: &[ExprID],
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) {
        self.hoist_protocols(node_ids, source_file, symbol_table);
        self.hoist_enums(node_ids, source_file, symbol_table);
        self.hoist_funcs(node_ids, source_file, symbol_table);
        self.hoise_structs(node_ids, source_file, symbol_table);

        for node_id in node_ids {
            let Some(expr) = &mut source_file.get_mut(node_id) else {
                continue;
            };
            log::trace!("Resolving: {expr:?}");
            match expr.clone() {
                LiteralInt(_) => continue,
                LiteralFloat(_) => continue,
                LiteralString(_) => continue,
                LiteralArray(items) => {
                    self.resolve_nodes(&items, source_file, symbol_table);
                }
                LiteralTrue | LiteralFalse => continue,
                Incomplete(incomplete) => match incomplete {
                    IncompleteExpr::Member(receiver) => {
                        if let Some(receiver) = receiver {
                            self.resolve_nodes(&[receiver], source_file, symbol_table);
                        }
                    }
                    IncompleteExpr::Func {
                        name,
                        params,
                        generics,
                        ret,
                        body,
                    } => {
                        self.resolve_func(
                            &name,
                            node_id,
                            &params.unwrap_or(vec![]),
                            &generics.unwrap_or(vec![]),
                            body.as_ref(),
                            &ret,
                            symbol_table,
                            source_file,
                        );
                    }
                },
                Struct {
                    name,
                    generics,
                    body,
                    conformances,
                } => {
                    match name {
                        Name::Raw(name_str) => {
                            let symbol_id = self.declare(
                                name_str.clone(),
                                SymbolKind::Struct,
                                node_id,
                                source_file,
                                symbol_table,
                            );
                            self.type_symbol_stack.push(symbol_id);
                            source_file.nodes.insert(
                                *node_id,
                                Struct {
                                    name: Name::Resolved(symbol_id, name_str),
                                    generics: generics.clone(),
                                    conformances: conformances.clone(),
                                    body,
                                },
                            );
                        }
                        _ => continue,
                    }

                    self.resolve_nodes(&generics, source_file, symbol_table);
                    self.resolve_nodes(&conformances, source_file, symbol_table);
                    self.resolve_nodes(&[body], source_file, symbol_table);
                    self.type_symbol_stack.pop();
                }
                Extend {
                    name,
                    generics,
                    body,
                    conformances,
                } => match name {
                    Name::Raw(name_str) => {
                        let Some(symbol_id) = self.lookup(&name_str) else {
                            log::error!("Did not find symbol for {name_str}");
                            if let Ok(mut session) = self.session.lock() {
                                session.add_diagnostic(Diagnostic::resolve(
                                    source_file.path.clone(),
                                    *node_id,
                                    NameResolverError::UnresolvedName(name_str),
                                ))
                            }
                            return;
                        };

                        log::trace!("Resolving extension {name_str} {symbol_id:?}");

                        let symbol_id = symbol_id.0;
                        self.type_symbol_stack.push(symbol_id);
                        source_file.nodes.insert(
                            *node_id,
                            Extend {
                                name: Name::Resolved(symbol_id, name_str),
                                generics: generics.clone(),
                                conformances: conformances.clone(),
                                body,
                            },
                        );

                        self.resolve_nodes(&generics, source_file, symbol_table);
                        self.resolve_nodes(&conformances, source_file, symbol_table);
                        self.resolve_nodes(&[body], source_file, symbol_table);
                        self.type_symbol_stack.pop();
                    }
                    _ => continue,
                },
                Break => (),
                Init(_, func_id) => {
                    let Some(symbol_id) = self.type_symbol_stack.last().cloned() else {
                        log::error!("no type found for initializer");
                        return;
                    };

                    symbol_table.add_initializer(symbol_id, *node_id);
                    self.resolve_nodes(&[func_id], source_file, symbol_table);
                    source_file
                        .nodes
                        .insert(*node_id, Expr::Init(Some(symbol_id), func_id));
                }
                Property {
                    type_repr,
                    default_value,
                    name,
                } => {
                    let mut to_resolve = vec![];
                    if let Some(type_repr) = type_repr {
                        to_resolve.push(type_repr)
                    }
                    if let Some(default_value) = default_value {
                        to_resolve.push(default_value)
                    }
                    self.resolve_nodes(&to_resolve, source_file, symbol_table);

                    if let Name::Raw(name_str) = name {
                        let symbol_id = self.declare(
                            name_str.clone(),
                            SymbolKind::Property,
                            node_id,
                            source_file,
                            symbol_table,
                        );

                        source_file.nodes.insert(
                            *node_id,
                            Expr::Property {
                                name: Name::Resolved(symbol_id, name_str),
                                type_repr,
                                default_value,
                            },
                        );
                    }
                }
                Return(rhs) => {
                    if let Some(rhs) = rhs {
                        self.resolve_nodes(&[rhs], source_file, symbol_table);
                    }
                }
                If(condi, conseq, alt) => {
                    if let Some(alt) = alt {
                        self.resolve_nodes(&[condi, conseq, alt], source_file, symbol_table);
                    } else {
                        self.resolve_nodes(&[condi, conseq], source_file, symbol_table);
                    }
                }
                Loop(cond, body) => {
                    if let Some(cond) = cond {
                        self.resolve_nodes(&[cond, body], source_file, symbol_table);
                    } else {
                        self.resolve_nodes(&[body], source_file, symbol_table);
                    }
                }
                Member(receiver, _member) => {
                    if let Some(receiver) = receiver {
                        self.resolve_nodes(&[receiver], source_file, symbol_table);
                    }
                }
                Let(name, rhs) => {
                    let name = match name {
                        Name::Raw(name_str) => {
                            let symbol_id = self.declare(
                                name_str.clone(),
                                SymbolKind::Local,
                                node_id,
                                source_file,
                                symbol_table,
                            );
                            Name::Resolved(symbol_id, name_str)
                        }
                        Name::Resolved(_, _) | Name::_Self(_) | Name::SelfType => name,
                    };

                    if let Some(rhs) = rhs {
                        self.resolve_nodes(&[rhs], source_file, symbol_table);
                    }

                    source_file.nodes.insert(*node_id, Let(name, rhs));
                }
                Call {
                    callee,
                    type_args,
                    args,
                } => {
                    let mut to_resolve = args.clone();
                    to_resolve.extend(type_args);
                    to_resolve.push(callee);

                    self.resolve_nodes(&to_resolve, source_file, symbol_table);
                }
                Assignment(lhs, rhs) => {
                    self.resolve_nodes(&[lhs, rhs], source_file, symbol_table);
                }
                Unary(_, expr_id) => {
                    self.resolve_nodes(&[expr_id], source_file, symbol_table);
                }
                Binary(lhs, _, rhs) => {
                    self.resolve_nodes(&[lhs, rhs], source_file, symbol_table);
                }
                Tuple(items) => {
                    self.resolve_nodes(&items, source_file, symbol_table);
                }
                Block(items) => {
                    self.start_scope(source_file, source_file.span(node_id));
                    self.hoist_funcs(&items, source_file, symbol_table);
                    self.resolve_nodes(&items, source_file, symbol_table);
                    self.end_scope();
                }
                Func {
                    generics,
                    params,
                    body,
                    ret,
                    name,
                    ..
                } => {
                    self.resolve_func(
                        &name,
                        node_id,
                        &params,
                        &generics,
                        Some(&body),
                        &ret,
                        symbol_table,
                        source_file,
                    );
                }
                CallArg { value, .. } => {
                    self.resolve_nodes(&[value], source_file, symbol_table);
                }
                Parameter(name, ty_repr) => {
                    if let Some(ty_repr) = ty_repr {
                        self.resolve_nodes(&[ty_repr], source_file, symbol_table);
                    };

                    match name {
                        Name::Raw(name_str) => {
                            let Some((symbol_id, _)) = self.lookup(&name_str) else {
                                if let Ok(mut session) = self.session.lock() {
                                    session.add_diagnostic(Diagnostic::resolve(
                                        source_file.path.clone(),
                                        *node_id,
                                        NameResolverError::UnresolvedName(name_str),
                                    ))
                                }
                                return;
                            };
                            symbol_table.add_map(source_file, node_id, &symbol_id);
                            source_file.nodes.insert(
                                *node_id,
                                Parameter(Name::Resolved(symbol_id, name_str), ty_repr),
                            );
                        }
                        Name::Resolved(_, _) | Name::_Self(_) | Name::SelfType => (),
                    }
                }
                Variable(name, _) => match name {
                    Name::Raw(name_str) => {
                        let name = if name_str == "self" {
                            if let Some(last_symbol) = self.type_symbol_stack.last() {
                                let name = Name::_Self(*last_symbol);
                                symbol_table.add_map(source_file, node_id, last_symbol);
                                name
                            } else {
                                if let Ok(mut lock) = self.session.lock() {
                                    lock.add_diagnostic(Diagnostic::resolve(
                                        source_file.path.clone(),
                                        *node_id,
                                        NameResolverError::InvalidSelf,
                                    ));
                                }
                                continue;
                            }
                        } else {
                            let Some((symbol_id, depth)) = self.lookup(&name_str) else {
                                if let Ok(mut session) = self.session.lock() {
                                    session.add_diagnostic(Diagnostic::resolve(
                                        source_file.path.clone(),
                                        *node_id,
                                        NameResolverError::UnresolvedName(name_str),
                                    ))
                                }

                                return;
                            };
                            log::info!("Replacing variable {name_str} with {symbol_id:?}");

                            symbol_table.add_map(source_file, node_id, &symbol_id);

                            // Check to see if this is a capture
                            if let Some((func_id, func_depth)) = self.func_stack.last()
                                && &depth < func_depth
                                && symbol_id.0 > 0
                            {
                                #[allow(clippy::unwrap_used)]
                                let Func { name, captures, .. } =
                                    source_file.get_mut(func_id).unwrap()
                                else {
                                    unreachable!()
                                };

                                if let Some(Name::Resolved(_, func_name)) = name
                                    && func_name == &name_str
                                {
                                    log::trace!("the same: {func_name:?} <> {name_str:?}");
                                } else {
                                    if !captures.contains(&symbol_id) {
                                        (*captures).push(symbol_id);
                                    }

                                    symbol_table.mark_as_captured(&symbol_id);
                                }
                            }

                            Name::Resolved(symbol_id, name_str)
                        };

                        source_file.nodes.insert(*node_id, Variable(name, None));
                    }
                    Name::Resolved(_, _) | Name::_Self(_) | Name::SelfType => (),
                },
                TypeRepr {
                    name,
                    generics,
                    conformances,
                    introduces_type,
                } => {
                    log::trace!(
                        "Resolving TypeRepr: {name:?}, generics: {generics:?}, is_param_decl: {introduces_type}"
                    );

                    let resolved_name_for_node = match name.clone() {
                        Name::Raw(raw_name_str) => {
                            if introduces_type {
                                // Declaration site of a type parameter (e.g., T in `enum Option<T>`)
                                // Ensure it's declared in the current scope.
                                let symbol_id = self.declare(
                                    raw_name_str.clone(),
                                    SymbolKind::TypeParameter,
                                    node_id,
                                    source_file,
                                    symbol_table,
                                );
                                Name::Resolved(symbol_id, raw_name_str)
                            } else {
                                // Usage site of a type name (e.g., T in `case some(T)`, or `Int`)
                                // Look up an existing symbol.
                                if raw_name_str == "Self"
                                    && let Some(last_symbol) = self.type_symbol_stack.last()
                                {
                                    let name = Name::SelfType;
                                    symbol_table.add_map(source_file, node_id, last_symbol);
                                    name
                                } else if let Some((symbol_id, _)) = self.lookup(&raw_name_str) {
                                    Name::Resolved(symbol_id, raw_name_str)
                                } else {
                                    if let Ok(mut session) = self.session.lock() {
                                        session.add_diagnostic(Diagnostic::resolve(
                                            source_file.path.clone(),
                                            *node_id,
                                            NameResolverError::UnresolvedName(raw_name_str),
                                        ))
                                    }

                                    return;
                                }
                            }
                        }
                        Name::Resolved(_, _) | Name::_Self(_) | Name::SelfType => name, // Already resolved, no change needed to the name itself.
                    };

                    self.resolve_nodes(&conformances, source_file, symbol_table);

                    // Update the existing TypeRepr node with the resolved name.
                    // The node type remains TypeRepr.
                    source_file.nodes.insert(
                        *node_id,
                        TypeRepr {
                            name: resolved_name_for_node,
                            generics: generics.clone(), // Keep original generics ExprIDs
                            conformances: conformances.clone(),
                            introduces_type,
                        },
                    );

                    // Recursively resolve any type arguments within this TypeRepr.
                    self.resolve_nodes(&generics, source_file, symbol_table);
                }
                FuncTypeRepr(args, ret, _) => {
                    self.resolve_nodes(&args, source_file, symbol_table);
                    self.resolve_nodes(&[ret], source_file, symbol_table);
                }
                TupleTypeRepr(types, _) => {
                    self.resolve_nodes(&types, source_file, symbol_table);
                }
                EnumDecl {
                    name,
                    generics,
                    conformances,
                    body,
                } => {
                    match name {
                        Name::Raw(name_str) => {
                            let symbol_id = self.declare(
                                name_str.clone(),
                                SymbolKind::Enum,
                                node_id,
                                source_file,
                                symbol_table,
                            );
                            self.type_symbol_stack.push(symbol_id);
                            self.resolve_nodes(&generics, source_file, symbol_table);
                            self.resolve_nodes(&conformances, source_file, symbol_table);
                            self.resolve_nodes(&[body], source_file, symbol_table);
                            source_file.nodes.insert(
                                *node_id,
                                EnumDecl {
                                    name: Name::Resolved(symbol_id, name_str),
                                    generics: generics.clone(),
                                    conformances: conformances.clone(),
                                    body,
                                },
                            );
                        }
                        _ => continue,
                    }

                    self.resolve_nodes(&generics, source_file, symbol_table);
                    self.resolve_nodes(&[body], source_file, symbol_table);
                    self.type_symbol_stack.pop();
                }
                EnumVariant(name, values) => {
                    if let Name::Raw(name_str) = name {
                        self.resolve_nodes(&values, source_file, symbol_table);
                        let Some(type_sym) = self.type_symbol_stack.last() else {
                            continue;
                        };
                        let sym = self.declare(
                            name_str.clone(),
                            SymbolKind::EnumVariant(SymbolID(type_sym.0)),
                            node_id,
                            source_file,
                            symbol_table,
                        );

                        source_file
                            .nodes
                            .insert(*node_id, EnumVariant(Name::Resolved(sym, name_str), values));
                    }
                }
                Match(scrutinee, arms) => {
                    // Resolve the scrutinee expression
                    self.resolve_nodes(&[scrutinee], source_file, symbol_table);
                    // Each arm will manage its own scope for pattern bindings.
                    // The Match expression itself doesn't introduce a new scope for *bindings*
                    // that span across arms or affect expressions outside the match.
                    self.resolve_nodes(&arms, source_file, symbol_table);
                }
                MatchArm(pattern, body) => {
                    self.start_scope(source_file, source_file.span(node_id));
                    self.resolve_nodes(&[pattern], source_file, symbol_table);
                    self.resolve_nodes(&[body], source_file, symbol_table);
                    self.end_scope();
                }
                Pattern(pattern) => {
                    let pattern =
                        self.resolve_pattern(&pattern, source_file, symbol_table, node_id);
                    source_file.nodes.insert(*node_id, Pattern(pattern));
                }
                PatternVariant(_, _, _items) => (),
                FuncSignature {
                    name,
                    params,
                    generics,
                    ret,
                } => self.resolve_func(
                    &Some(name),
                    node_id,
                    &params,
                    &generics,
                    None,
                    &Some(ret),
                    symbol_table,
                    source_file,
                ),
                ProtocolDecl {
                    name,
                    associated_types,
                    conformances,
                    body,
                } => match name {
                    Name::Raw(name_str) => {
                        let symbol_id = self.declare(
                            name_str.clone(),
                            SymbolKind::Protocol,
                            node_id,
                            source_file,
                            symbol_table,
                        );
                        self.type_symbol_stack.push(symbol_id);
                        source_file.nodes.insert(
                            *node_id,
                            ProtocolDecl {
                                name: Name::Resolved(symbol_id, name_str),
                                associated_types: associated_types.clone(),
                                conformances: conformances.clone(),
                                body,
                            },
                        );

                        self.resolve_nodes(&associated_types, source_file, symbol_table);
                        self.resolve_nodes(&conformances, source_file, symbol_table);
                        self.resolve_nodes(&[body], source_file, symbol_table);
                        self.type_symbol_stack.pop();
                    }
                    _ => continue,
                },
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn resolve_func(
        &mut self,
        name: &Option<Name>,
        node_id: &ExprID,
        params: &Vec<ExprID>,
        generics: &[ExprID],
        body: Option<&ExprID>,
        ret: &Option<ExprID>,
        symbol_table: &mut SymbolTable,
        source_file: &mut SourceFile,
    ) {
        if !self.type_symbol_stack.is_empty() && name.is_none() {
            if let Ok(mut lock) = self.session.lock() {
                lock.add_diagnostic(Diagnostic::resolve(
                    source_file.path.clone(),
                    *node_id,
                    NameResolverError::MissingMethodName,
                ));
            }

            return;
        }

        self.func_stack.push((*node_id, self.scopes.len()));
        self.start_scope(source_file, source_file.span(node_id));

        self.resolve_nodes(generics, source_file, symbol_table);

        for param in params {
            let Some(Parameter(Name::Raw(name), ty_id)) = source_file.get(param).cloned() else {
                if let Ok(mut lock) = self.session.lock() {
                    lock.add_diagnostic(Diagnostic::resolve(
                        source_file.path.clone(),
                        *node_id,
                        NameResolverError::Unknown("Params must be variables".to_string()),
                    ));
                }

                continue;
            };

            self.declare(
                name.clone(),
                SymbolKind::Param,
                node_id,
                source_file,
                symbol_table,
            );

            if let Some(ty_id) = ty_id {
                self.resolve_nodes(&[ty_id], source_file, symbol_table);
            }
        }

        let mut to_resolve = params.clone();

        if let Some(body) = body {
            to_resolve.push(*body);
        }

        if let Some(ret) = ret {
            to_resolve.push(*ret);
        }

        self.resolve_nodes(&to_resolve, source_file, symbol_table);
        self.end_scope();
        self.func_stack.pop();
    }

    fn hoist_funcs(
        &mut self,
        node_ids: &[ExprID],
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) {
        for id in node_ids {
            if let Some(Func {
                name: Some(Name::Raw(name)),
                generics,
                params,
                body,
                ret,
                captures,
            }) = source_file.get(id).cloned()
            {
                let symbol_id = self.declare(
                    name.clone(),
                    SymbolKind::FuncDef,
                    id,
                    source_file,
                    symbol_table,
                );

                source_file.nodes.insert(
                    *id,
                    Func {
                        name: Some(Name::Resolved(symbol_id, name)),
                        generics,
                        params,
                        body,
                        ret,
                        captures,
                    },
                );
            }

            if let Some(FuncSignature {
                name: Name::Raw(name),
                generics,
                params,
                ret,
            }) = source_file.get(id).cloned()
            {
                let symbol_id = self.declare(
                    name.clone(),
                    SymbolKind::FuncDef,
                    id,
                    source_file,
                    symbol_table,
                );

                source_file.nodes.insert(
                    *id,
                    FuncSignature {
                        name: Name::Resolved(symbol_id, name),
                        generics,
                        params,
                        ret,
                    },
                );
            }
        }
    }

    fn hoise_structs(
        &mut self,
        node_ids: &[ExprID],
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) {
        for id in node_ids {
            let Some(Struct {
                name: Name::Raw(name_str),
                generics,
                conformances,
                body,
            }) = source_file.get(id).cloned()
            else {
                continue;
            };

            if let Some((symbol_id, _)) = self.lookup(&name_str)
                && let Some(info) = symbol_table.get(&symbol_id)
                && let Some(this_info) = source_file.meta.get(id)
                && let Some(existing_info) = source_file.meta.get(&info.expr_id)
                && this_info != existing_info
                && let Ok(session) = &mut self.session.lock()
            {
                session.add_diagnostic(Diagnostic::resolve(
                    source_file.path.clone(),
                    *id,
                    NameResolverError::Redeclaration(name_str.clone(), info.clone()),
                ));
            }

            let struct_symbol = self.declare(
                name_str.clone(),
                SymbolKind::Struct,
                id,
                source_file,
                symbol_table,
            );

            symbol_table.initialize_type_table(struct_symbol);

            self.resolve_nodes(&generics, source_file, symbol_table);
            self.resolve_nodes(&conformances, source_file, symbol_table);

            source_file.nodes.insert(
                *id,
                Struct {
                    name: Name::Resolved(struct_symbol, name_str),
                    generics,
                    conformances,
                    body,
                },
            );

            // Hoist properties
            let Some(Block(ids)) = source_file.get(&body) else {
                log::error!("Didn't get struct body");
                return;
            };

            self.type_symbol_stack.push(struct_symbol);

            // Get properties for the struct so we can synthesize stuff before
            // type checking
            for id in ids {
                let Some(Property {
                    name: Name::Raw(name_str),
                    type_repr: ty,
                    default_value: val,
                }) = source_file.get(id)
                else {
                    continue;
                };

                symbol_table.add_property(struct_symbol, name_str.clone(), *ty, *val);
            }
            self.hoist_enum_members(&body, source_file, symbol_table);
            self.type_symbol_stack.pop();
        }
    }

    fn hoist_enums(
        &mut self,
        node_ids: &[ExprID],
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) {
        for id in node_ids {
            let Some(EnumDecl {
                name: Name::Raw(name_str),
                generics,
                conformances,
                body,
            }) = source_file.get(id).cloned()
            else {
                continue;
            };

            // Declare the enum type
            let enum_symbol = self.declare(
                name_str.clone(),
                SymbolKind::Enum,
                id,
                source_file,
                symbol_table,
            );

            self.resolve_nodes(&generics, source_file, symbol_table);
            self.resolve_nodes(&conformances, source_file, symbol_table);

            source_file.nodes.insert(
                *id,
                EnumDecl {
                    name: Name::Resolved(enum_symbol, name_str),
                    generics,
                    conformances,
                    body,
                },
            );

            // Hoist variants
            self.type_symbol_stack.push(enum_symbol);
            self.hoist_enum_members(&body, source_file, symbol_table);
            self.type_symbol_stack.pop();
        }
    }

    fn resolve_pattern(
        &mut self,
        pattern: &Pattern,
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
        node_id: &ExprID,
    ) -> Pattern {
        match pattern {
            Pattern::Bind(Name::Raw(name_str)) => {
                let symbol = self.declare(
                    name_str.clone(),
                    SymbolKind::PatternBind,
                    node_id,
                    source_file,
                    symbol_table,
                );
                Pattern::Bind(Name::Resolved(symbol, name_str.to_string()))
            }
            Pattern::Variant {
                enum_name,
                variant_name,
                fields,
            } => {
                let enum_name = if let Some(Name::Raw(enum_name)) = enum_name
                    && let Some((symbol, _)) = self.lookup(enum_name)
                {
                    Some(Name::Resolved(symbol, enum_name.to_string()))
                } else {
                    None
                };

                self.resolve_nodes(fields, source_file, symbol_table);
                Pattern::Variant {
                    enum_name,
                    variant_name: variant_name.clone(),
                    fields: fields.to_vec(),
                }
            }
            _ => pattern.clone(),
        }
    }

    pub fn resolve_builtin(&self, name: &Name, symbol_table: &mut SymbolTable) -> Option<SymbolID> {
        match name {
            Name::Raw(name_str) => symbol_table.lookup(name_str),
            _ => None,
        }
    }

    fn hoist_protocols(
        &mut self,
        items: &[ExprID],
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) {
        for id in items {
            let Some(Expr::ProtocolDecl {
                name: Name::Raw(name),
                associated_types,
                conformances,
                body,
            }) = source_file.get(id).cloned()
            else {
                continue;
            };

            let symbol_id = self.declare(
                name.clone(),
                SymbolKind::Protocol,
                id,
                source_file,
                symbol_table,
            );

            self.start_scope(source_file, source_file.span(id));
            self.type_symbol_stack.push(symbol_id);
            self.resolve_nodes(&associated_types, source_file, symbol_table);
            self.resolve_nodes(&conformances, source_file, symbol_table);
            self.resolve_nodes(&[body], source_file, symbol_table);
            self.type_symbol_stack.pop();
            self.end_scope();

            source_file.nodes.insert(
                *id,
                Expr::ProtocolDecl {
                    name: Name::Resolved(symbol_id, name),
                    associated_types,
                    body,
                    conformances,
                },
            );
        }
    }

    // New helper method to hoist enum variants
    fn hoist_enum_members(
        &mut self,
        body_expr_id: &ExprID,
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) {
        let Some(Block(items)) = source_file.get(body_expr_id).cloned() else {
            return;
        };

        for variant_id in &items {
            let Some(variant_expr) = source_file.get(variant_id).cloned() else {
                continue;
            };

            if let EnumVariant(Name::Raw(variant_name), field_types) = variant_expr {
                self.resolve_nodes(&field_types, source_file, symbol_table);

                // Update the AST
                source_file.nodes.insert(
                    *variant_id,
                    EnumVariant(Name::Raw(variant_name), field_types),
                );
            }
        }

        self.resolve_nodes(&items, source_file, symbol_table);
    }

    // Helper method to get enum symbol from variant symbol
    pub fn get_enum_for_variant(
        &self,
        variant_symbol: SymbolID,
        symbol_table: &mut SymbolTable,
    ) -> Option<SymbolID> {
        if let Some(symbol_info) = symbol_table.get(&variant_symbol) {
            match &symbol_info.kind {
                SymbolKind::EnumVariant(enum_symbol) => Some(*enum_symbol),
                _ => None,
            }
        } else {
            None
        }
    }

    fn declare(
        &mut self,
        name: String,
        kind: SymbolKind,
        expr_id: &ExprID,
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) -> SymbolID {
        let Some(meta) = source_file.meta.get(expr_id) else {
            return SymbolID(0);
        };

        let definition = Definition {
            path: source_file.path.clone(),
            line: meta.start.line,
            col: meta.start.col,
            sym: None,
        };

        let symbol_id = symbol_table.add(&name, kind.clone(), *expr_id, Some(definition));

        log::info!("Replacing {kind:?} {name} with {symbol_id:?}");

        if let Some(scope_id) = self.scope_tree_ids.last() {
            source_file
                .scope_tree
                .add_symbol_to_scope(*scope_id, symbol_id);
        }

        let Some(scope) = self.scopes.last_mut() else {
            return SymbolID(0);
        };
        scope.insert(name, symbol_id);
        symbol_table.add_map(source_file, expr_id, &symbol_id);
        symbol_id
    }

    fn lookup(&self, name: &str) -> Option<(SymbolID, usize /* depth */)> {
        for (i, scope) in self.scopes.iter().rev().enumerate() {
            if let Some(symbol_id) = scope.get(name) {
                // The depth of the scope where the variable was found
                let found_depth = self.scopes.len() - 1 - i;
                return Some((*symbol_id, found_depth));
            }
        }

        None
    }

    fn start_scope(&mut self, source_file: &mut SourceFile, span: Span) {
        log::trace!("scope started: {:?}", self.scopes);

        self.scope_tree_ids.push(
            source_file
                .scope_tree
                .new_scope(self.scope_tree_ids.last().copied(), span),
        );
        self.scopes.push(Default::default());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
        self.scope_tree_ids.pop();
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, path::PathBuf};

    use super::*;
    use crate::{compiling::driver::Driver, diagnostic::DiagnosticKind, expr::Expr};

    fn resolve(code: &'static str) -> SourceFile<NameResolved> {
        let mut driver = Driver::with_str(code);
        driver.resolved_source_file(&PathBuf::from("-")).unwrap()
    }

    fn resolve_with_session(
        code: &'static str,
    ) -> (SourceFile<NameResolved>, SharedCompilationSession) {
        let mut driver = Driver::with_str(code);
        (
            driver.resolved_source_file(&PathBuf::from("-")).unwrap(),
            driver.session,
        )
    }

    pub fn resolve_with_symbols(code: &'static str) -> (SourceFile<NameResolved>, SymbolTable) {
        let mut driver = Driver::with_str(code);
        let file = driver.units[0]
            .clone()
            .parse(false)
            .resolved(&mut driver.symbol_table)
            .source_file(&PathBuf::from("-"))
            .unwrap()
            .clone();
        (file, driver.symbol_table)
    }

    #[test]
    fn resolves_literal_int_unchanged() {
        let tree = resolve("123");
        let root = tree.roots()[0].unwrap();
        assert_eq!(root, &LiteralInt("123".into()));
    }

    #[test]
    fn resolves_literal_float_unchanged() {
        let tree = resolve("3.14");
        let root = tree.roots()[0].unwrap();
        assert_eq!(root, &LiteralFloat("3.14".into()));
    }

    #[test]
    fn resolved_builtin() {
        let tree = resolve("Int");
        let root = tree.roots()[0].unwrap();
        assert_eq!(
            root,
            &Variable(Name::Resolved(SymbolID(-1), "Int".into()), None)
        );
    }

    #[test]
    fn resolves_simple_variable_to_depth_0() {
        let tree = resolve("let hello = 1; hello");
        let root = tree.roots()[1].unwrap();
        assert_eq!(
            root,
            &Variable(Name::Resolved(SymbolID::resolved(1), "hello".into()), None)
        );
    }

    #[test]
    fn resolves_shadowed_variable_in_lambda() {
        let tree = resolve("func(x) { x }\n");
        let root = tree.roots()[0].unwrap();

        if let Func { params, body, .. } = root {
            assert_eq!(params.len(), 1);
            let x_param = tree.get(&params[0]).unwrap();
            assert_eq!(
                x_param,
                &Parameter(Name::Resolved(SymbolID::resolved(1), "x".into()), None)
            );

            let Block(exprs) = &tree.get(body).unwrap() else {
                unreachable!("didn't get a block")
            };

            assert_eq!(exprs.len(), 1);
            let x = tree.get(&exprs[0]).unwrap();
            assert_eq!(
                x,
                &Variable(Name::Resolved(SymbolID::resolved(1), "x".into()), None)
            );
        } else {
            unreachable!("expected Func node");
        }
    }

    #[test]
    fn resolves_nested_shadowing_correctly() {
        let tree = resolve("func(x, y) { func(x) { x \n y }\nx }\n");
        let outer = tree.roots()[0].unwrap();
        // outer Func has its body as an inner Func
        let Func {
            body: outer_body_id,
            ..
        } = outer
        else {
            panic!("did not get outer func")
        };
        let Block(outer_body) = &tree.get(outer_body_id).unwrap() else {
            panic!("outer body not a block")
        };

        let inner = tree.get(&outer_body[0]).unwrap();
        let Func {
            body: inner_body_id,
            ..
        } = inner
        else {
            panic!("didn't get inner func")
        };

        let Block(inner_body) = &tree.get(inner_body_id).unwrap() else {
            panic!("outer body not a block")
        };

        let inner_x = tree.get(&inner_body[0]).unwrap();
        assert_eq!(
            inner_x,
            &Variable(Name::Resolved(SymbolID::resolved(3), "x".into()), None)
        );

        let inner_y = tree.get(&inner_body[1]).unwrap();
        assert_eq!(
            inner_y,
            &Variable(Name::Resolved(SymbolID::resolved(2), "y".into()), None)
        );

        let outer_x = tree.get(&outer_body[1]).unwrap();
        assert_eq!(
            outer_x,
            &Variable(Name::Resolved(SymbolID::resolved(1), "x".into()), None)
        );
    }

    #[test]
    fn resolves_inside_array_literals() {
        let resolved = resolve(
            "
            let a = 1; let b = 2; let c = 3;
            [a, b, c]
            ",
        );

        let Expr::LiteralArray(ids) = resolved.get(&resolved.root_ids()[3]).unwrap() else {
            panic!("did not get literal array");
        };

        assert_eq!(
            resolved.get(&ids[0]).unwrap(),
            &Expr::Variable(Name::Resolved(SymbolID::resolved(1), "a".into()), None)
        );
    }

    #[test]
    fn resolves_let_definitions() {
        let (_, symbols) = resolve_with_symbols(
            "
        let x = 123
        let y = 345
        x
        y
        ",
        );

        let symbol_id = symbols.lookup("y").unwrap();
        let info = symbols.get(&symbol_id).unwrap();
        assert_eq!(
            info.definition.as_ref().unwrap(),
            &Definition {
                path: "-".into(),
                line: 2,
                col: 11,
                sym: None
            }
        )
    }

    #[test]
    fn resolves_let_expr() {
        let tree = resolve(
            "
        let x = 123
        let y = 345
        x
        y
        ",
        );

        let Expr::Assignment(let_expr, int) = tree.get(&tree.root_ids()[0]).unwrap() else {
            panic!("didnt get assignment")
        };

        assert_eq!(
            *tree.get(let_expr).unwrap(),
            Let(Name::Resolved(SymbolID::resolved(1), "x".into()), None)
        );

        assert_eq!(*tree.get(int).unwrap(), LiteralInt("123".into()));

        assert_eq!(
            *tree.get(&tree.root_ids()[2]).unwrap(),
            Expr::Variable(Name::Resolved(SymbolID::resolved(1), "x".into()), None)
        );
        assert_eq!(
            *tree.get(&tree.root_ids()[3]).unwrap(),
            Variable(Name::Resolved(SymbolID::resolved(2), "y".into()), None)
        );
    }

    #[test]
    fn resolves_let_rhs() {
        let tree = resolve(
            "
        let x = Optional.none
        ",
        );

        let Expr::Assignment(_, rhs) = tree.get(&tree.root_ids()[0]).unwrap() else {
            panic!("didnt get assignment")
        };

        let Expr::Member(Some(receiver_id), member_name) = tree.get(rhs).unwrap() else {
            panic!("didn't get member");
        };

        assert_eq!("none", member_name);

        assert_eq!(
            *tree.get(receiver_id).unwrap(),
            Variable(Name::Resolved(SymbolID::OPTIONAL, "Optional".into()), None)
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        let (tree, session) = resolve_with_session("{ let x = 123 }; x");

        let session = session.lock().unwrap();
        let diagnostics = session.diagnostics_for(&tree.path).unwrap();
        assert!(!diagnostics.is_empty());
        let Diagnostic {
            path: _,
            kind: DiagnosticKind::Resolve(_, NameResolverError::UnresolvedName(name)),
        } = diagnostics.iter().find(|_| true).unwrap().clone()
        else {
            panic!("didn't get diagnostic");
        };

        assert_eq!("x", name);
    }

    #[test]
    fn resolves_enum_variant() {
        let resolved = resolve(
            "
        enum Fizz {
            case foo, bar
        }

        Fizz.foo
        ",
        );

        let Expr::EnumDecl { name, body, .. } = resolved.roots()[0].unwrap() else {
            panic!("Didn't get enum decl");
        };

        assert_eq!(name, &Name::Resolved(SymbolID::resolved(1), "Fizz".into()));
        let Expr::Block(ids) = resolved.get(body).unwrap() else {
            panic!("did not get ids");
        };

        assert_eq!(
            *resolved.get(&ids[0]).unwrap(),
            EnumVariant(Name::Resolved(SymbolID::resolved(2), "foo".into()), vec![])
        );
        assert_eq!(
            *resolved.get(&ids[1]).unwrap(),
            EnumVariant(Name::Resolved(SymbolID::resolved(3), "bar".into()), vec![])
        );

        let Expr::Member(receiver, member_name) = resolved.roots()[1].unwrap() else {
            panic!("did not get member");
        };

        assert_eq!(member_name, "foo");

        assert_eq!(
            resolved.get(&receiver.unwrap()).unwrap(),
            &Variable(Name::Resolved(SymbolID::resolved(1), "Fizz".into()), None)
        );
    }

    #[test]
    fn resolves_enum_variant_with_args() {
        let resolved = resolve(
            "
        enum Fizz {
            case foo(Int), bar
        }

        Fizz.foo(123)
        ",
        );

        let Expr::EnumDecl { name, body, .. } = resolved.roots()[0].unwrap() else {
            panic!("didn't get enum decl");
        };

        assert_eq!(name, &Name::Resolved(SymbolID::resolved(1), "Fizz".into()));

        let Expr::Block(ids) = resolved.get(body).unwrap() else {
            panic!("didn't get body");
        };

        let EnumVariant(Name::Resolved(_, foo_name), foo_args) = resolved.get(&ids[0]).unwrap()
        else {
            panic!("didn't get foo variant");
        };

        assert_eq!(foo_name, "foo");
        assert_eq!(
            resolved.get(&foo_args[0]).unwrap(),
            &Expr::TypeRepr {
                name: Name::Resolved(SymbolID::INT, "Int".into()),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );

        assert_eq!(
            *resolved.get(&ids[1]).unwrap(),
            EnumVariant(Name::Resolved(SymbolID::resolved(3), "bar".into()), vec![])
        );

        let Call { callee, args, .. } = resolved.roots()[1].unwrap() else {
            panic!("didn't get call");
        };

        let Expr::Member(Some(receiver), member_name) = resolved.get(callee).unwrap() else {
            panic!("didn't get .foo member");
        };

        assert_eq!(member_name, "foo");
        assert_eq!(
            *resolved.get(receiver).unwrap(),
            Expr::Variable(Name::Resolved(SymbolID::resolved(1), "Fizz".into()), None)
        );

        let Expr::CallArg { label: None, value } = resolved.get(&args[0]).unwrap() else {
            panic!("didn't get call arg");
        };

        assert_eq!(resolved.get(value), Some(&Expr::LiteralInt("123".into())));
    }

    #[test]
    fn resolves_enum_method() {
        let resolved = resolve(
            "
        enum Fizz {
            func sup() {
                self
            }
        }
        ",
        );

        resolved.find_expr_id(
            |expr| matches!(expr, Variable(Name::_Self(sym), None) if sym == &SymbolID::resolved(1)),
        ).unwrap();
    }

    #[test]
    fn ensures_methods_have_names() {
        let (_, session) = resolve_with_session(
            "
        enum Fizz {
            func() {
                self
            }
        }
        ",
        );

        assert!(
            !session
                .lock()
                .unwrap()
                .diagnostics_for(&PathBuf::from("-"))
                .unwrap()
                .is_empty()
        )
    }

    #[test]
    fn resolves_captures() {
        let (resolved, symbol_table) = resolve_with_symbols(
            "
        let count = 0
        func counter() {
            count
            count
        }
        ",
        );

        let Assignment(lhs, rhs) = resolved.roots()[0].unwrap() else {
            panic!("didn't get assignment: {:?}", resolved.roots()[0].unwrap());
        };
        assert_eq!(*resolved.get(rhs).unwrap(), Expr::LiteralInt("0".into()));
        assert_eq!(
            *resolved.get(lhs).unwrap(),
            Let(Name::Resolved(SymbolID::resolved(2), "count".into()), None)
        );

        assert!(
            symbol_table
                .get(&SymbolID::resolved(2))
                .unwrap()
                .is_captured
        );

        let Func {
            name: Some(name),
            ret: None,
            captures,
            ..
        } = resolved.get(&resolved.root_ids()[1]).unwrap()
        else {
            panic!(
                "didn't get resolved: {:?}",
                resolved.get(&resolved.root_ids()[1]).unwrap()
            );
        };

        assert_eq!(
            name,
            &Name::Resolved(SymbolID::resolved(1), "counter".into())
        );
        assert_eq!(captures, &vec![SymbolID::resolved(2)]);
    }

    #[test]
    fn doesnt_mark_builtins_as_captured() {
        let resolved = resolve(
            "
        func fizz() {
            __alloc<Int>(123)
        }
        ",
        );

        let Func { captures, .. } = resolved.roots()[0].unwrap() else {
            panic!("no func");
        };

        assert!(captures.is_empty());
    }

    #[test]
    fn resolves_array_builtin() {
        let resolved = resolve("func c() -> Array<Int> {}");

        let Expr::Func { ret, .. } = resolved.roots()[0].unwrap() else {
            panic!("didn't get a func");
        };

        let TypeRepr {
            name: Name::Resolved(SymbolID::ARRAY, _),
            generics,
            introduces_type: false,
            ..
        } = resolved.get(&ret.unwrap()).unwrap()
        else {
            panic!(
                "didn't get array type repr: {:?}",
                resolved.get(&ret.unwrap()).unwrap()
            );
        };

        assert_eq!(
            *resolved.get(&generics[0]).unwrap(),
            TypeRepr {
                name: Name::Resolved(SymbolID(-1), "Int".into()),
                conformances: vec![],
                generics: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn resolves_struct() {
        let resolved = resolve("struct Person {}\nPerson()");
        let Struct {
            name: Name::Resolved(sym, person_str),
            body,
            ..
        } = resolved.roots()[0].unwrap()
        else {
            panic!("didn't get struct");
        };

        assert_eq!(SymbolID::resolved(1), *sym);
        assert_eq!(*person_str, "Person".to_string());

        let Expr::Call { callee, .. } = resolved.get(&resolved.root_ids()[1]).unwrap() else {
            panic!("didn't get call: {:?}", resolved.get(body));
        };
        assert_eq!(
            *resolved.get(callee).unwrap(),
            Expr::Variable(Name::Resolved(SymbolID::resolved(1), "Person".into()), None)
        )
    }

    #[test]
    fn resolves_properties() {
        let resolved = resolve(
            "
        struct Person {
            let age: Int
        }
        ",
        );
        let Struct {
            name: Name::Resolved(sym, person_str),
            body,
            ..
        } = resolved.roots()[0].unwrap()
        else {
            panic!("didn't get struct");
        };

        assert_eq!(SymbolID::resolved(1), *sym);
        assert_eq!(*person_str, "Person".to_string());

        let Expr::Block(body) = resolved.get(body).unwrap() else {
            panic!("didn't get block");
        };

        let Expr::Property {
            name,
            type_repr,
            default_value,
        } = resolved.get(&body[0]).unwrap()
        else {
            panic!("didn't get property: {:?}", resolved.get(&body[0]));
        };

        assert_eq!(*name, Name::Resolved(SymbolID::resolved(2), "age".into()));
        assert!(default_value.is_none());

        assert_eq!(
            *resolved.get(&type_repr.unwrap()).unwrap(),
            Expr::TypeRepr {
                name: Name::Resolved(SymbolID(-1), "Int".into()),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }

    #[test]
    fn resolves_initializers() {
        let resolved = resolve(
            "
        struct Person {
            let age: Int

            init(age: Int) {
                self.age = age
            }
        }
        ",
        );

        let Expr::Struct {
            name: Name::Resolved(sym, person_str),
            body,
            ..
        } = resolved.roots()[0].unwrap()
        else {
            panic!("didn't get struct");
        };

        assert_eq!(SymbolID::resolved(1), *sym);
        assert_eq!(*person_str, "Person".to_string());

        let Expr::Block(body) = resolved.get(body).unwrap() else {
            panic!("didn't get block");
        };

        let Expr::Property {
            name,
            type_repr,
            default_value,
        } = resolved.get(&body[0]).unwrap()
        else {
            panic!("didn't get property: {:?}", resolved.get(&body[0]));
        };

        assert_eq!(*name, Name::Resolved(SymbolID::resolved(2), "age".into()));
        assert!(default_value.is_none());

        assert_eq!(
            *resolved.get(&type_repr.unwrap()).unwrap(),
            Expr::TypeRepr {
                name: Name::Resolved(SymbolID(-1), "Int".into()),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );

        let Expr::Init(_, _) = resolved.get(&body[1]).unwrap() else {
            panic!("didn't get init");
        };
    }

    #[test]
    fn resolves_extend() {
        let resolved = resolve(
            "
        struct Person {}
        extend Person: Printable {}
        ",
        );

        let Struct {
            name: Name::Resolved(person_symbol, _),
            ..
        } = resolved.roots()[0].unwrap()
        else {
            panic!("didn't get struct");
        };

        let Extend {
            name: Name::Resolved(extend_symbol, _),
            ..
        } = resolved.roots()[1].unwrap()
        else {
            panic!("didn't get struct");
        };

        assert_eq!(person_symbol, extend_symbol);
    }

    #[test]
    fn doesnt_let_structs_get_double_declared() {
        let (_, session) = resolve_with_session(
            "
        struct Person {}

        struct Person {}
        ",
        );

        let ses = session.lock().unwrap();
        let diagnostics = ses
            .diagnostics_for(&PathBuf::from("-"))
            .cloned()
            .unwrap_or(HashSet::new());
        assert_eq!(diagnostics.len(), 1);

        let Diagnostic {
            kind:
                DiagnosticKind::Resolve(
                    _,
                    NameResolverError::Redeclaration(
                        _,
                        SymbolInfo {
                            name: _,
                            kind: SymbolKind::Struct,
                            expr_id: _,
                            is_captured: false,
                            definition: Some(Definition { .. }),
                        },
                    ),
                ),
            ..
        } = diagnostics.iter().find(|_| true).unwrap()
        else {
            panic!(
                "didn't get diagnostic: {:?}",
                diagnostics.iter().find(|_| true).unwrap()
            );
        };
    }
}

// TODO:

// named recursive binds
// parameter ordering
// captured vs. shadowed vs. free
// arbitrary nesting depth
//   non‐statement AST nodes (tuples, blocks)
