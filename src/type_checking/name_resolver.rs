use std::collections::BTreeMap;
use std::path::PathBuf;

use crate::Definition;
use crate::ExprMetaStorage;
use crate::NameResolved;
use crate::SymbolID;
use crate::SymbolInfo;
use crate::SymbolKind;
use crate::SymbolTable;
use crate::compiling::compilation_session::SharedCompilationSession;
use crate::diagnostic::Diagnostic;
use crate::name::Name;
use crate::parsed_expr::Expr;
use crate::parsed_expr::IncompleteExpr;
use crate::parsed_expr::ParsedExpr;
use crate::parsed_expr::Pattern;
use crate::parser::ExprID;
use crate::scope_tree::ScopeId;
use crate::scope_tree::ScopeTree;
use crate::source_file::SourceFile;
use crate::span::Span;

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum NameResolverError {
    InvalidSelf,
    InvalidSpan,
    MissingMethodName,
    Unknown(String),
    UnresolvedName(String),
    Redeclaration(String, SymbolInfo),
}

// Just to make sure we're always ending scopes we started
struct ScopeTok;

impl NameResolverError {
    pub fn message(&self) -> String {
        match self {
            Self::InvalidSelf => "`self` can't be used outside type".to_string(),
            Self::InvalidSpan => "Span not found".to_string(),
            Self::UnresolvedName(string) => format!("Unknown identifier: {string}"),
            Self::MissingMethodName => "Missing method name".to_string(),
            Self::Unknown(string) => string.to_string(),
            Self::Redeclaration(name, _info) => format!("{name} already defined"),
        }
    }
}

pub struct NameResolver {
    pub scopes: Vec<BTreeMap<String, SymbolID>>,

    // For resolving `self` references
    type_symbol_stack: Vec<SymbolID>,

    // For resolving captures
    func_stack: Vec<(String /* func expr id */, usize /* scope depth */)>,

    scope_tree_ids: Vec<ScopeId>,
    scope_tree: ScopeTree,

    session: SharedCompilationSession,
    path: PathBuf,
}

impl NameResolver {
    pub fn new(
        initial_scope: BTreeMap<String, SymbolID>,
        session: SharedCompilationSession,
        path: PathBuf,
    ) -> Self {
        NameResolver {
            scopes: vec![initial_scope],
            type_symbol_stack: vec![],
            func_stack: vec![],
            scope_tree_ids: vec![],
            scope_tree: Default::default(),
            session,
            path,
        }
    }

    pub fn resolve(
        &mut self,
        mut source_file: SourceFile,
        symbol_table: &mut SymbolTable,
    ) -> SourceFile<NameResolved> {
        // Create the root scope for the file
        #[allow(clippy::unwrap_used)]
        if !source_file.roots().is_empty()
            && let Some(first_root) = &source_file
                .meta
                .borrow()
                .get(&source_file.roots().first().unwrap().id)
            && let Some(last_root) = &source_file
                .meta
                .borrow()
                .get(&source_file.roots().last().unwrap().id)
        {
            let root_scope_id = self.scope_tree.new_scope(
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

        let meta = source_file.meta.clone();
        self.resolve_nodes(source_file.roots_mut(), &meta.borrow(), symbol_table);
        source_file.to_resolved()
    }

    #[tracing::instrument(skip(self, symbol_table))]
    fn resolve_nodes(
        &mut self,
        exprs: &mut [ParsedExpr],
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
    ) -> Result<Vec<ParsedExpr>, NameResolverError> {
        self.hoist_protocols(exprs, meta, symbol_table);
        self.hoist_enums(exprs, meta, symbol_table);
        self.hoist_funcs(exprs, meta, symbol_table);
        self.hoise_structs(exprs, meta, symbol_table);

        let mut result = vec![];

        for expr in exprs {
            tracing::trace!("Resolving: {expr:?}");
            result.push(self.resolve_node(expr, meta, symbol_table)?);
        }

        Ok(result)
    }

    fn resolve_node(
        &mut self,
        parsed_expr: &mut ParsedExpr,
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
    ) -> Result<ParsedExpr, NameResolverError> {
        let expr = &mut parsed_expr.expr;

        match expr {
            Expr::LiteralArray(items) => {
                *items = self.resolve_nodes(items, meta, symbol_table)?;
            }
            Expr::Incomplete(incomplete) => match &mut *incomplete {
                IncompleteExpr::Member(receiver) => {
                    if let Some(box receiver_brw) = receiver {
                        *receiver_brw = self.resolve_node(receiver_brw, meta, symbol_table)?;
                    }
                }
                IncompleteExpr::Func {
                    name,
                    params,
                    generics,
                    ret,
                    body,
                } => {
                    // self.resolve_func(&name, expr, symbol_table);
                }
            },
            Expr::Struct { .. } => {
                // Handled by hoisting
            }
            Expr::Extend {
                name,
                generics,
                body,
                conformances,
            } => match name {
                Name::Raw(name_str) => {
                    let Some(symbol_id) = self.lookup(&name_str) else {
                        tracing::error!("Did not find symbol for {name_str}");
                        if let Ok(mut session) = self.session.lock() {
                            session.add_diagnostic(Diagnostic::resolve(
                                self.path.clone(),
                                parsed_expr.id,
                                NameResolverError::UnresolvedName(name_str.to_string()),
                            ))
                        }

                        return Ok(parsed_expr.clone());
                    };

                    tracing::trace!("Resolving extension {name_str} {symbol_id:?}");

                    let symbol_id = symbol_id.0;
                    self.type_symbol_stack.push(symbol_id);

                    *name = Name::Resolved(symbol_id, name_str.to_string());
                    *generics = self.resolve_nodes(generics, meta, symbol_table)?;
                    *conformances = self.resolve_nodes(conformances, meta, symbol_table)?;
                    *body = self.resolve_node(body, meta, symbol_table)?.into();

                    self.type_symbol_stack.pop();
                }
                _ => return Ok(parsed_expr.clone()),
            },
            Expr::Break => (),
            Expr::Init(_, func_id) => {
                let Some(symbol_id) = self.type_symbol_stack.last().cloned() else {
                    tracing::error!("no type found for initializer");
                    return Err(NameResolverError::InvalidSelf);
                };

                symbol_table.add_initializer(symbol_id, parsed_expr.id);
                *func_id = Box::new(self.resolve_node(func_id, meta, symbol_table)?);
            }
            Expr::Property {
                type_repr,
                default_value,
                name,
            } => {
                if let Some(type_repr) = type_repr {
                    *type_repr = Box::new(self.resolve_node(type_repr, meta, symbol_table)?);
                }
                if let Some(default_value) = default_value {
                    *default_value =
                        Box::new(self.resolve_node(default_value, meta, symbol_table)?);
                }

                if let Name::Raw(name_str) = name {
                    let symbol_id = self.declare(
                        name_str.clone(),
                        SymbolKind::Property,
                        parsed_expr.id,
                        meta,
                        symbol_table,
                    );

                    *name = Name::Resolved(symbol_id, name_str.to_string());
                }
            }
            Expr::Return(rhs) => {
                if let Some(rhs) = rhs {
                    *rhs = Box::new(self.resolve_node(rhs, meta, symbol_table)?);
                }
            }
            Expr::If(condi, conseq, alt) => {
                *condi = Box::new(self.resolve_node(condi, meta, symbol_table)?);
                *conseq = Box::new(self.resolve_node(conseq, meta, symbol_table)?);

                if let Some(alt) = alt {
                    *alt = Box::new(self.resolve_node(alt, meta, symbol_table)?);
                }
            }
            Expr::Loop(cond, body) => {
                if let Some(cond) = cond {
                    *cond = Box::new(self.resolve_node(cond, meta, symbol_table)?);
                }

                *body = Box::new(self.resolve_node(body, meta, symbol_table)?);
            }
            Expr::Member(receiver, _member) => {
                if let Some(receiver) = receiver {
                    *receiver = Box::new(self.resolve_node(receiver, meta, symbol_table)?);
                }
            }
            Expr::Let(name, rhs) => {
                if let Name::Raw(name_str) = name {
                    let symbol_id = self.declare(
                        name_str.clone(),
                        SymbolKind::Local,
                        parsed_expr.id,
                        meta,
                        symbol_table,
                    );

                    *name = Name::Resolved(symbol_id, name_str.to_string());
                }

                if let Some(rhs) = rhs {
                    *rhs = Box::new(self.resolve_node(rhs, meta, symbol_table)?);
                }
            }
            Expr::Call {
                callee,
                type_args,
                args,
            } => {
                *callee = Box::new(self.resolve_node(callee, meta, symbol_table)?);
                *type_args = self.resolve_nodes(type_args, meta, symbol_table)?;
                *args = self.resolve_nodes(args, meta, symbol_table)?;
            }
            Expr::Assignment(lhs, rhs) => {
                *lhs = Box::new(self.resolve_node(lhs, meta, symbol_table)?);
                *rhs = Box::new(self.resolve_node(rhs, meta, symbol_table)?);
            }
            Expr::Unary(_, rhs) => {
                *rhs = Box::new(self.resolve_node(rhs, meta, symbol_table)?);
            }
            Expr::Binary(lhs, _, rhs) => {
                *lhs = Box::new(self.resolve_node(lhs, meta, symbol_table)?);
                *rhs = Box::new(self.resolve_node(rhs, meta, symbol_table)?);
            }
            Expr::Tuple(items) => {
                *items = self.resolve_nodes(items, meta, symbol_table)?;
            }
            Expr::Block(items) => {
                let tok = self.start_scope(
                    meta.span(&parsed_expr.id)
                        .ok_or(NameResolverError::InvalidSpan)?,
                );
                self.hoist_funcs(items, meta, symbol_table);
                *items = self.resolve_nodes(items, meta, symbol_table)?;
                self.end_scope(tok);
            }
            Expr::Func { .. } => {
                self.resolve_func(expr, &parsed_expr.id, meta, symbol_table);
            }
            Expr::CallArg { value, .. } => {
                *value = Box::new(self.resolve_node(value, meta, symbol_table)?);
            }
            Expr::Parameter(name, ty_repr) => {
                if let Name::Raw(name_str) = &name {
                    let symbol_id = self.declare(
                        name_str.to_string(),
                        SymbolKind::Param,
                        parsed_expr.id,
                        meta,
                        symbol_table,
                    );

                    *name = Name::Resolved(symbol_id, name_str.to_string());
                }

                if let Some(ty_repr) = ty_repr {
                    *ty_repr = Box::new(self.resolve_node(ty_repr, meta, symbol_table)?);
                }
            }
            Expr::Variable(name) => match name {
                Name::Raw(name_str) => {
                    *name = if name_str == "self" {
                        if let Some(last_symbol) = self.type_symbol_stack.last() {
                            symbol_table.add_map(
                                meta.span(&parsed_expr.id)
                                    .ok_or(NameResolverError::InvalidSpan)?,
                                last_symbol,
                            );
                            Name::_Self(*last_symbol)
                        } else {
                            return Err(NameResolverError::InvalidSelf);
                        }
                    } else {
                        let Some((symbol_id, depth)) = self.lookup(&name_str) else {
                            return Err(NameResolverError::UnresolvedName(name_str.to_string()));
                        };

                        tracing::info!("Replacing variable {name_str} with {symbol_id:?}");

                        symbol_table.add_map(
                            meta.span(&parsed_expr.id)
                                .ok_or(NameResolverError::InvalidSpan)?,
                            &symbol_id,
                        );

                        // TODO: Resolve captures when we're resolving a func?
                        // Check to see if this is a capture
                        // if let Some((func_name, func_depth)) = self.func_stack.last()
                        //     && &depth < func_depth
                        //     && symbol_id.0 > 0
                        // {
                        //     #[allow(clippy::unwrap_used)]
                        //     if func_name == name_str {
                        //         tracing::trace!("the same: {func_name:?} <> {name_str:?}");
                        //     } else {
                        //         if !captures.contains(&symbol_id) {
                        //             (*captures).push(symbol_id);
                        //         }

                        //         symbol_table.mark_as_captured(&symbol_id);
                        //     }
                        // }

                        Name::Resolved(symbol_id, name_str.to_string())
                    };
                }
                Name::Resolved(_, _) | Name::_Self(_) | Name::SelfType => (),
            },
            Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => {
                let resolved_name_for_node = match name.clone() {
                    Name::Raw(raw_name_str) => {
                        if *introduces_type {
                            // Declaration site of a type parameter (e.g., T in `enum Option<T>`)
                            // Ensure it's declared in the current scope.
                            let symbol_id = self.declare(
                                raw_name_str.clone(),
                                SymbolKind::TypeParameter,
                                parsed_expr.id,
                                meta,
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
                                symbol_table.add_map(
                                    meta.span(&parsed_expr.id)
                                        .ok_or(NameResolverError::InvalidSpan)?,
                                    last_symbol,
                                );
                                name
                            } else if let Some((symbol_id, _)) = self.lookup(&raw_name_str) {
                                Name::Resolved(symbol_id, raw_name_str)
                            } else {
                                return Err(NameResolverError::UnresolvedName(raw_name_str));
                            }
                        }
                    }
                    Name::Resolved(_, _) | Name::_Self(_) | Name::SelfType => name.clone(), // Already resolved, no change needed to the name itself.
                };

                // Update the existing TypeRepr node with the resolved name.
                // The node type remains TypeRepr.
                *name = resolved_name_for_node;
                *generics = self.resolve_nodes(generics, meta, symbol_table)?;
                *conformances = self.resolve_nodes(conformances, meta, symbol_table)?;
            }
            Expr::FuncTypeRepr(args, ret, _) => {
                *args = self.resolve_nodes(args, meta, symbol_table)?;
                *ret = Box::new(self.resolve_node(ret, meta, symbol_table)?);
            }
            Expr::TupleTypeRepr(types, _) => {
                *types = self.resolve_nodes(types, meta, symbol_table)?;
            }
            Expr::EnumDecl {
                name,
                generics,
                conformances,
                body,
            } => {
                if let Name::Raw(name_str) = name {
                    let symbol_id = self.declare(
                        name_str.clone(),
                        SymbolKind::Enum,
                        parsed_expr.id,
                        meta,
                        symbol_table,
                    );
                    self.type_symbol_stack.push(symbol_id);
                    *generics = self.resolve_nodes(generics, meta, symbol_table)?;
                    *conformances = self.resolve_nodes(conformances, meta, symbol_table)?;
                    *body = self.resolve_node(body, meta, symbol_table)?.into();
                    *name = Name::Resolved(symbol_id, name_str.to_string());
                    self.type_symbol_stack.pop();
                }
            }
            Expr::EnumVariant(name, values) => {
                if let Name::Raw(name_str) = name {
                    let Some(type_sym) = self.type_symbol_stack.last() else {
                        return Err(NameResolverError::InvalidSelf);
                    };
                    let sym = self.declare(
                        name_str.clone(),
                        SymbolKind::EnumVariant(SymbolID(type_sym.0)),
                        parsed_expr.id,
                        meta,
                        symbol_table,
                    );

                    *name = Name::Resolved(sym, name_str.to_string());
                    *values = self.resolve_nodes(values, meta, symbol_table)?;
                }
            }
            Expr::Match(scrutinee, arms) => {
                // Resolve the scrutinee expression
                *scrutinee = Box::new(self.resolve_node(scrutinee, meta, symbol_table)?);
                // Each arm will manage its own scope for pattern bindings.
                // The Match expression itself doesn't introduce a new scope for *bindings*
                // that span across arms or affect expressions outside the match.
                *arms = self.resolve_nodes(arms, meta, symbol_table)?;
            }
            Expr::MatchArm(pattern, body) => {
                let tok = self.start_scope(
                    meta.span(&parsed_expr.id)
                        .ok_or(NameResolverError::InvalidSpan)?,
                );
                *pattern = Box::new(self.resolve_node(pattern, meta, symbol_table)?);
                *body = Box::new(self.resolve_node(body, meta, symbol_table)?);
                self.end_scope(tok);
            }
            Expr::ParsedPattern(pattern) => {
                self.resolve_pattern(pattern, meta, symbol_table, &parsed_expr.id)?;
            }
            Expr::PatternVariant(_, _, _items) => (),
            Expr::FuncSignature {
                name,
                params,
                generics,
                ret,
            } => {
                self.resolve_func(expr, &parsed_expr.id, meta, symbol_table);
            }
            Expr::ProtocolDecl {
                name,
                associated_types,
                conformances,
                body,
            } => match name {
                Name::Raw(name_str) => {
                    let symbol_id = self.declare(
                        name_str.clone(),
                        SymbolKind::Protocol,
                        parsed_expr.id,
                        meta,
                        symbol_table,
                    );
                    self.type_symbol_stack.push(symbol_id);
                    *name = Name::Resolved(symbol_id, name_str.to_string());
                    *associated_types = self.resolve_nodes(associated_types, meta, symbol_table)?;
                    *conformances = self.resolve_nodes(conformances, meta, symbol_table)?;
                    *body = self.resolve_node(body, meta, symbol_table)?.into();
                    self.type_symbol_stack.pop();
                }
                _ => return Err(NameResolverError::InvalidSelf),
            },
            _ => (),
        }

        Ok(parsed_expr.clone())
    }

    #[allow(clippy::too_many_arguments)]
    #[tracing::instrument(skip(self, meta, symbol_table))]
    fn resolve_func(
        &mut self,
        expr: &mut Expr,
        expr_id: &ExprID,
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
    ) -> Result<(), NameResolverError> {
        let Expr::Func {
            name,
            generics,
            params,
            body,
            ret,
            ..
        } = expr
        else {
            return Err(NameResolverError::InvalidSelf);
        };

        if !self.type_symbol_stack.is_empty() && name.is_none() {
            return Err(NameResolverError::MissingMethodName);
        }

        let Some(Name::Raw(name_str)) = name else {
            return Err(NameResolverError::InvalidSelf);
        };

        self.func_stack
            .push((name_str.to_string(), self.scopes.len()));
        let tok = self.start_scope(meta.span(expr_id).ok_or(NameResolverError::InvalidSpan)?);

        *generics = self.resolve_nodes(generics, meta, symbol_table)?;
        *params = self.resolve_nodes(params, meta, symbol_table)?;

        *body = Box::new(self.resolve_node(body, meta, symbol_table)?);

        if let Some(ret) = ret {
            *ret = Box::new(self.resolve_node(ret, meta, symbol_table)?);
        }

        self.end_scope(tok);
        self.func_stack.pop();

        Ok(())
    }

    #[tracing::instrument(skip(self, meta, symbol_table))]
    fn hoist_funcs(
        &mut self,
        parsed_exprs: &mut [ParsedExpr],
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
    ) -> Result<(), NameResolverError> {
        for parsed_expr in parsed_exprs {
            if let Expr::Func {
                name: name,
                generics,
                params,
                ret,
                ..
            } = &mut parsed_expr.expr
            {
                if let Some(Name::Raw(name_str)) = name {
                    let symbol_id = self.declare(
                        name_str.to_string(),
                        SymbolKind::FuncDef,
                        parsed_expr.id,
                        meta,
                        symbol_table,
                    );

                    *name = Some(Name::Resolved(symbol_id, name_str.to_string()));
                }

                let tok = self.start_scope(
                    meta.span(&parsed_expr.id)
                        .ok_or(NameResolverError::InvalidSpan)?,
                );

                *generics = self.resolve_nodes(generics, meta, symbol_table)?;
                *params = self.resolve_nodes(params, meta, symbol_table)?;

                if let Some(ret) = ret {
                    *ret = Box::new(self.resolve_node(ret, meta, symbol_table)?);
                }

                self.end_scope(tok);
            }

            if let Expr::FuncSignature {
                name,
                generics,
                params,
                ret,
            } = &mut parsed_expr.expr
            {
                if let Name::Raw(name_str) = name {
                    let symbol_id = self.declare(
                        name_str.to_string(),
                        SymbolKind::FuncDef,
                        parsed_expr.id,
                        meta,
                        symbol_table,
                    );
                    *name = Name::Resolved(symbol_id, name_str.to_string());
                };

                let tok = self.start_scope(
                    meta.span(&parsed_expr.id)
                        .ok_or(NameResolverError::InvalidSpan)?,
                );

                *generics = self.resolve_nodes(generics, meta, symbol_table)?;
                *params = self.resolve_nodes(params, meta, symbol_table)?;
                *ret = Box::new(self.resolve_node(ret, meta, symbol_table)?);

                self.end_scope(tok);
            }
        }

        Ok(())
    }

    #[tracing::instrument(skip(self, meta, symbol_table))]
    fn hoise_structs(
        &mut self,
        parsed_exprs: &mut [ParsedExpr],
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
    ) -> Result<(), NameResolverError> {
        for parsed_expr in parsed_exprs {
            let Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } = &mut parsed_expr.expr
            else {
                continue;
            };

            let Name::Raw(name_str) = name else {
                return Err(NameResolverError::InvalidSelf);
            };

            if let Some((symbol_id, _)) = self.lookup(&name_str)
                && let Some(info) = symbol_table.get(&symbol_id)
                && let Some(this_info) = meta.get(&parsed_expr.id)
                && let Some(existing_info) = meta.get(&info.expr_id)
                && this_info != existing_info
                && let Ok(session) = &mut self.session.lock()
            {
                return Err(NameResolverError::Redeclaration(
                    name_str.clone(),
                    info.clone(),
                ));
            }

            let struct_symbol = self.declare(
                name_str.clone(),
                SymbolKind::Struct,
                parsed_expr.id,
                meta,
                symbol_table,
            );

            *name = Name::Resolved(struct_symbol, name_str.to_string());

            symbol_table.initialize_type_table(struct_symbol);
            let tok = self.start_scope(
                meta.span(&parsed_expr.id)
                    .ok_or(NameResolverError::InvalidSpan)?,
            );
            self.type_symbol_stack.push(struct_symbol);

            *generics = self.resolve_nodes(generics, meta, symbol_table)?;
            *conformances = self.resolve_nodes(conformances, meta, symbol_table)?;

            // Hoist properties
            let Expr::Block(body_parsed_exprs) = &mut body.expr else {
                return Err(NameResolverError::InvalidSelf);
            };

            // Get properties for the struct so we can synthesize stuff before
            // type checking
            for body_expr in body_parsed_exprs {
                if let Expr::Property {
                    name,
                    type_repr: ty,
                    default_value: val,
                } = &mut body_expr.expr
                {
                    let Name::Raw(name_str) = name else {
                        return Err(NameResolverError::InvalidSelf);
                    };

                    symbol_table.add_property(
                        struct_symbol,
                        name_str.clone(),
                        ty.clone(),
                        val.clone(),
                    );
                    let property_symbol = self.declare(
                        name_str.clone(),
                        SymbolKind::Property,
                        body_expr.id,
                        meta,
                        symbol_table,
                    );
                    *name = Name::Resolved(property_symbol, name_str.clone());
                }
                if let Expr::Init(None, func_id) = &mut body_expr.expr {
                    symbol_table.add_initializer(struct_symbol, func_id.id);
                    *func_id = Box::new(self.resolve_node(func_id, meta, symbol_table)?);
                }
            }

            *body = Box::new(self.resolve_node(body, meta, symbol_table)?);

            self.type_symbol_stack.pop();
            self.end_scope(tok);
        }

        Ok(())
    }

    #[tracing::instrument(skip(self, meta, symbol_table))]
    fn hoist_enums(
        &mut self,
        parsed_exprs: &mut [ParsedExpr],
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
    ) -> Result<(), NameResolverError> {
        for parsed_expr in parsed_exprs {
            let Expr::EnumDecl {
                name,
                generics,
                conformances,
                body,
            } = &mut parsed_expr.expr
            else {
                continue;
            };

            let Name::Raw(name_str) = name else {
                return Err(NameResolverError::InvalidSelf);
            };

            // Declare the enum type
            let enum_symbol = self.declare(
                name_str.clone(),
                SymbolKind::Enum,
                parsed_expr.id,
                meta,
                symbol_table,
            );

            let tok = self.start_scope(
                meta.span(&parsed_expr.id)
                    .ok_or(NameResolverError::InvalidSpan)?,
            );
            *generics = self.resolve_nodes(generics, meta, symbol_table)?;
            *conformances = self.resolve_nodes(conformances, meta, symbol_table)?;

            *name = Name::Resolved(enum_symbol, name_str.to_string());

            // Hoist variants
            self.type_symbol_stack.push(enum_symbol);
            self.hoist_enum_members(body, meta, symbol_table);
            self.type_symbol_stack.pop();
            self.end_scope(tok);
        }

        Ok(())
    }

    #[tracing::instrument(skip(self, meta, symbol_table))]
    fn resolve_pattern(
        &mut self,
        pattern: &mut Pattern,
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
        expr_id: &ExprID,
    ) -> Result<(), NameResolverError> {
        *pattern = match pattern {
            Pattern::Bind(Name::Raw(name_str)) => {
                let symbol = self.declare(
                    name_str.clone(),
                    SymbolKind::PatternBind,
                    *expr_id,
                    meta,
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

                *fields = self.resolve_nodes(fields, meta, symbol_table)?;
                Pattern::Variant {
                    enum_name,
                    variant_name: variant_name.clone(),
                    fields: fields.to_vec(),
                }
            }
            _ => pattern.clone(),
        };

        Ok(())
    }

    pub fn resolve_builtin(&self, name: &Name, symbol_table: &mut SymbolTable) -> Option<SymbolID> {
        match name {
            Name::Raw(name_str) => symbol_table.lookup(name_str),
            _ => None,
        }
    }

    #[tracing::instrument(skip(self, meta, symbol_table))]
    fn hoist_protocols(
        &mut self,
        items: &mut [ParsedExpr],
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
    ) -> Result<(), NameResolverError> {
        for parsed_expr in items {
            let Expr::ProtocolDecl {
                name,
                associated_types,
                conformances,
                body,
            } = &mut parsed_expr.expr
            else {
                continue;
            };

            let Name::Raw(name_str) = name else {
                return Ok(());
            };

            let symbol_id = self.declare(
                name_str.clone(),
                SymbolKind::Protocol,
                parsed_expr.id,
                meta,
                symbol_table,
            );

            *name = Name::Resolved(symbol_id, name_str.to_string());

            let Some(span) = meta.span(&parsed_expr.id) else {
                return Err(NameResolverError::InvalidSelf);
            };

            let tok = self.start_scope(span);
            self.type_symbol_stack.push(symbol_id);
            *associated_types = self.resolve_nodes(associated_types, meta, symbol_table)?;
            *conformances = self.resolve_nodes(conformances, meta, symbol_table)?;
            *body = Box::new(self.resolve_node(body, meta, symbol_table)?);
            self.type_symbol_stack.pop();
            self.end_scope(tok);
        }

        Ok(())
    }

    // New helper method to hoist enum variants
    #[tracing::instrument(skip(self, meta, symbol_table))]
    fn hoist_enum_members(
        &mut self,
        body: &mut ParsedExpr,
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
    ) -> Result<(), NameResolverError> {
        let Expr::Block(items) = &mut body.expr else {
            return Ok(());
        };

        for variant_expr in &mut *items {
            let Expr::EnumVariant(Name::Raw(_), field_types) = &mut variant_expr.expr else {
                continue;
            };

            *field_types = self.resolve_nodes(field_types, meta, symbol_table)?;
        }

        *items = self.resolve_nodes(items, meta, symbol_table)?;

        Ok(())
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

    #[tracing::instrument(skip(self, meta, symbol_table))]
    fn declare(
        &mut self,
        name: String,
        kind: SymbolKind,
        expr_id: ExprID,
        meta: &ExprMetaStorage,
        symbol_table: &mut SymbolTable,
    ) -> SymbolID {
        if self.lookup(&name).is_some() {
            tracing::warn!("Already declared name: {name}");
        }

        let Some(expr_meta) = meta.get(&expr_id) else {
            return SymbolID(0);
        };

        let definition = Definition {
            path: meta.path.clone(),
            line: expr_meta.start.line,
            col: expr_meta.start.col,
            sym: None,
        };

        let symbol_id = symbol_table.add(&name, kind.clone(), expr_id, Some(definition));

        tracing::info!("Replacing {kind:?} {name} with {symbol_id:?}");

        if let Some(scope_id) = self.scope_tree_ids.last() {
            self.scope_tree.add_symbol_to_scope(*scope_id, symbol_id);
        }

        let Some(scope) = self.scopes.last_mut() else {
            return SymbolID(0);
        };
        scope.insert(name.clone(), symbol_id);
        if let Some(span) = meta.span(&expr_id) {
            symbol_table.add_map(span, &symbol_id);
        } else {
            tracing::error!("No span for {name}");
        }

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

    #[must_use]
    fn start_scope(&mut self, span: Span) -> ScopeTok {
        self.scope_tree_ids.push(
            self.scope_tree
                .new_scope(self.scope_tree_ids.last().copied(), span),
        );
        self.scopes.push(Default::default());

        ScopeTok
    }

    fn end_scope(&mut self, _tok: ScopeTok) {
        self.scopes.pop();
        self.scope_tree_ids.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        any_expr, compiling::driver::Driver, diagnostic::DiagnosticKind, parsed_expr::Expr,
    };

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
            .resolved(&mut driver.symbol_table, &driver.config)
            .source_file(&PathBuf::from("-"))
            .unwrap()
            .clone();
        (file, driver.symbol_table)
    }

    #[test]
    fn resolves_literal_int_unchanged() {
        let tree = resolve("123");
        assert_eq!(tree.roots()[0], any_expr!(Expr::LiteralInt("123".into())));
    }

    #[test]
    fn resolves_literal_float_unchanged() {
        let tree = resolve("3.14");
        assert_eq!(
            tree.roots()[0],
            any_expr!(Expr::LiteralFloat("3.14".into()))
        );
    }

    #[test]
    fn resolved_builtin() {
        let tree = resolve("Int");
        assert_eq!(
            tree.roots()[0],
            any_expr!(Expr::Variable(Name::Resolved(SymbolID(-1), "Int".into())))
        );
    }

    #[test]
    fn resolves_simple_variable_to_depth_0() {
        let tree = resolve("let hello = 1; hello");
        assert_eq!(
            tree.roots()[0],
            any_expr!(Expr::Variable(Name::Resolved(
                SymbolID::resolved(1),
                "hello".into()
            )))
        );
    }

    #[test]
    fn resolves_shadowed_variable_in_lambda() {
        let tree = resolve("func(x) { x }\n");

        assert_eq!(
            tree.roots()[0],
            any_expr!(Expr::Func {
                name: None,
                generics: vec![],
                params: vec![any_expr!(Expr::Parameter(
                    Name::Resolved(SymbolID::resolved(1), "x".into()),
                    None
                ))],
                body: any_expr!(Expr::Block(vec![any_expr!(Expr::Variable(
                    Name::Resolved(SymbolID::resolved(1), "x".into())
                ))]))
                .into(),
                ret: None,
                captures: vec![]
            })
        );
    }

    #[test]
    fn resolves_nested_shadowing_correctly() {
        let tree = resolve("func(x, y) { func(x) { x \n y }\nx }\n");

        assert_eq!(
            tree.roots()[0],
            any_expr!(Expr::Func {
                name: None,
                generics: vec![],
                params: vec![
                    any_expr!(Expr::Parameter(
                        Name::Resolved(SymbolID::resolved(1), "x".into()),
                        None
                    )),
                    any_expr!(Expr::Parameter(
                        Name::Resolved(SymbolID::resolved(2), "y".into()),
                        None
                    )),
                ],
                body: any_expr!(Expr::Block(vec![
                    any_expr!(Expr::Func {
                        name: None,
                        generics: vec![],
                        params: vec![any_expr!(Expr::Parameter(
                            Name::Resolved(SymbolID::resolved(3), "x".into()),
                            None
                        ))],
                        body: any_expr!(Expr::Block(vec![
                            any_expr!(Expr::Variable(Name::Resolved(
                                SymbolID::resolved(3),
                                "x".into()
                            ))),
                            any_expr!(Expr::Variable(Name::Resolved(
                                SymbolID::resolved(2),
                                "y".into()
                            )))
                        ]))
                        .into(),
                        ret: None,
                        captures: vec![]
                    }),
                    any_expr!(Expr::Variable(Name::Resolved(
                        SymbolID::resolved(1),
                        "x".into()
                    ))),
                ]))
                .into(),
                ret: None,
                captures: vec![]
            })
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

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::Assignment(
                any_expr!(Expr::Let(
                    Name::Resolved(SymbolID::resolved(1), "a".into()),
                    None
                ))
                .into(),
                any_expr!(Expr::LiteralInt("1".into())).into()
            ))
        );

        assert_eq!(
            resolved.roots()[1],
            any_expr!(Expr::Assignment(
                any_expr!(Expr::Let(
                    Name::Resolved(SymbolID::resolved(2), "b".into()),
                    None
                ))
                .into(),
                any_expr!(Expr::LiteralInt("2".into())).into()
            ))
        );

        assert_eq!(
            resolved.roots()[2],
            any_expr!(Expr::Assignment(
                any_expr!(Expr::Let(
                    Name::Resolved(SymbolID::resolved(3), "c".into()),
                    None
                ))
                .into(),
                any_expr!(Expr::LiteralInt("3".into())).into()
            ))
        );

        assert_eq!(
            resolved.roots()[3],
            any_expr!(Expr::LiteralArray(vec![
                any_expr!(Expr::Variable(Name::Resolved(
                    SymbolID::resolved(1),
                    "a".into()
                )))
                .into(),
                any_expr!(Expr::Variable(Name::Resolved(
                    SymbolID::resolved(2),
                    "b".into()
                )))
                .into(),
                any_expr!(Expr::Variable(Name::Resolved(
                    SymbolID::resolved(3),
                    "c".into()
                )))
                .into(),
            ]))
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

        assert_eq!(
            tree.roots()[0],
            any_expr!(Expr::Assignment(
                any_expr!(Expr::Let(
                    Name::Resolved(SymbolID::resolved(1), "x".into()),
                    None
                ))
                .into(),
                any_expr!(Expr::LiteralInt("123".into())).into()
            ))
        );

        assert_eq!(
            tree.roots()[1],
            any_expr!(Expr::Assignment(
                any_expr!(Expr::Let(
                    Name::Resolved(SymbolID::resolved(2), "y".into()),
                    None
                ))
                .into(),
                any_expr!(Expr::LiteralInt("345".into())).into()
            ))
        );

        assert_eq!(
            tree.roots()[2],
            any_expr!(Expr::Variable(Name::Resolved(
                SymbolID::resolved(1),
                "x".into()
            )))
        );

        assert_eq!(
            tree.roots()[3],
            any_expr!(Expr::Variable(Name::Resolved(
                SymbolID::resolved(2),
                "y".into()
            )))
        );
    }

    #[test]
    fn resolves_let_rhs() {
        let tree = resolve(
            "
        let x = Optional.none
        ",
        );

        assert_eq!(
            tree.roots()[0],
            any_expr!(Expr::Assignment(
                any_expr!(Expr::Let(
                    Name::Resolved(SymbolID::resolved(1), "x".into()),
                    None
                ))
                .into(),
                any_expr!(Expr::Member(
                    Some(
                        any_expr!(Expr::Variable(Name::Resolved(
                            SymbolID::OPTIONAL,
                            "Optional".into()
                        )))
                        .into()
                    ),
                    "none".into()
                ))
                .into()
            ))
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        let (tree, session) = resolve_with_session("{ let x = 123 }; x");

        let session = session.lock().unwrap();
        let diagnostics = session.diagnostics_for(&tree.path);
        assert!(!diagnostics.is_empty());
        let Diagnostic {
            path: _,
            kind: DiagnosticKind::Resolve(_, NameResolverError::UnresolvedName(name)),
        } = diagnostics.iter().find(|_| true).unwrap()
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

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::EnumDecl {
                name: Name::Resolved(SymbolID::resolved(1), "Fizz".into()),
                body: any_expr!(Expr::Block(vec![
                    any_expr!(Expr::EnumVariant(
                        Name::Resolved(SymbolID::resolved(2), "foo".into()),
                        vec![]
                    )),
                    any_expr!(Expr::EnumVariant(
                        Name::Resolved(SymbolID::resolved(3), "bar".into()),
                        vec![]
                    )),
                ]))
                .into(),
                generics: vec![],
                conformances: vec![],
            })
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

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::EnumDecl {
                name: Name::Resolved(SymbolID::resolved(1), "Fizz".into()),
                body: any_expr!(Expr::Block(vec![any_expr!(Expr::EnumVariant(
                    Name::Resolved(SymbolID::resolved(2), "foo".into()),
                    vec![any_expr!(Expr::LiteralInt("123".into())).into()]
                ))]))
                .into(),
                generics: vec![],
                conformances: vec![],
            })
        );

        assert_eq!(
            resolved.roots()[1],
            any_expr!(Expr::Call {
                callee: any_expr!(Expr::Variable(Name::Resolved(
                    SymbolID::resolved(1),
                    "Fizz".into()
                )))
                .into(),
                args: vec![any_expr!(Expr::LiteralInt("123".into())).into()],
                type_args: vec![],
            })
        );
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

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::EnumDecl {
                name: Name::Resolved(SymbolID::resolved(1), "Fizz".into()),
                body: any_expr!(Expr::Block(vec![any_expr!(Expr::Func {
                    name: None,
                    generics: vec![],
                    params: vec![],
                    body: any_expr!(Expr::Block(vec![any_expr!(Expr::Variable(Name::_Self(
                        SymbolID::resolved(1)
                    )))]))
                    .into(),
                    ret: None,
                    captures: vec![]
                })]))
                .into(),
                generics: vec![],
                conformances: vec![],
            })
        );
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

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::Assignment(
                any_expr!(Expr::Let(
                    Name::Resolved(SymbolID::resolved(1), "count".into()),
                    None
                ))
                .into(),
                any_expr!(Expr::LiteralInt("0".into())).into()
            ))
        );

        assert_eq!(
            resolved.roots()[1],
            any_expr!(Expr::Func {
                name: None,
                generics: vec![],
                params: vec![],
                body: any_expr!(Expr::Block(vec![any_expr!(Expr::Variable(
                    Name::Resolved(SymbolID::resolved(1), "count".into())
                ))]))
                .into(),
                ret: None,
                captures: vec![SymbolID::resolved(1)]
            })
        );

        assert!(
            symbol_table
                .get(&SymbolID::resolved(1))
                .unwrap()
                .is_captured
        );
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

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::Func {
                name: None,
                generics: vec![],
                params: vec![],
                body: any_expr!(Expr::Block(vec![any_expr!(Expr::Call {
                    callee: any_expr!(Expr::Variable(Name::Resolved(
                        SymbolID::resolved(-5),
                        "__alloc".into()
                    ))),
                    args: vec![any_expr!(Expr::LiteralInt("123".into())).into()],
                    type_args: vec![],
                })]))
                .into(),
                ret: None,
                captures: vec![]
            })
        );
    }

    #[test]
    fn resolves_array_builtin() {
        let resolved = resolve("func c() -> Array<Int> {}");

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::Func {
                name: None,
                generics: vec![],
                params: vec![],
                body: any_expr!(Expr::Block(vec![])).into(),
                ret: Some(
                    any_expr!(Expr::TypeRepr {
                        name: Name::Resolved(SymbolID::ARRAY, "Array".into()),
                        generics: vec![],
                        introduces_type: false,
                        conformances: vec![],
                    })
                    .into()
                ),
                captures: vec![]
            })
        );
    }

    #[test]
    fn resolves_struct() {
        let resolved = resolve("struct Person {}\nPerson()");
        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::Struct {
                name: Name::Resolved(SymbolID::resolved(1), "Person".into()),
                body: any_expr!(Expr::Block(vec![])).into(),
                generics: vec![],
                conformances: vec![],
            })
        );
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

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::Struct {
                name: Name::Resolved(SymbolID::resolved(1), "Person".into()),
                body: any_expr!(Expr::Block(vec![
                    any_expr!(Expr::Property {
                        name: Name::Resolved(SymbolID::resolved(2), "age".into()),
                        type_repr: Some(
                            any_expr!(Expr::TypeRepr {
                                name: Name::Resolved(SymbolID::INT, "Int".into()),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false,
                            })
                            .into()
                        ),
                        default_value: None,
                    })
                    .into()
                ]))
                .into(),
                generics: vec![],
                conformances: vec![],
            })
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

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::Struct {
                name: Name::Resolved(SymbolID::resolved(1), "Person".into()),
                body: any_expr!(Expr::Block(vec![
                    any_expr!(Expr::Property {
                        name: Name::Resolved(SymbolID::resolved(2), "age".into()),
                        type_repr: Some(
                            any_expr!(Expr::TypeRepr {
                                name: Name::Resolved(SymbolID::INT, "Int".into()),
                                generics: vec![],
                                conformances: vec![],
                                introduces_type: false,
                            })
                            .into()
                        ),
                        default_value: None,
                    }),
                    any_expr!(Expr::Init(
                        Some(SymbolID::resolved(3)),
                        any_expr!(Expr::Func {
                            name: None,
                            generics: vec![],
                            params: vec![any_expr!(Expr::Parameter(
                                Name::Resolved(SymbolID::resolved(3), "age".into()),
                                Some(
                                    any_expr!(Expr::TypeRepr {
                                        name: Name::Resolved(SymbolID::INT, "Int".into()),
                                        generics: vec![],
                                        conformances: vec![],
                                        introduces_type: false,
                                    })
                                    .into()
                                ),
                            ))],
                            body: any_expr!(Expr::Block(vec![])).into(),
                            ret: None,
                            captures: vec![],
                        })
                        .into()
                    ))
                    .into(),
                ]))
                .into(),
                generics: vec![],
                conformances: vec![],
            })
        );
    }

    #[test]
    fn resolves_extend() {
        let resolved = resolve(
            "
        struct Person {}
        extend Person: Printable {}
        ",
        );

        assert_eq!(
            resolved.roots()[0],
            any_expr!(Expr::Struct {
                name: Name::Resolved(SymbolID::resolved(1), "Person".into()),
                body: any_expr!(Expr::Block(vec![])).into(),
                generics: vec![],
                conformances: vec![],
            })
        );

        assert_eq!(
            resolved.roots()[1],
            any_expr!(Expr::Extend {
                name: Name::Resolved(SymbolID::resolved(1), "Person".into()),
                body: any_expr!(Expr::Block(vec![])).into(),
                generics: vec![],
                conformances: vec![
                    any_expr!(Expr::TypeRepr {
                        name: Name::Resolved(SymbolID::resolved(2), "Printable".into()),
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false,
                    })
                    .into()
                ],
            })
        );
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
        let diagnostics = ses.diagnostics_for(&PathBuf::from("-"));
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
