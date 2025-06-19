use std::collections::HashMap;

use crate::Definition;
use crate::NameResolved;
use crate::SymbolID;
use crate::SymbolKind;
use crate::SymbolTable;
use crate::diagnostic::Diagnostic;
use crate::expr::Expr;
use crate::expr::Expr::*;
use crate::expr::Pattern;
use crate::name::Name;
use crate::parser::ExprID;
use crate::scope_tree::ScopeId;
use crate::source_file::SourceFile;
use crate::span::Span;

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum NameResolverError {
    InvalidSelf,
}

impl NameResolverError {
    pub fn message(&self) -> String {
        match self {
            Self::InvalidSelf => format!("`self` can't be used outside type"),
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
}

impl NameResolver {
    pub fn new(symbol_table: &mut SymbolTable) -> Self {
        let initial_scope = symbol_table.build_name_scope();

        NameResolver {
            scopes: vec![initial_scope],
            type_symbol_stack: vec![],
            func_stack: vec![],
            scope_tree_ids: vec![],
        }
    }

    pub fn resolve(
        mut self,
        mut source_file: SourceFile,
        symbol_table: &mut SymbolTable,
    ) -> SourceFile<NameResolved> {
        // Create the root scope for the file
        if !source_file.roots().is_empty() {
            let first_root = &source_file.meta[*source_file.root_ids().first().unwrap() as usize];
            let last_root = &source_file.meta[*source_file.root_ids().last().unwrap() as usize];
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
        self.hoist_enums(node_ids, source_file, symbol_table);
        self.hoist_funcs(node_ids, source_file, symbol_table);
        self.hoise_structs(node_ids, source_file, symbol_table);

        for node_id in node_ids {
            let expr = &mut source_file.get_mut(node_id).unwrap();
            log::trace!("Resolving: {expr:?}");
            match expr.clone() {
                LiteralInt(_) => continue,
                LiteralFloat(_) => continue,
                LiteralArray(items) => {
                    self.resolve_nodes(&items, source_file, symbol_table);
                }
                LiteralTrue | LiteralFalse => continue,
                Struct(name, generics, body) => {
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
                                Struct(Name::Resolved(symbol_id, name_str), generics.clone(), body),
                            );
                        }
                        _ => continue,
                    }

                    self.resolve_nodes(&generics, source_file, symbol_table);
                    self.resolve_nodes(&[body], source_file, symbol_table);
                    self.type_symbol_stack.pop();
                }
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
                        Name::Resolved(_, _) | Name::_Self(_) => name,
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
                    if !self.type_symbol_stack.is_empty() && name.is_none() {
                        panic!("missing method name");
                    }

                    self.func_stack.push((*node_id, self.scopes.len()));
                    self.start_scope(source_file, source_file.span(node_id));

                    self.resolve_nodes(&generics, source_file, symbol_table);

                    for param in &params {
                        let Some(Parameter(Name::Raw(name), ty_id)) =
                            source_file.get(param).cloned()
                        else {
                            panic!("got a non variable param")
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
                    to_resolve.push(body);

                    if let Some(ret) = ret {
                        to_resolve.push(ret);
                    }

                    self.resolve_nodes(&to_resolve, source_file, symbol_table);
                    self.end_scope();
                    self.func_stack.pop();
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
                            let (symbol_id, _) = self.lookup(&name_str);
                            symbol_table.add_map(source_file, node_id, &symbol_id);
                            source_file.nodes.insert(
                                *node_id,
                                Parameter(Name::Resolved(symbol_id, name_str), ty_repr),
                            );
                        }
                        Name::Resolved(_, _) | Name::_Self(_) => (),
                    }
                }
                Variable(name, _) => match name {
                    Name::Raw(name_str) => {
                        let name = if name_str == "self" {
                            if let Some(last_symbol) = self.type_symbol_stack.last() {
                                Name::_Self(*last_symbol)
                            } else {
                                source_file.diagnostics.insert(Diagnostic::resolve(
                                    *node_id,
                                    NameResolverError::InvalidSelf,
                                ));
                                Name::_Self(SymbolID(0))
                            }
                        } else {
                            let (symbol_id, depth) = self.lookup(&name_str);
                            log::trace!("Replacing variable {name_str} with {symbol_id:?}");

                            symbol_table.add_map(source_file, node_id, &symbol_id);

                            // Check to see if this is a capture
                            if let Some((func_id, func_depth)) = self.func_stack.last()
                                && &depth < func_depth
                            {
                                let Func { captures, .. } = source_file.get_mut(func_id).unwrap()
                                else {
                                    unreachable!()
                                };

                                if !captures.contains(&symbol_id) {
                                    captures.push(symbol_id);
                                }

                                symbol_table.mark_as_captured(&symbol_id);
                            }

                            Name::Resolved(symbol_id, name_str)
                        };

                        source_file.nodes.insert(*node_id, Variable(name, None));
                    }
                    Name::Resolved(_, _) | Name::_Self(_) => (),
                },
                TypeRepr(name, generics, is_type_parameter_decl) => {
                    log::trace!(
                        "Resolving TypeRepr: {name:?}, generics: {generics:?}, is_param_decl: {is_type_parameter_decl}"
                    );

                    let resolved_name_for_node = match name.clone() {
                        Name::Raw(raw_name_str) => {
                            if is_type_parameter_decl {
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
                                let (symbol_id, _) = self.lookup(&raw_name_str);
                                Name::Resolved(symbol_id, raw_name_str)
                            }
                        }
                        Name::Resolved(_, _) | Name::_Self(_) => name, // Already resolved, no change needed to the name itself.
                    };

                    // Update the existing TypeRepr node with the resolved name.
                    // The node type remains TypeRepr.
                    source_file.nodes.insert(
                        *node_id,
                        TypeRepr(
                            resolved_name_for_node,
                            generics.clone(), // Keep original generics ExprIDs
                            is_type_parameter_decl,
                        ),
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
                EnumDecl(name, generics, body) => {
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
                            source_file.nodes.insert(
                                *node_id,
                                EnumDecl(
                                    Name::Resolved(symbol_id, name_str),
                                    generics.clone(),
                                    body,
                                ),
                            );
                        }
                        _ => continue,
                    }

                    self.resolve_nodes(&generics, source_file, symbol_table);
                    self.resolve_nodes(&[body], source_file, symbol_table);
                    self.type_symbol_stack.pop();
                }
                EnumVariant(_, values) => {
                    self.resolve_nodes(&values, source_file, symbol_table);
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
                PatternVariant(_, _, _items) => todo!(),
            }
        }
    }

    fn hoist_funcs(
        &mut self,
        node_ids: &[ExprID],
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) {
        for id in node_ids {
            if let Func {
                name: Some(Name::Raw(name)),
                generics,
                params,
                body,
                ret,
                captures,
            } = source_file.get(id).unwrap().clone()
            {
                let symbol_id = self.declare(
                    name.clone(),
                    SymbolKind::Func,
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
        }
    }

    fn hoise_structs(
        &mut self,
        node_ids: &[ExprID],
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) {
        for id in node_ids {
            let Some(Struct(Name::Raw(name_str), generics, body_expr)) =
                source_file.get(id).cloned()
            else {
                continue;
            };

            let struct_symbol = self.declare(
                name_str.clone(),
                SymbolKind::Struct,
                id,
                source_file,
                symbol_table,
            );

            symbol_table.initialize_type_table(struct_symbol);

            self.resolve_nodes(&generics, source_file, symbol_table);

            source_file.nodes.insert(
                *id,
                Struct(Name::Resolved(struct_symbol, name_str), generics, body_expr),
            );

            // Hoist properties
            let Some(Block(ids)) = source_file.get(&body_expr) else {
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
            self.hoist_enum_members(&body_expr, source_file, symbol_table);
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
            let Some(EnumDecl(Name::Raw(name_str), generics, body_expr)) =
                source_file.get(id).cloned()
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

            source_file.nodes.insert(
                *id,
                EnumDecl(Name::Resolved(enum_symbol, name_str), generics, body_expr),
            );

            // Hoist variants
            self.type_symbol_stack.push(enum_symbol);
            self.hoist_enum_members(&body_expr, source_file, symbol_table);
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
                let enum_name = if let Some(Name::Raw(enum_name)) = enum_name {
                    let symbol = self.declare(
                        enum_name.clone(),
                        SymbolKind::PatternBind,
                        node_id,
                        source_file,
                        symbol_table,
                    );
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

    // New helper method to hoist enum variants
    fn hoist_enum_members(
        &mut self,
        body_expr_id: &ExprID,
        source_file: &mut SourceFile,
        symbol_table: &mut SymbolTable,
    ) {
        let Block(items) = source_file.get(body_expr_id).unwrap().clone() else {
            unreachable!("Expected Block for enum body");
        };

        for variant_id in &items {
            let variant_expr = source_file.get(variant_id).unwrap().clone();

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
        log::trace!(
            "declaring {} in {:?} at depth {}",
            name,
            self.scopes,
            self.scopes.len() - 1
        );

        let meta = &source_file.meta[*expr_id as usize];
        let definition = Definition {
            path: source_file.path.clone(),
            line: meta.start.line,
            col: meta.start.col,
            sym: None,
        };

        let symbol_id = symbol_table.add(&name, kind, *expr_id, Some(definition));

        if let Some(scope_id) = self.scope_tree_ids.last() {
            source_file
                .scope_tree
                .add_symbol_to_scope(*scope_id, symbol_id);
        }

        self.scopes.last_mut().unwrap().insert(name, symbol_id);
        symbol_table.add_map(source_file, expr_id, &symbol_id);
        symbol_id
    }

    fn lookup(&self, name: &str) -> (SymbolID, usize /* depth */) {
        // self.scopes.last().unwrap().get(name)
        for (i, scope) in self.scopes.iter().rev().enumerate() {
            if let Some(symbol_id) = scope.get(name) {
                // The depth of the scope where the variable was found
                let found_depth = self.scopes.len() - 1 - i;
                return (*symbol_id, found_depth);
            }
        }

        (SymbolID(0), 0)
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
    use std::path::PathBuf;

    use super::*;
    use crate::{compiling::driver::Driver, expr::Expr};

    fn resolve(code: &'static str) -> SourceFile<NameResolved> {
        let mut driver = Driver::with_str(code);
        driver.resolved_source_file(&PathBuf::from("-")).unwrap()
    }

    pub fn resolve_with_symbols(code: &'static str) -> (SourceFile<NameResolved>, SymbolTable) {
        let mut driver = Driver::with_str(code);
        let file = driver.units[0]
            .clone()
            .parse()
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
        let tree = resolve("hello");
        let root = tree.roots()[0].unwrap();
        assert_eq!(
            root,
            &Variable(Name::Resolved(SymbolID(0), "hello".into()), None)
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
            [a, b, c]
            ",
        );

        assert_eq!(
            *resolved.get(&0.into()).unwrap(),
            Expr::Variable(Name::Resolved(SymbolID(0), "a".into()), None)
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

        assert_eq!(
            *tree.get(rhs).unwrap(),
            Expr::Member(Some(1.into()), "none".into())
        );

        assert_eq!(
            *tree.get(&1.into()).unwrap(),
            Variable(Name::Resolved(SymbolID::OPTIONAL, "Optional".into()), None)
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        // parse a block with a single let,
        // followed by a bare `x` at top level:
        let tree = resolve("{ let x = 123 } x");

        // The first root is the Block, the second is the Variable("x")
        let roots = tree.root_ids();
        // That `x` should resolve to the global‐fallback ID 0,
        // not to the block's own `x` (which would have been >0).
        let second = tree.get(&roots[1]).unwrap();
        assert_eq!(
            second,
            &Variable(Name::Resolved(SymbolID(0), "x".into()), None)
        );
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
            *resolved.roots()[0].unwrap(),
            Expr::EnumDecl(
                Name::Resolved(SymbolID::resolved(1), "Fizz".into()),
                vec![],
                2.into()
            )
        );
        assert_eq!(
            *resolved.get(&2.into()).unwrap(),
            Expr::Block(vec![0.into(), 1.into()])
        );
        assert_eq!(
            *resolved.get(&0.into()).unwrap(),
            EnumVariant(Name::Raw("foo".into()), vec![])
        );
        assert_eq!(
            *resolved.get(&1.into()).unwrap(),
            EnumVariant(Name::Raw("bar".into()), vec![])
        );

        assert_eq!(
            *resolved.roots()[1].unwrap(),
            Expr::Member(Some(4.into()), "foo".into())
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
            *resolved.roots()[0].unwrap(),
            Expr::EnumDecl(
                Name::Resolved(SymbolID::resolved(1), "Fizz".into()),
                vec![],
                3.into()
            )
        );
        assert_eq!(
            *resolved.get(&3.into()).unwrap(),
            Expr::Block(vec![1.into(), 2.into()])
        );
        assert_eq!(
            *resolved.get(&1.into()).unwrap(),
            EnumVariant(Name::Raw("foo".into()), vec![0.into()])
        );
        assert_eq!(
            *resolved.get(&2.into()).unwrap(),
            EnumVariant(Name::Raw("bar".into()), vec![])
        );

        assert_eq!(
            *resolved.roots()[1].unwrap(),
            Call {
                callee: 6.into(),
                type_args: vec![],
                args: vec![8.into()]
            }
        );
        assert_eq!(
            *resolved.get(&6.into()).unwrap(),
            Expr::Member(Some(5.into()), "foo".into())
        );
        assert_eq!(
            *resolved.get(&5.into()).unwrap(),
            Expr::Variable(Name::Resolved(SymbolID::resolved(1), "Fizz".into()), None)
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
            *resolved.get(&0.into()).unwrap(),
            Expr::Variable(Name::_Self(SymbolID::resolved(1)), None)
        );
    }

    #[test]
    #[should_panic]
    fn ensures_methods_have_names() {
        resolve(
            "
        enum Fizz {
            func() {
                self
            }
        }
        ",
        );
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
            *resolved.roots()[0].unwrap(),
            Assignment(0.into(), 1.into()),
        );
        assert_eq!(
            *resolved.get(&0.into()).unwrap(),
            Let(Name::Resolved(SymbolID::resolved(2), "count".into()), None)
        );

        assert!(
            symbol_table
                .get(&SymbolID::resolved(2))
                .unwrap()
                .is_captured
        );

        assert_eq!(
            *resolved.roots()[1].unwrap(),
            Func {
                name: Some(Name::Resolved(SymbolID::resolved(1), "counter".into())),
                generics: vec![],
                params: vec![],
                body: 5.into(),
                ret: None,
                captures: vec![SymbolID::resolved(2)],
            }
        );
    }

    #[test]
    fn resolves_array_builtin() {
        let resolved = resolve("func c() -> Array<Int> {}");

        let Expr::Func { ret, .. } = resolved.roots()[0].unwrap() else {
            panic!("didn't get a func");
        };

        assert_eq!(
            *resolved.get(&ret.unwrap().into()).unwrap(),
            TypeRepr(
                Name::Resolved(SymbolID::ARRAY, "Array".into()),
                vec![0.into()],
                false
            )
        );
        assert_eq!(
            *resolved.get(&0.into()).unwrap(),
            TypeRepr(Name::Resolved(SymbolID(-1), "Int".into()), vec![], false)
        );
    }

    #[test]
    fn resolves_struct() {
        let resolved = resolve("struct Person {}\nPerson()");
        assert_eq!(
            *resolved.roots()[0].unwrap(),
            Struct(
                Name::Resolved(SymbolID::resolved(1), "Person".into()),
                vec![],
                0.into()
            )
        );
        assert_eq!(
            *resolved.roots()[1].unwrap(),
            Expr::Call {
                callee: 2.into(),
                type_args: vec![],
                args: vec![],
            }
        );
        assert_eq!(
            *resolved.get(&2.into()).unwrap(),
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
        assert_eq!(
            *resolved.roots()[0].unwrap(),
            Struct(
                Name::Resolved(SymbolID::resolved(1), "Person".into()),
                vec![],
                2.into()
            )
        );
        assert_eq!(
            *resolved.get(&1.into()).unwrap(),
            Expr::Property {
                name: Name::Resolved(SymbolID::resolved(2), "age".into()),
                type_repr: Some(0.into()),
                default_value: None
            }
        );
        assert_eq!(
            *resolved.get(&0.into()).unwrap(),
            Expr::TypeRepr(Name::Resolved(SymbolID(-1), "Int".into()), vec![], false)
        );
    }

    #[test]
    fn resolves_initializers() {
        let (resolved, symbol_table) = resolve_with_symbols(
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
            *resolved.roots()[0].unwrap(),
            Struct(
                Name::Resolved(SymbolID::resolved(1), "Person".into()),
                vec![],
                11.into()
            )
        );
        assert_eq!(
            *resolved.get(&1.into()).unwrap(),
            Expr::Property {
                name: Name::Resolved(SymbolID::resolved(2), "age".into()),
                type_repr: Some(0.into()),
                default_value: None
            }
        );
        assert_eq!(
            *resolved.get(&0.into()).unwrap(),
            Expr::TypeRepr(Name::Resolved(SymbolID(-1), "Int".into()), vec![], false)
        );

        assert_eq!(
            symbol_table.initializers_for(&SymbolID::resolved(1)),
            Some(&vec![10])
        )
    }
}

// TODO:

// named recursive binds
// parameter ordering
// captured vs. shadowed vs. free
// arbitrary nesting depth
//   non‐statement AST nodes (tuples, blocks)
